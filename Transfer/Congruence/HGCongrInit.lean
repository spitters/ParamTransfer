/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Related
import Mathlib.Tactic.GCongr

/-!
# `hgcongr` engine — head-pair-keyed DB, attribute, and tactic

This module holds the engine for `hgcongr` (heterogeneous cross-head
generalized congruence): the head-pair-keyed environment extension, the
`@[hgcongr]` attribute (`makeHGCongrLemma`), and the `hgcongr` tactic core. The
registered correspondences and demos live in the importer `HGCongr.lean`.

The split is mandatory: an `initialize` env-extension declaration cannot be
*evaluated* in the same module that defines it, and applying `@[hgcongr]` to a
lemma forces that evaluation at elaboration time. So the extension + attribute
must sit in a module imported before any `@[hgcongr]` use (the same reason
Mathlib keeps `gcongrExt` in `GCongr/Core.lean`, used only by importers, and the
reason `ParamDB.lean` is split from its consumers here). See `HGCongr.lean` for
the design rationale, the `rcongr`/gcongr contrast, and the upstream-patch spec.
-/

set_option autoImplicit false

namespace Transfer

open Lean Meta Elab Tactic
open Mathlib.Tactic.GCongr (getCongrAppFnArgs getRel)

/-! ## The head-pair-keyed lemma database -/

/-- Lookup key for a heterogeneous congruence lemma: the relation together with
    both heads. Unlike gcongr's `GCongrKey` (one `head`), this stores the
    LHS head `f` and RHS head `g` of a conclusion `R (f a..) (g b..)`. The
    diagonal `lhsHead = rhsHead` recovers the homogeneous gcongr key. -/
structure HGCongrKey where
  /-- The relation name, e.g. ``Eq``. -/
  relName : Name
  /-- The LHS head function, e.g. ``HMul.hMul``. -/
  lhsHead : Name
  /-- The RHS head function, e.g. ``bbFieldMul`` (may differ from `lhsHead`). -/
  rhsHead : Name
  deriving Inhabited, BEq, Hashable

/-- Data for one registered heterogeneous congruence lemma. -/
structure HGCongrLemma where
  /-- The head-pair key under which the lemma is stored. -/
  key : HGCongrKey
  /-- The lemma's declaration name. -/
  declName : Name
  /-- For each per-argument *main* subgoal: the hypothesis index, the number of
      leading binders to `intro`, and whether it is contravariant. -/
  mainSubgoals : Array (Nat × Nat × Bool)
  /-- The number of arguments to supply when applying the lemma. -/
  numHyps : Nat
  /-- The number of varying-argument pairs (for priority/diagnostics). -/
  numVarying : Nat
  deriving Inhabited

/-- The head-pair-keyed lemma collection stored in the environment extension. -/
abbrev HGCongrLemmas := Std.HashMap HGCongrKey (List HGCongrLemma)

/-- Environment extension for `@[hgcongr]` lemmas, keyed on the head **pair**.
    Contrast `Mathlib.Tactic.GCongr.gcongrExt`, keyed on a single head. -/
initialize hgcongrExt : SimpleScopedEnvExtension HGCongrLemma HGCongrLemmas ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m l => m.alter l.key fun
      | none    => some [l]
      | some es => some (l :: es)
    initial := {}
  }

/-! ## Registration: `makeHGCongrLemma`

The heterogeneous analogue of `makeGCongrLemma`. The two structural differences
from gcongr are (a) no `lhsHead == rhsHead` / arity-equality guard, and
(b) varying-argument pairs are recovered from the hypotheses rather than by a
positional zip of the two argument lists (which is ill-defined when the heads
have different arities, as `HMul.hMul`/`bbFieldMul` do). -/

/-- Build the `HGCongrLemma` for a lemma with hypotheses `hyps` and conclusion
    `target` of the form `R (f a₁ … aₘ) (g b₁ … bₙ)`, `f` and `g` possibly
    different (and `m ≠ n` permitted). Each hypothesis `Rᵢ lᵢ rᵢ` whose sides are
    free variables appearing among the LHS-args and RHS-args (in either order)
    becomes a varying pair and a recursive *main* subgoal. -/
def makeHGCongrLemma (hyps : Array Expr) (target : Expr) (declName : Name) :
    MetaM HGCongrLemma := do
  let fail {α} (m : MessageData) : MetaM α := throwError "\
    @[hgcongr] only applies to lemmas proving `R (f x₁..xₘ) (g x₁'..xₙ')`.\n\
    {m} in {target}"
  let some (relName, lhs, rhs) := getRel (← whnfR target) | fail "No relation found"
  let lhs := lhs.headBeta; let rhs := rhs.headBeta
  let some (lhsHead, lhsArgs) := getCongrAppFnArgs lhs | fail "LHS is not suitable for congruence"
  let some (rhsHead, rhsArgs) := getCongrAppFnArgs rhs | fail "RHS is not suitable for congruence"
  -- The free variables occurring directly as arguments to each head.
  let lhsFVars := lhsArgs.filterMap (·.eta.fvarId?)
  let rhsFVars := rhsArgs.filterMap (·.eta.fvarId?)
  let mut mainSubgoals := #[]
  let mut i := 0
  for hyp in hyps do
    let new ← forallTelescopeReducing (← inferType hyp) fun args hypTy => do
      let hypTy ← whnfR hypTy
      if let some (_, l₁, r₁) := getRel hypTy then
        if let .fvar l₁ := l₁.getAppFn then
        if let .fvar r₁ := r₁.getAppFn then
          if lhsFVars.contains l₁ && rhsFVars.contains r₁ then
            return some (i, args.size, false)
          if lhsFVars.contains r₁ && rhsFVars.contains l₁ then
            return some (i, args.size, true)
      return none
    if let some sg := new then
      mainSubgoals := mainSubgoals.push sg
    i := i + 1
  if mainSubgoals.isEmpty then fail "no varying-argument hypotheses found"
  let key := { relName, lhsHead, rhsHead }
  return { key, declName, mainSubgoals, numHyps := hyps.size, numVarying := mainSubgoals.size }

/-- Attribute `@[hgcongr]`: register a heterogeneous (cross-head) generalized
    congruence lemma. Unlike `@[gcongr]`, the conclusion `R (f x..) (g y..)` may
    have `f ≠ g` and different arities; both heads are stored as the lookup key.
    The diagonal `f = g` is exactly a `@[gcongr]`-shaped lemma, so `@[hgcongr]`
    subsumes the homogeneous case. -/
initialize registerBuiltinAttribute {
  name := `hgcongr
  descr := "heterogeneous (cross-head) generalized congruence"
  add := fun declName _stx kind ↦ MetaM.run' do withReducible do
    let cinfo ← getConstInfo declName
    forallTelescope cinfo.type fun xs type => do
      hgcongrExt.add (← makeHGCongrLemma xs type declName) kind
}

/-! ## The `hgcongr` tactic -/

/-- The core descent. Mirror of `Lean.MVarId.gcongr` but with the head-**pair**
    lookup. On a goal `R (f a..) (g b..)`:

* try `rfl` first (closes leaves and the homogeneous reflexive case);
* read `(relName, lhsHead, rhsHead)`, look up the `(f, g)` correspondence in the
  head-pair DB, `apply` the lemma at the LHS-head arity, recurse on the
  per-argument main subgoals, and `rfl`-discharge any leftover side goals;
* otherwise return the goal unsolved. -/
partial def hgcongrCore (g : MVarId) : MetaM (List MVarId) := g.withContext do
  if ← (try withReducible g.applyRfl; pure true catch _ => pure false) then
    return []
  let rel ← withReducible g.getType'
  let some (relName, lhs, rhs) := getRel rel | return [g]
  let some (lhsHead, _) := getCongrAppFnArgs lhs | return [g]
  let some (rhsHead, _) := getCongrAppFnArgs rhs | return [g]
  let key : HGCongrKey := { relName, lhsHead, rhsHead }
  let lemmas := (hgcongrExt.getState (← getEnv)).getD key []
  let mctx ← getMCtx
  for lem in lemmas do
    let gs ← try
      let const ← mkConstWithFreshMVarLevels lem.declName
      withReducible (g.applyWithArity const lem.numHyps { synthAssignedInstances := false })
    catch _ => setMCtx mctx; continue
    let some e ← getExprMVarAssignment? g | do setMCtx mctx; continue
    let args := e.getAppArgs
    let mut out := #[]
    for (idx, nh, _isContra) in lem.mainSubgoals do
      if let some (.mvar mv) := args[idx]? then
        let (_, mv) ← mv.introN nh
        out := out ++ (← hgcongrCore mv)
    -- `rfl`-discharge any side goals not handled as main subgoals.
    let mainMVs := lem.mainSubgoals.filterMap fun (idx, _, _) =>
      match args[idx]? with
      | some (.mvar m) => some m
      | _ => none
    for sg in gs do
      unless (← sg.isAssigned) || mainMVs.contains sg || out.contains sg do
        try withReducible sg.applyRfl catch _ => out := out.push sg
    return out.toList
  return [g]

/-- `hgcongr` — heterogeneous (cross-head) generalized congruence.

Reduce a relational goal `R (f a₁ … aₘ) (g b₁ … bₙ)` whose two sides have a
*registered* head correspondence `(f, g)` (a `@[hgcongr]` lemma) to its
per-argument subgoals, recursing. The heads `f`, `g` may differ (the case
`@[gcongr]` rejects); the diagonal `f = g` recovers gcongr's homogeneous
descent. Leaves and reflexive steps are closed by `rfl`. -/
elab "hgcongr" : tactic => do
  let rem ← hgcongrCore (← getMainGoal)
  replaceMainGoal rem

end Transfer
