/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: ParamTransfer Contributors
-/
import Transfer.Integrations.ParamForIn
import Transfer.Statements.ParamTransferTac

/-!
# `rcomp`: structural assembly of an `RComp` witness

`Integrations/ParamTripleTransfer.lean` builds an `RComp` witness — the Kleisli
logical relation observed through `wp` — by hand, one `RComp.pure` / `RComp.bind`
leaf per `pure` / `bind` in the `do`-block. This module automates that assembly:
`rcomp` is the monad-level analogue of the pure `transfer` / `rcongr` descent, a
goal-shape-directed tactic that walks the two programs' structure and applies the
matching `RComp` rule, leaving each *value*-relatedness as a residual goal.

## What `rcomp` does

On a goal `RComp Rα c c'` it tries, in order:

* `RComp.refl` — the diagonal (`c` and `c'` definitionally equal, `Rα` reflexive);
* `RComp.pure` — a `pure`/`pure` (or pure-reducible) pair, leaving one leaf
  `Rα a a'`;
* `RComp.bind` — a `bind`/`bind` pair, pinning the intermediate relation to the
  goal's `Rα` and recursing on the head and (under the introduced value binders)
  the continuation;
* `RComp.forIn_list` — a `for`/`do` loop.

The value leaves (`Rα a a'`, the arithmetic content) are left for the caller — the
same non-fabrication discipline `transfer` follows. A pure computation over `Id`
collapses to a single leaf (`pure` reduces definitionally), discharged with
`norm_cast` / `simp_all`; a genuinely effectful monad descends its `bind`
structure leaf by leaf.

## Folded into `param_transfer`

`param_transfer` gains an `RComp` alternative: on a `∀`-transfer goal it runs the
abstraction-theorem `∀`-rule (`ParamTransferTac`), and on an `RComp` goal it
assembles the witness with `rcomp`. One entry point, both the pure and the
effectful abstraction theorem.

Only the *structurally parallel* fragment is automatic — the two programs must
share a `pure` / `bind` / `forIn` skeleton and a uniform value relation, which is
the shape every hand-assembled witness has. A structural mismatch stays a residual
`RComp` goal rather than being forced.
-/

set_option autoImplicit false

open Std.Do

namespace Transfer.Param

open Lean Elab Tactic Meta

/-- Goal-shape-directed `RComp` descent. On `RComp Rα c c'` it applies the first
    matching rule — `RComp.refl` (diagonal), `RComp.pure` (a `pure` leaf, or a
    pure-reducible `Id` computation collapsed to one leaf), `RComp.bind` (a `bind`
    node, intermediate relation pinned to `Rα`), or `RComp.forIn_list` (a loop) —
    and recurses into the resulting `RComp` / continuation subgoals, introducing
    the continuation's value binders with fresh names. Value-relatedness leaves are
    left as residual goals. -/
partial def rcompCore : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if let (``Transfer.Param.RComp, args) := tgt.getAppFnArgs then
    let rαStx ← Lean.Elab.Term.exprToSyntax args[5]!
    evalTactic (← `(tactic|
      first
        | exact RComp.refl _
        | refine RComp.pure _ ?_
        | refine RComp.bind (Rα := $rαStx) ?_ ?_
        | apply RComp.forIn_list))
    allGoals (withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      if g.isAppOf ``Transfer.Param.RComp || g.isForall then rcompCore else pure ())
  else if tgt.isForall then
    let a  := mkIdent (← mkFreshUserName `a)
    let a' := mkIdent (← mkFreshUserName `a)
    let hr := mkIdent (← mkFreshUserName `hr)
    evalTactic (← `(tactic| intro $a $a' $hr))
    rcompCore
  else
    pure ()

/-- Assemble an `RComp` witness by structural descent (see `rcompCore`). Fails
    on a goal that is not `RComp _ _ _`, so it composes safely as a `param_transfer`
    alternative. The value-relatedness leaves remain — discharge them with the
    relation's arithmetic (`norm_cast` / `simp_all` / `push_cast; ring`). -/
elab "rcomp" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isAppOf ``Transfer.Param.RComp then rcompCore
  else throwError "rcomp: goal is not `RComp _ _ _`"

/-- Fold: `param_transfer` assembles an `RComp` witness when the goal is one. The
    `∀`-rule alternative (`ParamTransferTac`) is tried for a `∀`-transfer goal;
    this alternative handles the effectful/`RComp` goal. -/
macro_rules
  | `(tactic| param_transfer) => `(tactic| rcomp)

/-! ## Demonstrations

Each witness below is assembled by the tactic; the caller writes only the value
leaf. Compare `Examples/HexEffectful.lean` / `Examples/EffectfulTransfer.lean`,
where the same witnesses are spelled out by hand. -/

/-- A straight-line `Id` program transferred across a value-*type* change
    (`ℕ ↦ ℤ`). `rcomp` collapses the pure computation to one leaf; `norm_cast`
    closes it. -/
example (natProg : Nat → Nat → Id Nat) (intProg : Int → Int → Id Int)
    (hn : ∀ n m, natProg n m = pure (n + 1 + (m + 1)))
    (hi : ∀ n m, intProg n m = pure (n + 1 + (m + 1))) (n m : Nat) :
    RComp (M := Id) (fun (a : Nat) (a' : Int) => (a : Int) = a')
      (natProg n m) (intProg (n : Int) (m : Int)) := by
  rw [hn, hi]; rcomp; norm_cast

/-- The diagonal: any computation is `RComp`-related to itself. `rcomp` closes it
    with `RComp.refl`. -/
example (c : Id Nat) : RComp (M := Id) (fun a a' => a = a') c c := by rcomp

/-- The same, through the folded `param_transfer` entry point. -/
example (c : Id Nat) : RComp (M := Id) (fun a a' => a = a') c c := by param_transfer

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.RComp.forIn_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RComp.forIn_list

end AxiomAudit

end Transfer.Param
