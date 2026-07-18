/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Combinators.ParamData
import Transfer.Deriving.ParamDerive
import Transfer.Combinators.ParamCoherence
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util
import Lean.Meta.Inductive

/-!
# The description-based `@[derive Param]` handler

`ParamDerive.lean` *specified* the deriving-handler algorithm (its 6-step design
note) and hand-ported the representative inductive shapes (`R_sum`/`paramSum`,
`R_nat`/`paramNat`); `ParamData.lean` hand-ported `R_prod`/`R_option`/`R_list`.
This file turns the front half of that spec into a running elaborator: an
`IndDesc` extraction in AdapTT's style, a mixed-variance guard, and a generator
that emits the relational lift `R_<T>` of a simple inductive *uniformly from its
constructor signatures* — the constructor-wise `Forall₂`-shape congruence the
hand-ports reproduce by hand.

## Implemented vs. specified

Running elaborator (this file, exercised by the demos below):

1. `IndDesc` / `CtorDesc` / `FieldKind` — AdapTT's `IndDesc` scheme: a constructor
   is a list of fields, each field classified as
   * `param i` — a non-recursive covariant occurrence of the `i`-th type
     parameter (e.g. the `a` in `Tree.leaf a`),
   * `recursive` — the inductive itself applied to the params (e.g. the subtrees
     in `Tree.node`),
   * `other` — a parameter-free field type, lifted by equality.
2. `Param.occPol` — a polarity (variance) analysis of a parameter's occurrences
   in a field type, flipping polarity under each arrow domain.
3. `Param.toIndDesc : Name → MetaM IndDesc` — reads an `InductiveVal` via
   `getConstInfoInduct`, walks each constructor's field telescope
   (`forallTelescopeReducing`), and classifies every field. Here the
   mixed-variance guard applies: a parameter that occurs in both co- and
   contravariant position (the canonical non-example, e.g. a field of type
   `A → A`) is rejected with AdapTT's `NonExample (Mixed variance)`; a purely
   contravariant occurrence is likewise rejected (a `Param` lift of `A` is a
   relation `A → A' → Prop`, which only supplies a *covariant* element relation).
4. `Param.mkRelInductive : IndDesc → Name → CommandElabM (TSyntax \`command)` —
   the generator: emits
   `inductive R_<T> {A₀ A₀' …} (P₀ : A₀ → A₀' → Prop) … : T A₀ … → T A₀' … → Prop`
   with one constructor per source constructor, each taking the per-field
   relatedness hypotheses (`Pᵢ aⱼ aⱼ'` for a param field; the recursive `R_<T> …`
   for a recursive field; `aⱼ = aⱼ'` for an `other` field) and concluding
   `R_<T> P… (c a…) (c a'…)`. This is exactly the shape of `R_sum`/`R_list` etc.
5. `Param.mkParamMap1Cmds : IndDesc → Name → …` — for a non-recursive
   inductive (records / enums — the crypto carriers), the relation is upgraded to
   a full annotated `Param`: it emits the forward map `T.paramMap` (constructor-wise,
   applying each parameter's forward map to the matching field) and the instance
   `T.param_instance : Param .map3 .map0 (T A…) (T A'…)` whose `R` is the generated
   `R_<T>`. The `map_in_R` and `R_in_map` proof fields are synthesized
   constructor-wise (`cases` + `exact R_<T>.<c> …` / `simp [T.paramMap, …]`) — a
   finite per-constructor term, no induction needed because no field is the
   inductive itself. Element inputs are taken at `Param .map3 .map3` (the level
   supplying `map`/`map_in_R`/`R_in_map`, e.g. `paramId`'s level). This is exactly
   the shape `paramProd`/`paramOption` reproduce by hand, at the forward-`map3`
   level so the result feeds `castViaParam`.
6. `Param.isUniformRecursive` / `Param.mkParamMapRecCmds` — for a
   uniform-recursive inductive (List/Tree-shape: every recursive field is
   `T` applied to the *same* parameters), the same full `Param .map3 .map0`
   instance is generated, but the three forward fields are recursive:
   `T.paramMap` by structural recursion (recurse on recursive fields),
   `map_in_R` by `induction` on the value, `R_in_map` by `induction` on the
   `R_<T>` derivation — recursive arms use the induction hypothesis, param arms
   the element `Pⱼ.fwd.*`. `isUniformRecursive` gates the path: non-uniform
   recursion (nesting / arrows / differing args / indices) stays relation-only.
7. `Param.mkParamDeriveCmds` / `mkParamInstanceHandler` — registered as the
   `@[derive Param]` deriving handler (`registerDerivingHandler`): on
   `deriving instance Param for T` (or a `deriving Param` clause) it elaborates
   the generated `R_<T>` relation and the `T.paramMap` / `T.param_instance`
   (non-recursive or uniform-recursive) into the environment.

What the map-instance synthesis covers, and the boundary:

* Non-recursive inductives (records / enums): a full `Param .map3 .map0`
  instance — forward map plus both graph inclusions — is synthesized
  generically (`mkParamMap1Cmds`, finite per-constructor terms). `deriving Param`
  on a crypto record yields a *usable* `Param`, not just `R_<T>`.
* Uniform-recursive inductives (List/Tree-shape — every recursive field is the
  inductive applied to the *same* parameters): also a full `Param .map3 .map0`
  instance (`mkParamMapRecCmds`). The forward map `T.paramMap` is generated by
  structural recursion (recurse on recursive fields; the equation compiler
  discharges termination); `map_in_R` by `induction` on the value (recursive
  arms use the IH, param arms `Pⱼ.fwd.map_in_R`); `R_in_map` by `induction` on
  the `R_<T>` derivation (recursive arms use the IH, param arms
  `Pⱼ.fwd.R_in_map`). This reproduces the hand-written `paramList`/`paramOption`
  of `ParamData` generically, at the full `map3` forward level. The
  uniform-recursion guard is `isUniformRecursive`.
* Non-uniform recursion is out of scope (the labelled residual): a recursive
  occurrence *nested* under another type former (`List (T A)`), applied to
  *different* arguments, *under an arrow* (higher-order recursion), or an
  *indexed* family. `isUniformRecursive` returns `false`, so the uniform map path
  does not apply. (For genuinely nested recursion the relation generator itself
  does not apply — its `other`-by-equality lift is ill-typed across the two
  parameter instantiations — and the registered handler declines `iv.isNested`
  inductives up front.)

So: the `@[derive Param]` attribute is registered and runs; both the non-recursive
and the uniform-recursive path generate the relation and the forward `map3`
`Param` instance with the variance guard; non-uniform recursive map/proof
synthesis is the labelled residual.
-/

set_option autoImplicit false

open Lean Meta Elab Command Term Parser

namespace Transfer.Param

/-! ## `IndDesc`: AdapTT's description of an inductive's constructor signatures -/

/-- How a constructor field is lifted by the parametricity translation.
    * `param i`: a non-recursive covariant occurrence of the `i`-th type
      parameter — lifted by the supplied element relation `Pᵢ`.
    * `recursive`: the inductive applied to the params — lifted by the recursive
      relation `R_<T>`.
    * `other`: a parameter-free field type — lifted by equality. -/
inductive FieldKind
  | param (idx : Nat)
  | recursive
  /-- A `List (T p…)` field: the inductive nested under `List`, applied to the
      parameters in order. Lifted by `List.Forall₂ (R_<T> …)` in the relation,
      `·.map (T.paramMap …)` in the forward map (Extension 1, functorial-container
      nesting; `List` is the canonical container). -/
  | nestedList
  | other
  deriving Repr, Inhabited, DecidableEq

/-- A constructor: its name and the lift-classification of each field. -/
structure CtorDesc where
  name : Name
  fields : Array FieldKind
  deriving Inhabited

/-- A simple inductive's description: name, parameter count, constructors. The
    `IndDesc` of AdapTT's description-based scheme — the generator reads only this. -/
structure IndDesc where
  name : Name
  numParams : Nat
  ctors : Array CtorDesc
  deriving Inhabited

/-! ## Variance analysis and the mixed-variance guard -/

/-- Polarity (variance) of a parameter `p`'s occurrences in `e`.
    Returns `(occursPositively, occursNegatively)`; the domain of an arrow
    flips polarity. A parameter that comes back `(true, true)` is mixed
    variance — AdapTT's `NonExample`. -/
partial def occPol (p : FVarId) (pos : Bool) (e : Expr) : Bool × Bool :=
  match e with
  | .forallE _ d b _ =>
    let (dp, dn) := occPol p (!pos) d
    let (bp, bn) := occPol p pos b
    (dp || bp, dn || bn)
  | .app .. => Id.run do
    let (fp, fn) := occPol p pos e.getAppFn
    let mut rp := fp
    let mut rn := fn
    for a in e.getAppArgs do
      let (ap, an) := occPol p pos a
      rp := rp || ap
      rn := rn || an
    return (rp, rn)
  | .lam _ d b _ =>
    let (dp, dn) := occPol p (!pos) d
    let (bp, bn) := occPol p pos b
    (dp || bp, dn || bn)
  | .fvar fid => if fid == p then (if pos then (true, false) else (false, true)) else (false, false)
  | _ => (false, false)

/-- Is `e` the head `selfName` applied to *exactly the type parameters, in order*
    (`T p₀ … p_{k-1}`)? The uniform-recursion shape, reused to recognise the
    `List`-nested occurrence. -/
def isSelfAppliedToParams (selfName : Name) (pfids : Array FVarId) (e : Expr) : Bool := Id.run do
  unless e.isAppOf selfName do return false
  let args := e.getAppArgs
  unless args.size == pfids.size do return false
  for j in [:pfids.size] do
    unless args[j]!.isFVar && args[j]!.fvarId! == pfids[j]! do return false
  return true

/-- Classify a single constructor field type. Rejects mixed- and purely
    contravariant parameter occurrences (the `Param` element relation is
    covariant). A bare covariant occurrence `A` becomes `param i`; the inductive
    applied to the params becomes `recursive`; `List (T p…)` becomes `nestedList`;
    a parameter-free type is `other`. -/
def classifyField (selfName : Name) (pfids : Array FVarId) (ty : Expr) : MetaM FieldKind := do
  if isSelfAppliedToParams selfName pfids ty then
    return .recursive
  -- `List (T p…)`: the inductive nested under `List` (Extension 1). The element
  -- must be `T` applied to the parameters in order; deeper / other-container
  -- nesting falls through to the variance analysis below.
  if ty.isAppOf ``List then
    let args := ty.getAppArgs
    if args.size == 1 && isSelfAppliedToParams selfName pfids args[0]! then
      return .nestedList
  let mut hit : Option Nat := none
  for j in [:pfids.size] do
    let (pos, neg) := occPol pfids[j]! true ty
    if pos && neg then
      throwError "@[derive Param]: NonExample (Mixed variance)"
    if neg then
      throwError "@[derive Param]: NonExample (Contravariant variance)"
    if pos then
      if ty == (.fvar pfids[j]!) then
        hit := some j
      else
        -- positive but nested (e.g. `List A`): a previously-derived container.
        -- Out of scope for the uniform generator; classify as `other` so the
        -- relation still type-checks via equality (sound but coarse).
        hit := hit  -- leave as-is; fall through to `other` below
  match hit with
  | some j => return .param j
  | none => return .other

/-- Read a simple inductive into an `IndDesc`, classifying every constructor
    field — the `MetaM` extraction. The mixed-variance guard applies here. -/
def toIndDesc (declName : Name) : MetaM IndDesc := do
  let iv ← getConstInfoInduct declName
  let mut ctors : Array CtorDesc := #[]
  for c in iv.ctors do
    let ci ← getConstInfoCtor c
    let cd ← forallTelescopeReducing ci.type fun xs _ => do
      let pfids := (xs.extract 0 ci.numParams).map (·.fvarId!)
      let mut fields : Array FieldKind := #[]
      for i in [:ci.numFields] do
        let ty ← inferType xs[ci.numParams + i]!
        fields := fields.push (← classifyField declName pfids ty)
      return { name := c, fields }
    ctors := ctors.push cd
  return { name := declName, numParams := iv.numParams, ctors }

/-- Does `e` mention the constant `selfName` anywhere? Used to detect a
    recursive occurrence nested under another type former (e.g. `List (T A)`),
    which the uniform map generator does not handle. -/
partial def mentions (selfName : Name) (e : Expr) : Bool :=
  match e with
  | .const c _ => c == selfName
  | .app f a => mentions selfName f || mentions selfName a
  | .forallE _ d b _ => mentions selfName d || mentions selfName b
  | .lam _ d b _ => mentions selfName d || mentions selfName b
  | .mdata _ b => mentions selfName b
  | _ => false

/-- Is `T`'s recursion uniform (List/Tree-shape)? Every constructor field
    that mentions `T` must be `T` applied to *exactly the type parameters, in
    order* — a direct recursive sub-term. Fields with `T` nested under another
    type former (`List (T A)`), applied to different arguments, or under an
    arrow (higher-order recursion) make recursion non-uniform: the structural
    forward map / its proofs are out of scope, so the generator keeps such
    inductives relation-only. -/
def isUniformRecursive (declName : Name) : MetaM Bool := do
  let iv ← getConstInfoInduct declName
  for c in iv.ctors do
    let ci ← getConstInfoCtor c
    let ok ← forallTelescopeReducing ci.type fun xs _ => do
      let pfids := (xs.extract 0 ci.numParams).map (·.fvarId!)
      for i in [:ci.numFields] do
        let ty ← inferType xs[ci.numParams + i]!
        if ty.isAppOf declName then
          -- A top-level recursive occurrence: must be `T p₀ … p_{k-1}` exactly.
          let args := ty.getAppArgs
          unless args.size == pfids.size do return false
          for j in [:pfids.size] do
            unless args[j]!.isFVar && args[j]!.fvarId! == pfids[j]! do
              return false
        else if mentions declName ty then
          -- mentions `T` but not a clean top-level application: nested / arrow.
          return false
      return true
    unless ok do return false
  return true

/-! ## The relation generator -/

/-- Generate the relational lift `R_<T>` of an inductive uniformly from its
    `IndDesc`: a fresh inductive relation with one constructor per source
    constructor, the constructor-wise `Forall₂`-shape congruence. This is the
    shape `R_sum`/`R_prod`/`R_option`/`R_list` reproduce by hand. -/
def mkRelInductive (d : IndDesc) (relName : Name) : CommandElabM (TSyntax `command) := do
  let k := d.numParams
  let aIds := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}"))
  let aIds' := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}p"))
  let pIds := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"P{i}"))
  let allTypeIds := aIds ++ aIds'
  -- `{A0 A0' … : Type}`
  let typeBinder ← `(Term.bracketedBinderF| { $allTypeIds:ident* : Type })
  let mut relBinders : Array (TSyntax ``Term.bracketedBinder) := #[⟨typeBinder.raw⟩]
  for i in [:k] do
    relBinders := relBinders.push
      ⟨(← `(Term.bracketedBinderF| ( $(pIds[i]!) : $(aIds[i]!) → $(aIds'[i]!) → Prop ))).raw⟩
  let tName := mkIdent d.name
  let tApp ← `($tName $aIds*)
  let tApp' ← `($tName $aIds'*)
  let relId := mkIdent relName
  let mut ctorSyns : Array (TSyntax ``Parser.Command.ctor) := #[]
  for c in d.ctors do
    let cShort := mkIdent (Name.mkSimple c.name.componentsRev.head!.toString)
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let fIds' := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}p"))
    let cName := mkIdent c.name
    let mut hyps : Array (TSyntax `term) := #[]
    for i in [:n] do
      match c.fields[i]! with
      | .param j => hyps := hyps.push (← `($(pIds[j]!) $(fIds[i]!) $(fIds'[i]!)))
      | .recursive => hyps := hyps.push (← `($relId $pIds* $(fIds[i]!) $(fIds'[i]!)))
      | .nestedList =>
          hyps := hyps.push (← `(List.Forall₂ ($relId $pIds*) $(fIds[i]!) $(fIds'[i]!)))
      | .other => hyps := hyps.push (← `(@Eq _ $(fIds[i]!) $(fIds'[i]!)))
    let lhs ← `($cName $fIds*)
    let rhs ← `($cName $fIds'*)
    let concl ← `($relId $pIds* $lhs $rhs)
    let body ← hyps.foldrM (init := concl) (fun h acc => `($h → $acc))
    let allF := fIds ++ fIds'
    let ctorSyn ←
      if allF.isEmpty then
        `(Parser.Command.ctor| | $cShort:ident : $body)
      else
        `(Parser.Command.ctor| | $cShort:ident { $allF:ident* } : $body)
    ctorSyns := ctorSyns.push ctorSyn
  `(command|
    inductive $relId:ident $relBinders:bracketedBinder* : $tApp → $tApp' → Prop where
      $ctorSyns:ctor*)

/-- The relation name the handler emits for inductive `T`: `…T.R_param`. -/
def relNameFor (declName : Name) : Name :=
  declName ++ `R_param

/-- The forward-map name the handler emits for inductive `T`: `…T.paramMap`. -/
def mapNameFor (declName : Name) : Name :=
  declName ++ `paramMap

/-- The `Param` instance name the handler emits for inductive `T`:
    `…T.param_instance`. -/
def instNameFor (declName : Name) : Name :=
  declName ++ `param_instance

/-! ## The `Param .map3` instance generator (non-recursive inductives)

For a non-recursive inductive `T` (records / enums — the crypto carriers) the
relation `R_<T>` generated above is upgraded to a *full annotated relation*: a
forward `map` plus both graph inclusions (`map_in_R`, `R_in_map`). All three are
finite, per-constructor terms — no induction is needed because no field is the
inductive itself — so the handler synthesizes them directly, mirroring the
hand-written `paramProd`/`paramOption`/`paramList` of `ParamData` (which build the
same constructor-wise shape) but at the `map3` forward level (so the result is a
usable `Param`, e.g. it feeds `castViaParam`).

Element inputs are taken at `Param .map3 .map3` (the level supplying `map`,
`map_in_R`, `R_in_map` — `paramId`'s level), and the synthesized instance is
`Param .map3 .map0`: forward `map3`, backward `map0` (the relation alone backward,
as for the data combinators). -/

/-- Generate, for a non-recursive inductive `T`, the forward map
    `T.paramMap` and the `Param .map3 .map0` instance `T.param_instance` whose
    relation is the already-generated `R_<T>`. The per-field proofs are finite
    (no induction) because no field is the inductive itself. Recursive inductives
    are routed to `mkParamMapRecCmds` instead; the defensive guard below returns
    `#[]` should a recursive field reach here. -/
def mkParamMap1Cmds (d : IndDesc) (relName : Name) :
    CommandElabM (Array (TSyntax `command)) := do
  -- Defensive: recursive inductives go through `mkParamMapRecCmds`. If one
  -- reaches here, fall back to the relation-only path rather than emit a
  -- non-recursive map that would not type-check.
  for c in d.ctors do
    if c.fields.contains FieldKind.recursive || c.fields.contains FieldKind.nestedList then
      return #[]
  let k := d.numParams
  let aIds := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}"))
  let aIds' := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}p"))
  let pIds := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"P{i}"))
  let allTypeIds := aIds ++ aIds'
  let tName := mkIdent d.name
  let tApp ← `($tName $aIds*)
  let tApp' ← `($tName $aIds'*)
  let relId := mkIdent relName
  let mapId := mkIdent (mapNameFor d.name)
  let instId := mkIdent (instNameFor d.name)
  -- `{A0 A0' … : Type}` plus `(Pᵢ : Param .map3 .map3 Aᵢ Aᵢ')`.
  let typeBinder ← `(Term.bracketedBinderF| { $allTypeIds:ident* : Type })
  let mut pbinders : Array (TSyntax ``Term.bracketedBinder) := #[⟨typeBinder.raw⟩]
  for i in [:k] do
    pbinders := pbinders.push
      ⟨(← `(Term.bracketedBinderF|
            ( $(pIds[i]!) : Param .map3 .map3 $(aIds[i]!) $(aIds'[i]!) ))).raw⟩
  -- `T.paramMap`: constructor-wise, `Pⱼ.fwd.map` on a `param j` field, identity
  -- on an `other` field.
  let mut mapArms : Array (TSyntax ``Term.matchAlt) := #[]
  for c in d.ctors do
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let cName := mkIdent c.name
    let pat ← `($cName $fIds*)
    let mut rhsArgs : Array (TSyntax `term) := #[]
    for i in [:n] do
      match c.fields[i]! with
      | .param j => rhsArgs := rhsArgs.push (← `($(pIds[j]!).fwd.map $(fIds[i]!)))
      | .other => rhsArgs := rhsArgs.push (← `($(fIds[i]!)))
      | .recursive => pure ()  -- unreachable: guarded above
      | .nestedList => pure ()  -- unreachable: guarded above
    let rhs ← `($cName $rhsArgs*)
    mapArms := mapArms.push (← `(Term.matchAltExpr| | $pat => $rhs))
  let mapDef ← `(command|
    def $mapId:ident $pbinders:bracketedBinder* : $tApp → $tApp'
      $mapArms:matchAlt*)
  -- `R := R_<T> P0.R P1.R …`, `map := T.paramMap P0 P1 …`.
  let mut relArgs : Array (TSyntax `term) := #[]
  for i in [:k] do relArgs := relArgs.push (← `($(pIds[i]!).R))
  let rTerm ← `($relId $relArgs*)
  let mapTerm ← `($mapId $pIds*)
  let relCtorOf (c : CtorDesc) : Ident :=
    mkIdent (relName ++ Name.mkSimple c.name.componentsRev.head!.toString)
  -- `map_in_R`: `cases x`, then `exact R_<T>.<c> …` constructor-wise — per param
  -- field `Pⱼ.fwd.map_in_R _ _ rfl`, per `other` field `rfl`.
  let mut mirArms : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
  for c in d.ctors do
    let cShort := mkIdent (Name.mkSimple c.name.componentsRev.head!.toString)
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let relCtor := relCtorOf c
    let mut args : Array (TSyntax `term) := #[]
    for i in [:n] do
      match c.fields[i]! with
      | .param j => args := args.push (← `($(pIds[j]!).fwd.map_in_R $(fIds[i]!) _ rfl))
      | .other => args := args.push (← `(rfl))
      | .recursive => pure ()
      | .nestedList => pure ()
    let body ← `(tactic| exact $relCtor $args*)
    let seq ← `(tacticSeq| $body:tactic)
    mirArms := mirArms.push (← `(Lean.Parser.Tactic.inductionAlt| | $cShort $fIds* => $seq))
  -- `R_in_map`: `cases h` on the relation, then `simp [T.paramMap, …]` with the
  -- per-field `Pⱼ.fwd.R_in_map _ _ hᵢ` (param) / `hᵢ` (other equality).
  let mut rimArms : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
  for c in d.ctors do
    let cShort := mkIdent (Name.mkSimple c.name.componentsRev.head!.toString)
    let n := c.fields.size
    let hIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"h{i}"))
    let mut simpArgs : Array (TSyntax `term) := #[mapId]
    for i in [:n] do
      match c.fields[i]! with
      | .param j => simpArgs := simpArgs.push (← `($(pIds[j]!).fwd.R_in_map _ _ $(hIds[i]!)))
      | .other => simpArgs := simpArgs.push (← `($(hIds[i]!)))
      | .recursive => pure ()
      | .nestedList => pure ()
    let lemmas ← simpArgs.mapM (fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))
    let body ← `(tactic| simp [$lemmas,*])
    let seq ← `(tacticSeq| $body:tactic)
    rimArms := rimArms.push (← `(Lean.Parser.Tactic.inductionAlt| | $cShort $hIds* => $seq))
  let instDef ← `(command|
    instance $instId:ident $pbinders:bracketedBinder* :
        Param .map3 .map0 $tApp $tApp' where
      R := $rTerm
      fwd := {
        map := $mapTerm
        map_in_R := by
          intro x y e; subst e
          cases x with
          $mirArms:inductionAlt*
        R_in_map := by
          intro x y h
          cases h with
          $rimArms:inductionAlt*
      }
      bwd := ⟨⟩)
  pure #[mapDef, instDef]

/-! ## The `Param .map3` instance generator (uniform-recursive inductives)

For a uniform-recursive inductive `T` (List/Tree-shape: every recursive
field is `T` applied to the same parameters, no nesting / arrows / higher-order
recursion — `isUniformRecursive`), the relation `R_<T>` is upgraded to the same
full `Param .map3 .map0` annotated relation as the non-recursive path, but the
three forward fields are recursive:

* `T.paramMap` is generated by structural recursion: per constructor, apply
  each parameter's `fwd.map` to a `param` field, recurse `T.paramMap …` on each
  `recursive` field, leave `other` fields, rebuild with the constructor. Lean's
  equation compiler discharges termination (direct sub-term recursion).
* `map_in_R` is proved by `induction` on the value: each arm builds the
  `R_<T>` constructor from per-field facts — a `param` field via
  `Pⱼ.fwd.map_in_R`, an `other` field via `rfl`, a `recursive` field via the
  induction hypothesis.
* `R_in_map` is proved by `induction` on the `R_<T>` derivation (itself an
  inductive relation): each arm `simp [T.paramMap, …]`s with the per-field
  rewrite — a `param` field via `Pⱼ.fwd.R_in_map`, an `other` field via its
  equality hypothesis, a `recursive` field via the induction hypothesis.

This reproduces the hand-written `paramList`/`paramOption` of `ParamData`
generically, at the full `map3` forward level (so the result feeds
`castViaParam`). Element inputs are taken at `Param .map3 .map3` (as for the
non-recursive path / `paramId`). -/

/-- Generate, for a uniform-recursive inductive `T`, the structurally
    recursive forward map `T.paramMap` and the `Param .map3 .map0` instance
    `T.param_instance` whose relation is the already-generated `R_<T>`. Assumes
    `isUniformRecursive` held (otherwise returns `#[]`, relation-only). -/
def mkParamMapRecCmds (d : IndDesc) (relName : Name) :
    CommandElabM (Array (TSyntax `command)) := do
  let k := d.numParams
  let aIds := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}"))
  let aIds' := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}p"))
  let pIds := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"P{i}"))
  let allTypeIds := aIds ++ aIds'
  let tName := mkIdent d.name
  let tApp ← `($tName $aIds*)
  let tApp' ← `($tName $aIds'*)
  let relId := mkIdent relName
  let mapId := mkIdent (mapNameFor d.name)
  let instId := mkIdent (instNameFor d.name)
  -- `{A0 A0' … : Type}` plus `(Pᵢ : Param .map3 .map3 Aᵢ Aᵢ')`.
  let typeBinder ← `(Term.bracketedBinderF| { $allTypeIds:ident* : Type })
  let mut pbinders : Array (TSyntax ``Term.bracketedBinder) := #[⟨typeBinder.raw⟩]
  for i in [:k] do
    pbinders := pbinders.push
      ⟨(← `(Term.bracketedBinderF|
            ( $(pIds[i]!) : Param .map3 .map3 $(aIds[i]!) $(aIds'[i]!) ))).raw⟩
  -- `T.paramMap` (structural recursion): `Pⱼ.fwd.map` on a `param j` field,
  -- `T.paramMap P… xᵢ` on a `recursive` field, identity on an `other` field.
  let mut mapArms : Array (TSyntax ``Term.matchAlt) := #[]
  for c in d.ctors do
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let cName := mkIdent c.name
    let pat ← `($cName $fIds*)
    let mut rhsArgs : Array (TSyntax `term) := #[]
    for i in [:n] do
      match c.fields[i]! with
      | .param j => rhsArgs := rhsArgs.push (← `($(pIds[j]!).fwd.map $(fIds[i]!)))
      | .recursive => rhsArgs := rhsArgs.push (← `($mapId $pIds* $(fIds[i]!)))
      | .other => rhsArgs := rhsArgs.push (← `($(fIds[i]!)))
      | .nestedList => pure ()  -- unreachable: nested types route to mkParamMapNestedCmds
    let rhs ← `($cName $rhsArgs*)
    mapArms := mapArms.push (← `(Term.matchAltExpr| | $pat => $rhs))
  let mapDef ← `(command|
    def $mapId:ident $pbinders:bracketedBinder* : $tApp → $tApp'
      $mapArms:matchAlt*)
  -- `R := R_<T> P0.R …`, `map := T.paramMap P0 …`.
  let mut relArgs : Array (TSyntax `term) := #[]
  for i in [:k] do relArgs := relArgs.push (← `($(pIds[i]!).R))
  let rTerm ← `($relId $relArgs*)
  let mapTerm ← `($mapId $pIds*)
  let relCtorOf (c : CtorDesc) : Ident :=
    mkIdent (relName ++ Name.mkSimple c.name.componentsRev.head!.toString)
  -- `map_in_R`: `induction x`, then `exact R_<T>.<c> …` constructor-wise — a
  -- recursive field uses its IH, a `param` field `Pⱼ.fwd.map_in_R xᵢ _ rfl`, an
  -- `other` field `rfl`. The `induction` binder names every field `xᵢ`, then one
  -- IH `xrᵣ` per recursive field (in recursion order).
  let mut mirArms : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
  for c in d.ctors do
    let cShort := mkIdent (Name.mkSimple c.name.componentsRev.head!.toString)
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let relCtor := relCtorOf c
    let mut ihIds : Array Ident := #[]
    let mut args : Array (TSyntax `term) := #[]
    let mut r := 0
    for i in [:n] do
      match c.fields[i]! with
      | .param j => args := args.push (← `($(pIds[j]!).fwd.map_in_R $(fIds[i]!) _ rfl))
      | .other => args := args.push (← `(rfl))
      | .recursive =>
        let ih := mkIdent (Name.mkSimple s!"xr{r}")
        ihIds := ihIds.push ih
        args := args.push ih
        r := r + 1
      | .nestedList => pure ()  -- unreachable: nested types route to mkParamMapNestedCmds
    let binders := fIds ++ ihIds
    let body ← `(tactic| exact $relCtor $args*)
    let seq ← `(tacticSeq| $body:tactic)
    mirArms := mirArms.push (← `(Lean.Parser.Tactic.inductionAlt| | $cShort $binders* => $seq))
  -- `R_in_map`: `induction h` on the relation, then `simp [T.paramMap, …]` with
  -- per-field rewrites — a `param` field `Pⱼ.fwd.R_in_map _ _ hᵢ`, an `other`
  -- field `hᵢ`, a `recursive` field its IH. The `induction` binder names every
  -- field hypothesis `hᵢ`, then one IH `hrᵣ` per recursive field.
  let mut rimArms : Array (TSyntax ``Lean.Parser.Tactic.inductionAlt) := #[]
  for c in d.ctors do
    let cShort := mkIdent (Name.mkSimple c.name.componentsRev.head!.toString)
    let n := c.fields.size
    let hIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"h{i}"))
    let mut ihIds : Array Ident := #[]
    let mut simpArgs : Array (TSyntax `term) := #[mapId]
    let mut r := 0
    for i in [:n] do
      match c.fields[i]! with
      | .param j => simpArgs := simpArgs.push (← `($(pIds[j]!).fwd.R_in_map _ _ $(hIds[i]!)))
      | .other => simpArgs := simpArgs.push (← `($(hIds[i]!)))
      | .recursive =>
        let ih := mkIdent (Name.mkSimple s!"hr{r}")
        ihIds := ihIds.push ih
        simpArgs := simpArgs.push ih
        r := r + 1
      | .nestedList => pure ()  -- unreachable: nested types route to mkParamMapNestedCmds
    let binders := hIds ++ ihIds
    let lemmas ← simpArgs.mapM (fun t => `(Lean.Parser.Tactic.simpLemma| $t:term))
    let body ← `(tactic| simp [$lemmas,*])
    let seq ← `(tacticSeq| $body:tactic)
    rimArms := rimArms.push (← `(Lean.Parser.Tactic.inductionAlt| | $cShort $binders* => $seq))
  let instDef ← `(command|
    instance $instId:ident $pbinders:bracketedBinder* :
        Param .map3 .map0 $tApp $tApp' where
      R := $rTerm
      fwd := {
        map := $mapTerm
        map_in_R := by
          intro x y e; subst e
          induction x with
          $mirArms:inductionAlt*
        R_in_map := by
          intro x y h
          induction h with
          $rimArms:inductionAlt*
      }
      bwd := ⟨⟩)
  pure #[mapDef, instDef]

/-! ## The `Param .map3` instance generator (nested-`List`-recursive inductives)

Extension 1. For an inductive `T` with a `List (T p…)` field (the `Rose`-shape),
the forward map recurses *through* `List.map`, and the two graph inclusions are
proved by mutual structural recursion with a `List` helper — the `induction`
tactic rejects nested inductives, but the equation compiler accepts the mutual
recursion. The relation `R_<T>` (from `mkRelInductive`) already lifts the nested
field by `List.Forall₂`. `List` is the canonical functorial container; `Option` /
`Array` are the same shape (a registered map + relation lifter + congruence). -/

/-- Does `T` have a `List (T p…)` field (the nested-`List`-recursive shape that
    `mkParamMapNestedCmds` handles)? -/
def isNestedListSupported (d : IndDesc) : Bool :=
  d.ctors.any (·.fields.contains FieldKind.nestedList)

/-- Generate, for a nested-`List`-recursive inductive `T`, the forward map
    `T.paramMap` (structural recursion through `List.map`) and the full
    `Param .map3 .map0` instance, with `map_in_R` / `R_in_map` proved by mutual
    structural recursion + a `List` helper. Relation is the generated `R_<T>`. -/
def mkParamMapNestedCmds (d : IndDesc) (relName : Name) :
    CommandElabM (Array (TSyntax `command)) := do
  let k := d.numParams
  let aIds  := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}"))
  let aIds' := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"A{i}p"))
  let pIds  := (Array.range k).map (fun i => mkIdent (Name.mkSimple s!"P{i}"))
  let allTypeIds := aIds ++ aIds'
  let tName := mkIdent d.name
  let tApp  ← `($tName $aIds*)
  let tApp' ← `($tName $aIds'*)
  let mapId  := mkIdent (mapNameFor d.name)
  let mirId  := mkIdent (d.name ++ `param_mapInR)
  let mirLId := mkIdent (d.name ++ `param_mapInR_list)
  let rimId  := mkIdent (d.name ++ `param_RinMap)
  let rimLId := mkIdent (d.name ++ `param_RinMap_list)
  let instId := mkIdent (instNameFor d.name)
  -- binder telescope `{A0 A0' … : Type}` then `(Pᵢ : Param .map3 .map3 Aᵢ Aᵢ')`.
  let typeBinder ← `(Term.bracketedBinderF| { $allTypeIds:ident* : Type })
  let mut pbinders : Array (TSyntax ``Term.bracketedBinder) := #[⟨typeBinder.raw⟩]
  for i in [:k] do
    pbinders := pbinders.push
      ⟨(← `(Term.bracketedBinderF|
            ( $(pIds[i]!) : Param .map3 .map3 $(aIds[i]!) $(aIds'[i]!) ))).raw⟩
  let mut relArgs : Array (TSyntax `term) := #[]
  for i in [:k] do relArgs := relArgs.push (← `($(pIds[i]!).R))
  let relApp ← `($(mkIdent relName) $relArgs*)   -- R_<T> P0.R …
  let mapApp ← `($mapId $pIds*)                   -- T.paramMap P0 …
  let relCtorOf (c : CtorDesc) : Ident :=
    mkIdent (relName ++ Name.mkSimple c.name.componentsRev.head!.toString)
  -- (1) forward map (structural recursion through `List.map`).
  let mut mapArms : Array (TSyntax ``Term.matchAlt) := #[]
  for c in d.ctors do
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let cName := mkIdent c.name
    let pat ← `($cName $fIds*)
    let mut rhsArgs : Array (TSyntax `term) := #[]
    for i in [:n] do
      match c.fields[i]! with
      | .param j    => rhsArgs := rhsArgs.push (← `($(pIds[j]!).fwd.map $(fIds[i]!)))
      | .recursive  => rhsArgs := rhsArgs.push (← `($mapApp $(fIds[i]!)))
      | .nestedList => rhsArgs := rhsArgs.push (← `(List.map $mapApp $(fIds[i]!)))
      | .other      => rhsArgs := rhsArgs.push (← `($(fIds[i]!)))
    let rhs ← `($cName $rhsArgs*)
    mapArms := mapArms.push (← `(Term.matchAltExpr| | $pat => $rhs))
  let mapDef ← `(command|
    def $mapId:ident $pbinders:bracketedBinder* : $tApp → $tApp'
      $mapArms:matchAlt*)
  -- (2) map_in_R (main) arms: `by rw [T.paramMap]; exact R_<T>.c <perfield>`.
  let mut mirArms : Array (TSyntax ``Term.matchAlt) := #[]
  for c in d.ctors do
    let n := c.fields.size
    let fIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let cName := mkIdent c.name
    let relCtor := relCtorOf c
    let pat ← `($cName $fIds*)
    let mut args : Array (TSyntax `term) := #[]
    for i in [:n] do
      match c.fields[i]! with
      | .param j    => args := args.push (← `($(pIds[j]!).fwd.map_in_R $(fIds[i]!) _ rfl))
      | .recursive  => args := args.push (← `($mirId $pIds* $(fIds[i]!)))
      | .nestedList => args := args.push (← `($mirLId $pIds* $(fIds[i]!)))
      | .other      => args := args.push (← `(rfl))
    let proof ← `(by rw [$mapId:ident]; exact $relCtor $args*)
    mirArms := mirArms.push (← `(Term.matchAltExpr| | $pat => $proof))
  let mirType ← `(∀ x : $tApp, $relApp x ($mapApp x))
  let mirThm ← `(command| theorem $mirId:ident $pbinders:bracketedBinder* : $mirType
      $mirArms:matchAlt*)
  let mirLType ← `(∀ xs : List $tApp, List.Forall₂ $relApp xs (List.map $mapApp xs))
  let mirLThm ← `(command| theorem $mirLId:ident $pbinders:bracketedBinder* : $mirLType
      | [] => List.Forall₂.nil
      | hd :: tl => List.Forall₂.cons ($mirId $pIds* hd) ($mirLId $pIds* tl))
  let mutMapInR ← `(command| mutual $mirThm:command $mirLThm:command end)
  -- (3) R_in_map (main) arms: match `x`, `y`, derivation; `rw [T.paramMap, <field eqs>]`.
  let mut rimArms : Array (TSyntax ``Term.matchAlt) := #[]
  for c in d.ctors do
    let n := c.fields.size
    let xIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"x{i}"))
    let yIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"y{i}"))
    let hIds := (Array.range n).map (fun i => mkIdent (Name.mkSimple s!"h{i}"))
    let cName := mkIdent c.name
    let relCtor := relCtorOf c
    let xpat ← `($cName $xIds*)
    let ypat ← `($cName $yIds*)
    let dpat ← `($relCtor $hIds*)
    let mut rws : Array (TSyntax ``Lean.Parser.Tactic.rwRule) :=
      #[← `(Lean.Parser.Tactic.rwRule| $mapId:ident)]
    for i in [:n] do
      let t ← match c.fields[i]! with
        | .param j    => `($(pIds[j]!).fwd.R_in_map _ _ $(hIds[i]!))
        | .recursive  => `($rimId $pIds* $(hIds[i]!))
        | .nestedList => `($rimLId $pIds* $(hIds[i]!))
        | .other      => `($(hIds[i]!))
      rws := rws.push (← `(Lean.Parser.Tactic.rwRule| $t:term))
    let proof ← `(by rw [$rws,*])
    rimArms := rimArms.push (← `(Term.matchAltExpr| | $xpat, $ypat, $dpat => $proof))
  let rimType ← `(∀ {x : $tApp} {y : $tApp'}, $relApp x y → $mapApp x = y)
  let rimThm ← `(command| theorem $rimId:ident $pbinders:bracketedBinder* : $rimType
      $rimArms:matchAlt*)
  let rimLType ← `(∀ {xs : List $tApp} {ys : List $tApp'},
      List.Forall₂ $relApp xs ys → List.map $mapApp xs = ys)
  let hr := mkIdent `hr
  let ht := mkIdent `ht
  let eHr ← `($rimId $pIds* $hr)
  let eHt ← `($rimLId $pIds* $ht)
  let rwCons : Array (TSyntax ``Lean.Parser.Tactic.rwRule) := #[
    ← `(Lean.Parser.Tactic.rwRule| List.map_cons),
    ← `(Lean.Parser.Tactic.rwRule| $eHr:term),
    ← `(Lean.Parser.Tactic.rwRule| $eHt:term)]
  let rimLThm ← `(command| theorem $rimLId:ident $pbinders:bracketedBinder* : $rimLType
      | [], [], List.Forall₂.nil => rfl
      | _ :: _, _ :: _, List.Forall₂.cons $hr $ht => by rw [$rwCons,*])
  let mutRInMap ← `(command| mutual $rimThm:command $rimLThm:command end)
  -- (4) the instance, wiring the four recursive lemmas.
  let instDef ← `(command|
    instance $instId:ident $pbinders:bracketedBinder* :
        Param .map3 .map0 $tApp $tApp' where
      R := $relApp
      fwd := {
        map := $mapApp
        map_in_R := fun x y e => by subst e; exact $mirId $pIds* x
        R_in_map := fun _ _ h => $rimId $pIds* h
      }
      bwd := ⟨⟩)
  pure #[mapDef, mutMapInR, mutRInMap, instDef]

/-- Commands the `@[derive Param]` handler emits for one inductive: the
    relational lift `R_<T>` (the constructor-wise congruence) and the forward map
    `T.paramMap` + `Param .map3 .map0` instance `T.param_instance`. The
    non-recursive path (`mkParamMap1Cmds`), the uniform-recursive path
    (`mkParamMapRecCmds`), and the nested-`List`-recursive path
    (`mkParamMapNestedCmds`) all reach the full `map3` forward instance. Other
    non-uniform recursion (other-container nesting / arrows / indexed) stays
    relation-only. -/
def mkParamDeriveCmds (declName : Name) : CommandElabM (Array (TSyntax `command)) := do
  let d ← liftTermElabM <| toIndDesc declName
  let hasRec := d.ctors.any (·.fields.contains FieldKind.recursive)
  let relCmd ← mkRelInductive d (relNameFor declName)
  let instCmds ←
    if isNestedListSupported d then
      mkParamMapNestedCmds d (relNameFor declName)
    else if hasRec then
      if ← liftTermElabM (isUniformRecursive declName) then
        mkParamMapRecCmds d (relNameFor declName)
      else
        pure #[]
    else
      mkParamMap1Cmds d (relNameFor declName)
  return #[relCmd] ++ instCmds

/-- Elaborate a generated command at the root namespace. The generated
    relation carries its fully-qualified name (`<T>.R_param`), so it must be
    declared with the current namespace cleared — otherwise an open namespace
    would be prepended a second time. (Deriving handlers proper already run at
    root; this makes the generator namespace-robust for the in-file demo too.) -/
def elabAtRoot (cmd : TSyntax `command) : CommandElabM Unit :=
  withScope (fun s => { s with currNamespace := Name.anonymous }) <| elabCommand cmd

/-! ## Registration as the `@[derive Param]` deriving handler -/

/-- The deriving handler for `Param`. Generates, for each named simple inductive,
    its relational lift `R_<T>` uniformly from the constructor signatures, with
    the mixed-variance guard. Returns `false` (unhandled) for inductives the
    uniform generator does not yet cover (nested / reflexive / indexed families),
    so other handlers / a manual derivation can take over. -/
def mkParamInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let some _ := (← getEnv).find? declName | return false
    let .inductInfo iv ← getConstInfo declName | return false
    -- A nested inductive is accepted only when its nesting is the supported
    -- `List (T p…)` shape (Extension 1); other nesting / reflexive / indexed
    -- families are declined so another handler can take over.
    let nestedOk ← liftTermElabM do return isNestedListSupported (← toIndDesc declName)
    if (iv.isNested && !nestedOk) || iv.isReflexive || iv.numIndices != 0 then
      return false
    let cmds ← mkParamDeriveCmds declName
    for cmd in cmds do
      elabAtRoot cmd
  return true

initialize
  registerDerivingHandler ``Param mkParamInstanceHandler

/-! ## Demos

Lean's `initialize` blocks take effect only after the enclosing module is
imported, so the `registerDerivingHandler` above is live for *downstream* files
(`deriving Param` / `deriving instance Param for T` there route to
`mkParamInstanceHandler`) but not within this module. To exercise the generator
here it is invoked directly via `run_cmd` — the same `MetaM`/command
elaboration the registered handler runs — defining the test inductives first and
then emitting their relational lift `R_param`. -/

section Demo

/-- A binary product-like inductive (two covariant parameters). -/
inductive Pair (A B : Type) where
  | mk : A → B → Pair A B

/-- A recursive inductive (one covariant parameter + recursive subterms). -/
inductive Tree (A : Type) where
  | leaf : A → Tree A
  | node : Tree A → Tree A → Tree A

/-- A parameter-free enum (the base case: relation collapses to a tag match). -/
inductive Dir where
  | up | down

-- Run the generator (the body of the registered handler) on the three demo
-- inductives, emitting `Pair.R_param`, `Tree.R_param`, `Dir.R_param`.
run_cmd do
  for n in [``Pair, ``Tree, ``Dir] do
    for cmd in (← mkParamDeriveCmds n) do
      elabAtRoot cmd

/-- The generated `Pair.R_param`: two pairs are related iff their components are
    related by the supplied element relations — the constructor-wise congruence. -/
example {A A' B B' : Type} (PA : A → A' → Prop) (PB : B → B' → Prop)
    (a : A) (a' : A') (b : B) (b' : B') (ha : PA a a') (hb : PB b b') :
    Pair.R_param PA PB (Pair.mk a b) (Pair.mk a' b') :=
  Pair.R_param.mk ha hb

/-- The generated relation has the expected shape (signature check). -/
example {A A' B B' : Type} : (A → A' → Prop) → (B → B' → Prop) →
    Pair A B → Pair A' B' → Prop :=
  Pair.R_param

/-- Generated recursive relation on `Tree`: related leaves from related
    elements. -/
example {A A' : Type} (P : A → A' → Prop) (a : A) (a' : A') (h : P a a') :
    Tree.R_param P (Tree.leaf a) (Tree.leaf a') :=
  Tree.R_param.leaf h

/-- Related nodes from recursively related subtrees: the `recursive` field
    classification feeds the recursive relation `Tree.R_param`. -/
example {A A' : Type} (P : A → A' → Prop) (a : A) (a' : A')
    (hl : Tree.R_param P (Tree.leaf a) (Tree.leaf a'))
    (hr : Tree.R_param P (Tree.leaf a) (Tree.leaf a')) :
    Tree.R_param P (Tree.node (Tree.leaf a) (Tree.leaf a))
                   (Tree.node (Tree.leaf a') (Tree.leaf a')) :=
  Tree.R_param.node hl hr

/-- Parameter-free `Dir`: the relation collapses to a per-tag match (the
    parameter-free base case, mirroring `R_nat`'s shape). -/
example : Dir.R_param Dir.up Dir.up := Dir.R_param.up

/-- The non-recursive `Pair` also gets a full `Param .map3 .map0` instance:
    its forward map is the componentwise lift, witnessed via `castViaParam`. -/
example {A A' B B' : Type}
    (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B') (a : A) (b : B) :
    castViaParam (Pair.param_instance PA PB) (Pair.mk a b)
      = Pair.mk (PA.fwd.map a) (PB.fwd.map b) := rfl

/-- The parameter-free `Dir` instance's `castViaParam` is the identity on tags. -/
example : castViaParam Dir.param_instance Dir.up = Dir.up := rfl

/-! ### Recursive instance: `Tree` and `MyList` get the full `map3` instance

The `run_cmd` above ran the generator on `Tree`, which `isUniformRecursive`
accepts (the `node` subtrees are `Tree A` — the inductive at the same param), so
the uniform-recursive path applies and emits `Tree.paramMap` + `Tree.param_instance`.
A `cons`-shaped `MyList` (a `param` and a `recursive` field in one constructor)
exercises the mixed-field arm. -/

/-- A `cons`-list-shaped recursive inductive (one param + recursive tail). -/
inductive MyList (A : Type) where
  | nil : MyList A
  | cons : A → MyList A → MyList A

-- The generator on `MyList`: uniform recursion, so it emits the full instance.
run_cmd do
  for cmd in (← mkParamDeriveCmds ``MyList) do
    elabAtRoot cmd

/-- `Tree.param_instance` exists: the recursive forward
    map transports a leaf across, applying the element map at the leaf. -/
example {A A' : Type} (P : Param .map3 .map3 A A') (a : A) :
    castViaParam (Tree.param_instance P) (Tree.leaf a) = Tree.leaf (P.fwd.map a) := rfl

/-- The recursive forward map recurses into `node` subtrees. -/
example {A A' : Type} (P : Param .map3 .map3 A A') (a b : A) :
    castViaParam (Tree.param_instance P) (Tree.node (Tree.leaf a) (Tree.leaf b))
      = Tree.node (Tree.leaf (P.fwd.map a)) (Tree.leaf (P.fwd.map b)) := rfl

/-- The synthesized `map_in_R` holds on a concrete tree: a value is
    `R_param`-related to its own forward image (here on the diagonal via
    `paramId`). -/
example (a b : Nat) :
    (Tree.param_instance (paramId Nat)).R
      (Tree.node (Tree.leaf a) (Tree.leaf b))
      (castViaParam (Tree.param_instance (paramId Nat))
        (Tree.node (Tree.leaf a) (Tree.leaf b))) :=
  (Tree.param_instance (paramId Nat)).fwd.map_in_R _ _ rfl

/-- `MyList.param_instance` (the mixed param+recursive `cons` arm): `castViaParam`
    maps a concrete list across, applying the element map elementwise. -/
example {A A' : Type} (P : Param .map3 .map3 A A') (a b : A) :
    castViaParam (MyList.param_instance P) (MyList.cons a (MyList.cons b MyList.nil))
      = MyList.cons (P.fwd.map a) (MyList.cons (P.fwd.map b) MyList.nil) := rfl

/-- The `MyList` `map_in_R` graph inclusion holds on a concrete list. -/
example (a b : Nat) :
    (MyList.param_instance (paramId Nat)).R
      (MyList.cons a (MyList.cons b MyList.nil))
      (castViaParam (MyList.param_instance (paramId Nat))
        (MyList.cons a (MyList.cons b MyList.nil))) :=
  (MyList.param_instance (paramId Nat)).fwd.map_in_R _ _ rfl

-- `#print axioms` of the recursive instance: `propext` only (the structural
-- recursion and `induction` proofs stay within the `Param` hierarchy's
-- `Prop`-valued relations).
/-- info: 'Transfer.Param.Tree.param_instance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Tree.param_instance

/-! ### Nested-`List` recursive instance: `RoseT` gets the FULL `map3` instance (Extension 1)

A `Rose`-shape inductive — a recursive occurrence nested under `List` — is routed
by `isNestedListSupported` to `mkParamMapNestedCmds`. Its forward map recurses
through `List.map`, and the two graph inclusions are proved by mutual structural
recursion with a `List` helper (the `induction` tactic rejects nested inductives;
the equation compiler accepts the mutual recursion). -/

/-- A rose tree: children nested under `List` (the canonical functorial container). -/
inductive RoseT (A : Type) where
  | node : A → List (RoseT A) → RoseT A

-- The generator on `RoseT`: the nested-`List` path, emitting `RoseT.paramMap`,
-- the two mutual proof blocks, and `RoseT.param_instance`.
run_cmd do
  for cmd in (← mkParamDeriveCmds ``RoseT) do
    elabAtRoot cmd

/-- `RoseT.param_instance` exists: the nested forward map applies the element map at
    the head and recurses through `List.map` into the children. -/
example {A A' : Type} (P : Param .map3 .map3 A A') (a b : A) :
    castViaParam (RoseT.param_instance P) (RoseT.node a [RoseT.node b []])
      = RoseT.node (P.fwd.map a) [RoseT.node (P.fwd.map b) []] := by
  simp [castViaParam, RoseT.param_instance, RoseT.paramMap]

/-- The nested `map_in_R` graph inclusion holds on a concrete rose tree. -/
example (a b : Nat) :
    (RoseT.param_instance (paramId Nat)).R
      (RoseT.node a [RoseT.node b []])
      (castViaParam (RoseT.param_instance (paramId Nat))
        (RoseT.node a [RoseT.node b []])) :=
  (RoseT.param_instance (paramId Nat)).fwd.map_in_R _ _ rfl

/-- The nested `R_in_map` graph inclusion: the relation determines the forward
    image (single-valued through the map). -/
example (a b : Nat) (y : RoseT Nat)
    (h : (RoseT.param_instance (paramId Nat)).R (RoseT.node a [RoseT.node b []]) y) :
    castViaParam (RoseT.param_instance (paramId Nat))
      (RoseT.node a [RoseT.node b []]) = y :=
  (RoseT.param_instance (paramId Nat)).fwd.R_in_map _ _ h

-- The nested instance's `paramMap` recurses through `List.map`, whose equation
-- compilation brings in `Quot.sound` (alongside `propext`); both are standard.
/-- info: 'Transfer.Param.RoseT.param_instance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RoseT.param_instance

end Demo

/-! ## Crypto-record demos: a derived `Param .map3 .map0` instance in use

A `@[derive Param]` on a non-recursive crypto carrier
(an enum like a participant `Role`, a record like an ElGamal ciphertext or a
signature pair) yields a usable annotated relation — a forward map (via
`castViaParam`) and the proved graph inclusion `map_in_R` — not just `R_<T>`. -/

section CryptoDemo

/-- A participant role (parameter-free enum). -/
inductive Role where
  | prover | verifier

/-- An ElGamal ciphertext over a group carrier `G`: a pair of group elements. -/
inductive ElGamalCt (G : Type) where
  | mk : G → G → ElGamalCt G

/-- A signature pair: a group element plus a (parameter-free) scalar tag. -/
inductive SigPair (G : Type) where
  | mk : G → Nat → SigPair G

-- The generator (the registered handler's body) on the crypto carriers, emitting
-- `R_param`, `paramMap`, and the `Param .map3 .map0` `param_instance` for each.
run_cmd do
  for n in [``Role, ``ElGamalCt, ``SigPair] do
    for cmd in (← mkParamDeriveCmds n) do
      elabAtRoot cmd

/-- The derived `Role.param_instance` carries a forward map; `castViaParam`
    transports a value across (identity on the diagonal). -/
example : castViaParam Role.param_instance Role.prover = Role.prover := rfl

/-- The derived `ElGamalCt` instance's forward map is the componentwise group-map
    lift, transporting a ciphertext across the relation. -/
example {G G' : Type} (PG : Param .map3 .map3 G G') (c0 c1 : G) :
    castViaParam (ElGamalCt.param_instance PG) (ElGamalCt.mk c0 c1)
      = ElGamalCt.mk (PG.fwd.map c0) (PG.fwd.map c1) := rfl

/-- The synthesized `map_in_R` holds: a value is `R_param`-related to its own
    forward image under the derived map. (Here on the diagonal via `paramId`.) -/
example (c0 c1 : Nat) :
    (ElGamalCt.param_instance (paramId Nat)).R (ElGamalCt.mk c0 c1)
      (castViaParam (ElGamalCt.param_instance (paramId Nat)) (ElGamalCt.mk c0 c1)) :=
  (ElGamalCt.param_instance (paramId Nat)).fwd.map_in_R _ _ rfl

/-- The `SigPair` instance keeps the parameter-free `Nat` tag fixed under the
    forward map (the `other`-field case), transported across by `castViaParam`. -/
example (g : Nat) (s : Nat) :
    castViaParam (SigPair.param_instance (paramId Nat)) (SigPair.mk g s)
      = SigPair.mk g s := rfl

/-- And its `map_in_R` graph inclusion holds. -/
example (g : Nat) (s : Nat) :
    (SigPair.param_instance (paramId Nat)).R (SigPair.mk g s)
      (castViaParam (SigPair.param_instance (paramId Nat)) (SigPair.mk g s)) :=
  (SigPair.param_instance (paramId Nat)).fwd.map_in_R _ _ rfl

-- `#print axioms` of a derived crypto instance: `propext` only (from the
-- `Param` hierarchy's `Prop`-valued relations).
/-- info: 'Transfer.Param.ElGamalCt.param_instance' depends on axioms: [propext] -/
#guard_msgs in
#print axioms ElGamalCt.param_instance

end CryptoDemo

/-! ## The mixed-variance non-example is rejected

`toIndDesc` (hence the `@[derive Param]` handler) rejects an inductive whose
parameter occurs in both co- and contravariant position — AdapTT's
`NonExample (Mixed variance)`. -/

section MixedVarianceGuard

/-- A field of type `A → A` makes `A` mixed-variance. -/
inductive Endo (A : Type) where
  | mk : (A → A) → Endo A

-- `#guard_msgs` pin of the rejection diagnostic: running the generator on
-- `Endo` raises the `NonExample (Mixed variance)` error the handler would.
/-- error: @[derive Param]: NonExample (Mixed variance) -/
#guard_msgs in
run_cmd liftTermElabM do
  let _ ← toIndDesc ``Endo
  pure ()

end MixedVarianceGuard

/-! ## The non-uniform-recursion boundary

A recursive occurrence nested under another type former (`List (Rose A)`),
applied to different arguments, under an arrow, or in an indexed family is
non-uniform: the structural forward map / its proofs are out of scope.
`isUniformRecursive` is the gate — it returns `false`, so the uniform-recursive
map path does not apply. (For genuinely nested recursion such as `Rose` below the
relation generator itself does not apply either — its `other`-by-equality lift is
ill-typed across the two parameter instantiations, and the registered handler
declines such inductives up front via `iv.isNested`. The labelled residual is
thus: only the uniform List/Tree shape reaches the full `map3` instance.) -/

section NonUniformBoundary

/-- A rose tree: the children are a `List (Rose A)` — recursion nested under
    `List`, hence non-uniform. Used only to exercise the `isUniformRecursive`
    classifier; the generator is not run on it. -/
inductive Rose (A : Type) where
  | node : A → List (Rose A) → Rose A

-- `isUniformRecursive` classifies `Rose` as non-uniform (`false`) and
-- `Tree`/`MyList` as uniform (`true`) — the gate that routes the two paths.
run_cmd liftTermElabM do
  guard (! (← isUniformRecursive ``Rose))
  guard (← isUniformRecursive ``Tree)
  guard (← isUniformRecursive ``MyList)

end NonUniformBoundary

end Transfer.Param
