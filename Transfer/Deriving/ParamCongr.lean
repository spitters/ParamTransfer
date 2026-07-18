/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Related
import Lean

/-!
# `derive_param_congr` — a constructor-congruence `Related` deriver

The `Related` kernel (`Transfer/Base/Related.lean`) auto-composes binary-op trees
on a *single* carrier (`composeBinOp` over `RelatedBinOp` squares) but stops at
any *structure* head: it provides no constructor congruence for user inductives.
Crossing a structure boundary (e.g. a value of a single-constructor structure
that encodes to the product of its fields) therefore needs, per type, one
product-encoding `enc` plus one constructor-congruence `Related` instance — the
`Param_<T>` boilerplate.

This file generates that boilerplate. It is the Trocq/Elpi `Param_<T>` analogue
for the `Related` kernel: a metaprogram that, for a single-constructor structure
`T`, *reads the constructor's field names and types* and emits

* a `ParamEnc T α` instance — the product encoding
  `enc x = (ParamEnc.enc x.f₁, …, ParamEnc.enc x.fₙ)`, where each field's encoding
  is resolved recursively through `ParamEnc` (so nested derived structures
  compose automatically), and
* the constructor congruence `Related (ParamEnc.enc) (T.mk a₁ … aₙ)
  (a₁', …, aₙ')` from the per-field `Related (ParamEnc.enc) aᵢ aᵢ'` facts.

With both registered, instance resolution transports a structured value
*compositionally* — the constructor congruence on top, the base-carrier
`RelatedBinOp` squares underneath — with no monolithic whole-op leaf.

## Surface

* `derive_param_congr T` — a `command` elaborator (works in-file), and
* `deriving instance ParamCongr for T` / `deriving ParamCongr` — the registered
  deriving handler (live for *downstream* modules, since `initialize` takes
  effect only after this module is imported).

Both route to the same generator, `deriveParamCongrCore`.

## Reflective-vs-assumed boundary

* Reflective (read off the structure): the constructor name, the field
  names, the field types (hence the `aᵢ` binders), the structure's parameters
  (the generated instances are parametric in them), and each field's encoded
  type `αᵢ` (via `ParamEnc.enc`-type inference, so nested structures' encodings
  compose).
* Assumed / out of scope (matching the structure focus of relational
  parametricity derivers): single constructor only (multi-constructor inductives
  and indexed/dependent families are rejected); the per-field encodings are
  whatever `ParamEnc` resolves to (an atomic field uses the low-priority `id`
  leaf; a nested structure uses its own derived instance — derive bottom-up); the
  base-carrier op squares (`RelatedBinOp`) are *supplied*, never invented — the
  `relatedBinOpOfLeaf` bridge only re-uses an existing `id`-registered square at
  the `ParamEnc`-leaf encoding.
-/

set_option autoImplicit false

namespace Transfer.Deriving

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.PrettyPrinter Lean.Parser.Term
open Transfer

/-! ## 1. The field-encoding typeclass -/

/-- `ParamEnc A α`: a registered encoding `A → α` for the structure-field
    recursion. The derived `ParamEnc T _` instance for a structure encodes it to
    the product of its fields' encodings, so the recursion is automatic. -/
class ParamEnc (A : Type) (α : outParam Type) where
  /-- The encoding map. -/
  enc : A → α

/-- Leaf. An atomic type encodes to itself by `id`. Low priority so a derived
    structure instance (default priority) wins when both could apply. -/
instance (priority := low) paramEncLeaf {A : Type} : ParamEnc A A := ⟨id⟩

/-- Bridge. Any base-carrier `RelatedBinOp` registered at the `id` encoding
    lifts to the `ParamEnc`-leaf encoding for free (`ParamEnc.enc` at a leaf type
    is definitionally `id`). One instance re-uses every `id`-registered op square
    under the derived congruence — no per-op boilerplate. -/
instance (priority := low) relatedBinOpOfLeaf {A : Type} (op bop : A → A → A)
    [h : RelatedBinOp (id : A → A) op bop] :
    RelatedBinOp (ParamEnc.enc : A → A) op bop where
  comm := h.comm

/-- Leaf-encoding `Related`. `a` transports to itself along the `ParamEnc`
    leaf (it is `id`). Gives the base case of the congruence's per-coordinate
    composition an RHS that is literally the input (not `ParamEnc.enc a`), so
    `composeBinOp` terminates cleanly at base-carrier variables. -/
instance (priority := low) paramEncLeafRelated {A : Type} (a : A) :
    Related (ParamEnc.enc : A → A) a a where
  rel := rfl

/-- Marker class keying the `deriving` handler (`deriving instance ParamCongr for
    T`). The handler generates the `ParamEnc`/`Related` instances and ignores the
    literal class. -/
class ParamCongr (A : Sort _) : Prop

/-! ## 2. The generator -/

/-- Build the anonymous tuple syntax `(x₀, …, xₙ₋₁)` (right-nested `Prod.mk`);
    a singleton is returned bare. -/
def mkTupleStx (xs : Array Term) : CommandElabM Term := do
  if xs.size == 1 then
    return xs[0]!
  else
    let hd := xs[0]!
    let tl := xs.extract 1 xs.size
    `(($hd, $tl,*))

/-- Build the right-nested product type syntax `x₀ × … × xₙ₋₁`; a singleton is
    returned bare. -/
def mkProdTypeStx (xs : Array Term) : CommandElabM Term := do
  let mut acc := xs[xs.size - 1]!
  for i in [0 : xs.size - 1] do
    let j := xs.size - 2 - i
    acc ← `($(xs[j]!) × $acc)
  return acc

/-- The core generator: read single-constructor structure `declName` and emit its
    `ParamEnc` product-encoding instance and its constructor-congruence `Related`
    instance. -/
def deriveParamCongrCore (declName : Name) : CommandElabM Unit := do
  let iv ← liftTermElabM <| getConstInfoInduct declName
  unless iv.ctors.length == 1 && iv.numIndices == 0 && !iv.isReflexive do
    throwError
      "derive_param_congr: '{declName}' must be a single-constructor, non-indexed, \
       non-reflexive structure"
  let ctorName := iv.ctors.head!
  let env ← getEnv
  let fieldShort := getStructureFields env declName
  let n := fieldShort.size
  if n == 0 then
    throwError "derive_param_congr: '{declName}' has no fields"
  -- Gather all type syntax (param binders, `T params`, per-field `Fᵢ` and `αᵢ`)
  -- in one `MetaM` pass over the constructor telescope.
  let (pBinders, tAppStx, fieldTys, fieldEncTys) ← liftTermElabM do
    let ci ← getConstInfoCtor ctorName
    forallTelescopeReducing ci.type fun xs _ => do
      let nP := ci.numParams
      let params := xs.extract 0 nP
      let fields := xs.extract nP xs.size
      let mut pbs : Array (TSyntax ``bracketedBinder) := #[]
      for p in params do
        let ld ← p.fvarId!.getDecl
        let tyStx ← delab (← inferType p)
        pbs := pbs.push ⟨(← `(bracketedBinderF| ($(mkIdent ld.userName) : $tyStx))).raw⟩
      let tAppExpr := mkAppN (mkConst declName (iv.levelParams.map mkLevelParam)) params
      let tAppStx ← delab tAppExpr
      let mut ftys : Array Term := #[]
      let mut fencs : Array Term := #[]
      for f in fields do
        ftys := ftys.push (← delab (← inferType f))
        let encApp ← mkAppM ``ParamEnc.enc #[f]
        fencs := fencs.push (← delab (← inferType encApp))
      return (pbs, tAppStx, ftys, fencs)
  -- Identifiers for the congruence binders.
  let aIds := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"a{i}")
  let bIds := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"b{i}")
  let hIds := (Array.range n).map fun i => mkIdent (Name.mkSimple s!"h{i}")
  let projIds := fieldShort.map mkIdent
  -- (a) The `ParamEnc` product-encoding instance.
  let encComponents ← (Array.range n).mapM fun i =>
    `(ParamEnc.enc x.$(projIds[i]!):ident)
  let encTuple ← mkTupleStx encComponents
  let prodTyStx ← mkProdTypeStx fieldEncTys
  let paramEncCmd ← `(command|
    instance $pBinders:bracketedBinder* : ParamEnc $tAppStx $prodTyStx where
      enc := fun x => $encTuple)
  elabCommand paramEncCmd
  -- (b) The constructor-congruence `Related` instance.
  let mut congrBinders := pBinders
  for i in [:n] do
    congrBinders := congrBinders.push
      ⟨(← `(bracketedBinderF| ($(aIds[i]!) : $(fieldTys[i]!)))).raw⟩
  for i in [:n] do
    congrBinders := congrBinders.push
      ⟨(← `(bracketedBinderF| ($(bIds[i]!) : $(fieldEncTys[i]!)))).raw⟩
  for i in [:n] do
    congrBinders := congrBinders.push
      ⟨(← `(bracketedBinderF| [$(hIds[i]!) : Related ParamEnc.enc $(aIds[i]!) $(bIds[i]!)])).raw⟩
  let bTerms : Array Term := bIds.map fun b => ⟨b.raw⟩
  let bTuple ← mkTupleStx bTerms
  -- The `rel` proof term: `congrArg₂ Prod.mk h₀.rel (congrArg₂ Prod.mk h₁.rel …)`,
  -- right-nested to match the product tuple. Its type
  -- `(ParamEnc.enc a₀, …) = (b₀, …)` is defeq to the required
  -- `ParamEnc.enc (T.mk a₀ …) = (b₀, …)` (the derived encoding reduces), so it
  -- type-checks directly as `rel` with no tactic.
  let relEqs ← hIds.mapM fun hi => `(($hi).rel)
  let mut proof := relEqs[n - 1]!
  for i in [0 : n - 1] do
    let j := n - 2 - i
    proof ← `(congrArg₂ Prod.mk $(relEqs[j]!) $proof)
  let congrCmd ← `(command|
    instance $congrBinders:bracketedBinder* :
        Related ParamEnc.enc ((⟨$aIds,*⟩ : $tAppStx)) $bTuple where
      rel := $proof)
  elabCommand congrCmd

/-! ## 3. Surfaces -/

/-- In-file command: `derive_param_congr T`. -/
syntax (name := deriveParamCongrCmd) "derive_param_congr " ident : command

@[command_elab deriveParamCongrCmd]
def elabDeriveParamCongr : CommandElab := fun stx => do
  match stx with
  | `(derive_param_congr $id:ident) => do
      let declName ← liftTermElabM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
      deriveParamCongrCore declName
  | _ => throwUnsupportedSyntax

open Lean.Elab.Deriving in
/-- The registered `deriving` handler (`deriving instance ParamCongr for T`).
    Single-constructor structures only; declines otherwise so another handler can
    take over. -/
def paramCongrDerivingHandler (declNames : Array Name) : CommandElabM Bool := do
  for declName in declNames do
    let .inductInfo iv ← liftTermElabM <| getConstInfo declName | return false
    if iv.ctors.length != 1 || iv.numIndices != 0 || iv.isReflexive then
      return false
    deriveParamCongrCore declName
  return true

initialize
  Lean.Elab.registerDerivingHandler ``ParamCongr paramCongrDerivingHandler

end Transfer.Deriving
