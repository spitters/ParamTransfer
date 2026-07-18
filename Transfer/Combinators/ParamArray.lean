/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Combinators.ParamData

/-!
# The `Array` container rule and relational `foldl` transfer

`ParamData.lean` lifts `Param` through `×`/`Option`/`List`. This module adds the
**`Array`** container — the carrier `leanprover/hex`'s computational cores use for
O(1) dense access — and, crucially, the **relational `foldl` transfer** that makes
`Array`- (or `List`-) *carried folds* transfer generically.

## Why this is the recursion story

`ParamTransfer`'s term-level `⟦·⟧` stops at recursors, so a recursive algorithm is
not translated inline. CoqEAL's answer — and this module's — is that recursion is
factored through a small set of *combinators*, each transferred once. `foldlR`
is that lemma for the fold combinator: given a step that respects the element and
accumulator relations, a fold over related containers yields related results, at
*heterogeneous* element **and** accumulator types (the general parametricity of
`foldl`, not the encoding-only `HigherOrderTransfer.foldl_transfer`). Every
structural/bounded algorithm expressed as a fold — `HexBareiss`, `HexRowReduce`,
`HexGramSchmidt`, `HexDeterminant` — inherits transfer from this one lemma, without
touching the recursor frontier. `forIn`/`do`-loops desugar to a fold and ride it
too; the monadic case is `Integrations/ParamTripleTransfer`'s `RComp`.

## What is ported

* `R_array PA` — the pointwise lift to arrays, `List.Forall₂ PA.R` on `toList`
  (reusing the `R_list` machinery), with the `map0`/`map1`/`map2a` forward records
  and `paramArray : Param .map1 .map0 (Array A) (Array A')`, mirroring `paramList`.
* `foldlR_list` / `foldlR_array` — the relational fold transfer. The `Array`
  version reduces to the `List` version through `Array.foldl_toList`.
-/

set_option autoImplicit false

universe u v

namespace Transfer.Param

variable {A A' : Type u}

/-! ## The `Array` relation `R_array` (via `R_list` on `toList`) -/

/-- `R_array`: two arrays are related when their underlying lists are pointwise
    related by the element relation. Reuses `List.Forall₂`, exactly as `R_list`
    does — the `Array` rule is the `List` rule read through `Array.toList`. -/
def R_array {mA nA : MapClass} (PA : Param mA nA A A') : Array A → Array A' → Prop :=
  fun a a' => List.Forall₂ PA.R a.toList a'.toList

/-- `Map0_array`: no structure. -/
def Map0_array {mA nA : MapClass} (PA : Param mA nA A A') : Map0Has (R_array PA) := ⟨⟩

/-- `Map1_array`: lift the element forward map through `Array.map`. -/
def Map1_array (PA : Param .map1 .map0 A A') : Map1Has (R_array PA) :=
  ⟨Array.map PA.fwd.map⟩

/-- `Map2a_array`: the lifted map's graph is included in `R_array`, reducing to
    the `List` graph-inclusion (`Map2a_list`) through `Array.toList_map`. -/
def Map2a_array (PA : Param .map2a .map0 A A') : Map2aHas (R_array PA) where
  map := Array.map PA.fwd.map
  map_in_R := by
    intro a a' e; subst e
    show List.Forall₂ PA.R a.toList (Array.map PA.fwd.map a).toList
    rw [Array.toList_map]
    exact (Map2a_list PA).map_in_R a.toList (a.toList.map PA.fwd.map) rfl

/-- `paramArray`: from an element relation at forward-`map2a`, backward-`map0`,
    the annotated relation on `Array`, forward-`map1`, backward-`map0`. The
    `Array` analogue of `paramList`. -/
def paramArray (PA : Param .map2a .map0 A A') :
    Param .map1 .map0 (Array A) (Array A') where
  R := R_array PA
  fwd := ⟨Array.map PA.fwd.map⟩
  bwd := ⟨⟩

/-! ## Relational `foldl` transfer — the combinator lemma

The parametricity of `foldl` at heterogeneous element (`A`/`A'`) and accumulator
(`β`/`β'`) types: a step respecting both relations sends related seeds and related
containers to related results. This is the atom every fold-shaped algorithm
transfers through. -/

/-- **Relational `List.foldl` transfer.** If the step `f`/`f'` maps
    `Rβ`-related accumulators and `PA`-related elements to `Rβ`-related
    accumulators, then folding over `List.Forall₂ PA`-related lists from
    `Rβ`-related seeds yields `Rβ`-related results. The general parametricity of
    `foldl` (heterogeneous carriers), by induction on the `Forall₂` derivation
    with the accumulators generalized. -/
theorem foldlR_list {β : Type v} {β' : Type v} (PA : A → A' → Prop) (Rβ : β → β' → Prop)
    (f : β → A → β) (f' : β' → A' → β')
    (hf : ∀ s s' x x', Rβ s s' → PA x x' → Rβ (f s x) (f' s' x'))
    {s : β} {s' : β'} (hs : Rβ s s') {l : List A} {l' : List A'}
    (hl : List.Forall₂ PA l l') :
    Rβ (l.foldl f s) (l'.foldl f' s') := by
  induction hl generalizing s s' with
  | nil => exact hs
  | cons hx _ ih => exact ih (hf _ _ _ _ hs hx)

/-- **Relational `Array.foldl` transfer.** The `Array` combinator lemma, reduced
    to `foldlR_list` through `Array.foldl_toList`. A fold over `R_array`-related
    arrays from related seeds yields related results — so any `Array`-carried
    fold of a step that respects the refinement transfers, no recursion
    translation needed. -/
theorem foldlR_array {β : Type v} {β' : Type v} {mA nA : MapClass}
    (PA : Param mA nA A A') (Rβ : β → β' → Prop)
    (f : β → A → β) (f' : β' → A' → β')
    (hf : ∀ s s' x x', Rβ s s' → PA.R x x' → Rβ (f s x) (f' s' x'))
    {s : β} {s' : β'} (hs : Rβ s s') {a : Array A} {a' : Array A'}
    (ha : R_array PA a a') :
    Rβ (a.foldl f s) (a'.foldl f' s') := by
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  exact foldlR_list PA.R Rβ f f' hf hs ha

/-! ## Demos -/

/-- The diagonal element input for the `Array` rule (forward-`map2a`,
    backward-`map0`), the shape `paramArray` consumes. -/
def paramEqEltArray (T : Type u) : Param .map2a .map0 T T where
  R := Eq
  fwd := ⟨id, fun _ _ h => h⟩
  bwd := ⟨⟩

/-- `R_array` of the diagonal is `List.Forall₂ Eq` on the underlying lists. -/
example {T : Type u} (a a' : Array T) :
    R_array (paramEqEltArray T) a a' ↔ List.Forall₂ Eq a.toList a'.toList := Iff.rfl

/-- The array forward map is `Array.map` of the element map. -/
example {T : Type u} (a : Array T) :
    (paramArray (paramEqEltArray T)).fwd.map a = a.map id := rfl

/-- **A fold transfers generically.** Summing two `R_array`-related arrays gives
    equal results, obtained from `foldlR_array` alone (`Rβ := Eq`, element
    relation `Eq`, the additive step respects equality). This is the miniature of
    "structural/fold-shaped algorithms transfer through one combinator lemma". -/
example (a a' : Array Nat) (h : R_array (paramEqEltArray Nat) a a') :
    a.foldl (· + ·) 0 = a'.foldl (· + ·) 0 :=
  foldlR_array (paramEqEltArray Nat) Eq (· + ·) (· + ·)
    (fun _ _ _ _ hs hx => by subst hs; subst hx; rfl) rfl h

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.paramArray' depends on axioms: [propext] -/
#guard_msgs in
#print axioms paramArray

/-- info: 'Transfer.Param.foldlR_array' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms foldlR_array

end AxiomAudit

end Transfer.Param
