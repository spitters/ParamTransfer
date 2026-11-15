/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Hierarchy.ParamWeaken
public import Transfer.Synthesis.ParamSynth

/-!
# Level rules of the dependent pair, the unit type, equality and the universe

The rules of this file give the parametricity annotations of Trocq (Cohen, Crance, Mahboubi,
*Trocq: proof transfer for free, with or without univalence*, ESOP 2024) at the levels that the
reflexive-graph model of type theory assigns to the type formers. In that model a type is a
family of sets with relations over the edges of its context, and a level `k` of an edge is the
truncation of the fibrancy record of Altenkirch, Kaposi, Shulman and Üsküplü
(*From parametricity to identity types*, TYPES 2025) read in one direction: `map1` is transport,
`map2a` transport with the lift of its argument, `map2b` transport with uniqueness of related
elements, `map3` both, and `map4` is `map3` on the propositional relations used here.

The dependent pair is fibrant at level `t` when its base is fibrant at `sigmaBaseReq t` and its
fibres at `sigmaFiberReq t`:

| output `t` | base | fibres |
|---|---|---|
| `map0` | `map0` | `map0` |
| `map1` | `map2a` | `map1` |
| `map2a` | `map2a` | `map2a` |
| `map2b` | `map3` | `map2b` |
| `map3` | `map3` | `map3` |
| `map4` | `map3` | `map3` |

The base must reach `map2a` as soon as `t` is at least `map1`, because the fibre relation is
indexed by the witness that relates the transported base to its argument. At output `map1` the
fibres need only `map1`; `paramSigma` of `ParamSigma.lean` asks for `map2a` there. The unit type
and the identity relation of a type are fibrant at `map4` in both directions. The universe
relation `univRel m n` relates two small types joined by an annotated relation `Param m n`; it
carries `map2a` in both directions, by the identity relation.

## Main definitions

* `sigmaBaseReq`, `sigmaFiberReq` — the level table of the dependent pair;
* `sigmaRel`, `sigmaFwd` — the relation and the forward map of a dependent pair;
* `mapHasSigma` — the dependent pair at every output level, on relations;
* `paramSigmaAt`, `paramSigmaLe`, `paramSigmaMap1` — the dependent-pair `Param` at every pair of
  levels, from inputs at the table's levels or above;
* `paramUnitTop`, `paramEqTop`, `paramEqAt` — the unit type and the identity relation at
  `(map4, map4)` and below;
* `univRel`, `paramUniv` — the universe relation and its `Param` on `Type u`.

## Main results

* `sigmaFwd_in_R`, `R_in_sigmaFwd` — the two inclusions of the graph of `sigmaFwd`;
* `univRel_of_mapHas` — a relation with `MapHas m` and `MapHas n` of its converse relates its two
  types in the universe relation at `(m, n)`;
* `univRel_iff`, `univRel_refl`, `univRel_symm` — the universe relation as the existence of such
  a relation, its reflexivity and its symmetry.

## Instances

`HasParam` instances register the rules for the synthesizer of `ParamSynth.lean` and the first
strategy of `param_resolve`: `sigmaHasParam` at every pair of levels, `unitHasParam` and, at low
priority, `eqHasParam` at every pair of levels.

## References

* C. Cohen, E. Crance, A. Mahboubi, *Trocq: proof transfer for free, with or without
  univalence*, ESOP 2024.
* T. Altenkirch, A. Kaposi, M. Shulman, E. Üsküplü, *From parametricity to identity types*,
  TYPES 2025.

Search words: dependent sum, Sigma, level table, reflexive graph, fibrancy, truncated fibrancy,
unit, identity relation, universe relation, univalence-free.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param

/-! ## The level table of the dependent pair -/

/-- The base requirement of the dependent pair at an output level: the level of the base relation
that a dependent pair at level `t` needs. -/
def sigmaBaseReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map2a
  | .map2a => .map2a
  | .map2b => .map3
  | .map3 => .map3
  | .map4 => .map3

/-- The fiber requirement of the dependent pair at an output level: the level of the fiber
relations that a dependent pair at level `t` needs. -/
def sigmaFiberReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map1
  | .map2a => .map2a
  | .map2b => .map2b
  | .map3 => .map3
  | .map4 => .map3

/-- The dependent pair asks for at most `map3` of its base at every output level. -/
theorem sigmaBaseReq_le_map3 (t : MapClass) : sigmaBaseReq t ⊑ .map3 := by
  cases t <;> rfl

/-- The dependent pair asks for no more of its fibers than the output level. -/
theorem sigmaFiberReq_le (t : MapClass) : sigmaFiberReq t ⊑ t := by
  cases t <;> rfl

/-! ## The relation and the map of a dependent pair -/

section Sigma

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u}

/-- The relation of a dependent pair: related bases, and fibers related at that witness. It is
`R_sigma` of `ParamSigma.lean` with the fiber relation given as a relation, so that it does not
fix the level of the fiber. -/
def sigmaRel (SR : A → A' → Prop) (FR : ∀ a a', SR a a' → B a → B' a' → Prop) :
    (Σ a, B a) → (Σ a', B' a') → Prop :=
  fun p q => ∃ h : SR p.1 q.1, FR p.1 q.1 h p.2 q.2

variable {SR : A → A' → Prop} {FR : ∀ a a', SR a a' → B a → B' a' → Prop}

/-- The map of a dependent pair: the base map, and the fiber map at the witness of the base. -/
def sigmaFwd (smap : A → A') (wit : ∀ a, SR a (smap a))
    (fmap : ∀ a a', SR a a' → B a → B' a') : (Σ a, B a) → (Σ a', B' a') :=
  fun p => ⟨smap p.1, fmap p.1 (smap p.1) (wit p.1) p.2⟩

/-- The graph of `sigmaFwd` is included in the relation when the graphs of the fiber maps are
included in theirs. -/
theorem sigmaFwd_in_R (smap : A → A') (wit : ∀ a, SR a (smap a))
    (fmap : ∀ a a', SR a a' → B a → B' a')
    (hF : ∀ a a' h x, FR a a' h x (fmap a a' h x)) (p : Σ a, B a) (q : Σ a', B' a')
    (e : sigmaFwd smap wit fmap p = q) : sigmaRel SR FR p q := by
  subst e
  exact ⟨wit p.1, hF _ _ _ _⟩

/-- The relation is included in the graph of `sigmaFwd` when the base map and the fiber maps
include their relations. -/
theorem R_in_sigmaFwd (smap : A → A') (wit : ∀ a, SR a (smap a))
    (fmap : ∀ a a', SR a a' → B a → B' a') (hS : ∀ a a', SR a a' → smap a = a')
    (hF : ∀ a a' h x y, FR a a' h x y → fmap a a' h x = y) (p : Σ a, B a) (q : Σ a', B' a')
    (r : sigmaRel SR FR p q) : sigmaFwd smap wit fmap p = q := by
  obtain ⟨a, x⟩ := p
  obtain ⟨b, y⟩ := q
  obtain ⟨h, r⟩ := r
  obtain rfl := hS a b h
  exact congrArg (Sigma.mk _) (hF _ _ _ _ _ r)

/-- The dependent pair at every output level `t`, from the base at `sigmaBaseReq t` and the
fibers at `sigmaFiberReq t`. These are the levels of the dependent sum in the reflexive-graph
model. -/
def mapHasSigma : (t : MapClass) → MapHas (sigmaBaseReq t) SR →
    (∀ a a' h, MapHas (sigmaFiberReq t) (FR a a' h)) → MapHas t (sigmaRel SR FR)
  | .map0, _, _ => (⟨⟩ : Map0Has _)
  | .map1, hS, hF =>
    let hS : Map2aHas SR := hS
    let hF : ∀ a a' h, Map1Has (FR a a' h) := hF
    (⟨sigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map⟩ : Map1Has _)
  | .map2a, hS, hF =>
    let hS : Map2aHas SR := hS
    let hF : ∀ a a' h, Map2aHas (FR a a' h) := hF
    (⟨sigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map,
      sigmaFwd_in_R _ _ _ fun a a' h x => (hF a a' h).map_in_R x _ rfl⟩ : Map2aHas _)
  | .map2b, hS, hF =>
    let hS : Map3Has SR := hS
    let hF : ∀ a a' h, Map2bHas (FR a a' h) := hF
    (⟨sigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map,
      R_in_sigmaFwd _ _ _ hS.R_in_map fun a a' h => (hF a a' h).R_in_map⟩ : Map2bHas _)
  | .map3, hS, hF =>
    let hS : Map3Has SR := hS
    let hF : ∀ a a' h, Map3Has (FR a a' h) := hF
    (⟨sigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map,
      sigmaFwd_in_R _ _ _ fun a a' h x => (hF a a' h).map_in_R x _ rfl,
      R_in_sigmaFwd _ _ _ hS.R_in_map fun a a' h => (hF a a' h).R_in_map⟩ : Map3Has _)
  | .map4, hS, hF =>
    let hS : Map3Has SR := hS
    let hF : ∀ a a' h, Map3Has (FR a a' h) := hF
    (⟨sigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map,
      sigmaFwd_in_R _ _ _ fun a a' h x => (hF a a' h).map_in_R x _ rfl,
      R_in_sigmaFwd _ _ _ hS.R_in_map fun a a' h => (hF a a' h).R_in_map,
      fun _ _ _ => rfl⟩ : Map4Has _)

end Sigma

/-! ## The dependent-pair `Param` at every pair of levels -/

section SigmaParam

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u}

/-- The dependent-pair `Param` at every pair of output levels `(t, s)`: the base at
`(sigmaBaseReq t, sigmaBaseReq s)` and the fibers at `(sigmaFiberReq t, sigmaFiberReq s)`. The
backward direction is `mapHasSigma` applied to the converse base relation and the converse
fibers. -/
def paramSigmaAt (t s : MapClass)
    (PA : Param (sigmaBaseReq t) (sigmaBaseReq s) A A')
    (PB : ∀ a a', PA.R a a' → Param (sigmaFiberReq t) (sigmaFiberReq s) (B a) (B' a')) :
    Param t s (Σ a, B a) (Σ a', B' a') where
  R := sigmaRel PA.R fun a a' h => (PB a a' h).R
  fwd := mapHasSigma t PA.fwd fun a a' h => (PB a a' h).fwd
  bwd := mapHasSigma (B := B') (B' := B) (SR := symRel PA.R)
    (FR := fun a' a h => symRel (PB a a' h).R) s PA.bwd fun a' a h => (PB a a' h).bwd

/-- The dependent-pair `Param` at levels `(t, s)` from a base and fibers at any levels at or above
the requirements of the table. -/
def paramSigmaLe {m n k l : MapClass} (PA : Param m n A A')
    (PB : ∀ a a', PA.R a a' → Param k l (B a) (B' a')) (t s : MapClass)
    (ht : sigmaBaseReq t ⊑ m) (hs : sigmaBaseReq s ⊑ n) (hk : sigmaFiberReq t ⊑ k)
    (hl : sigmaFiberReq s ⊑ l) : Param t s (Σ a, B a) (Σ a', B' a') :=
  paramSigmaAt t s (PA.weaken ht hs) fun a a' h => (PB a a' h).weaken hk hl

/-- The dependent pair at `(map1, map0)` with fibers at `map1`: the level of `paramSigma` with
the fiber requirement of the table. -/
def paramSigmaMap1 {nA : MapClass} (PA : Param .map2a nA A A')
    (PB : ∀ a a', PA.R a a' → Param .map1 .map0 (B a) (B' a')) :
    Param .map1 .map0 (Σ a, B a) (Σ a', B' a') :=
  paramSigmaAt .map1 .map0 (PA.weaken (MapClass.le_refl _) (by cases nA <;> rfl)) PB

end SigmaParam

/-! ## The unit type and the identity relation -/

/-- The unit type at `(map4, map4)`, with the total relation. -/
def paramUnitTop : Param .map4 .map4 PUnit.{u + 1} PUnit.{u + 1} where
  R := fun _ _ => True
  fwd := (⟨fun _ => PUnit.unit, fun _ _ _ => trivial, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ :
    Map4Has _)
  bwd := (⟨fun _ => PUnit.unit, fun _ _ _ => trivial, fun _ _ _ => rfl, fun _ _ _ => rfl⟩ :
    Map4Has _)

/-- The identity relation of a type at `(map4, map4)`, with the identity maps. -/
def paramEqTop (T : Type u) : Param .map4 .map4 T T where
  R := Eq
  fwd := (⟨id, fun _ _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩ : Map4Has _)
  bwd := (⟨id, fun _ _ h => h.symm, fun _ _ h => h.symm, fun _ _ _ => rfl⟩ : Map4Has _)

/-- Every level is below `map4`. -/
theorem MapClass.le_map4 (m : MapClass) : m ⊑ .map4 := by
  cases m <;> rfl

/-- The identity relation of a type at every pair of levels. -/
def paramEqAt (m n : MapClass) (T : Type u) : Param m n T T :=
  (paramEqTop T).weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

/-! ## The universe relation -/

/-- The universe relation at annotation `(m, n)`: two small types are related when an annotated
relation `Param m n` joins them. -/
def univRel (m n : MapClass) (A B : Type u) : Prop :=
  Nonempty (Param m n A B)

/-- A relation between small types with `MapHas m` and `MapHas n` of its converse relates the two
types in the universe relation at `(m, n)`. -/
theorem univRel_of_mapHas {m n : MapClass} {A B : Type u} (R : A → B → Prop) (hf : MapHas m R)
    (hb : MapHas n (symRel R)) : univRel m n A B :=
  ⟨⟨R, hf, hb⟩⟩

/-- The universe relation at `(m, n)` is the existence of a relation with `MapHas m` and
`MapHas n` of its converse. -/
theorem univRel_iff {m n : MapClass} {A B : Type u} :
    univRel m n A B ↔
      ∃ R : A → B → Prop, Nonempty (MapHas m R) ∧ Nonempty (MapHas n (symRel R)) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.R, ⟨P.fwd⟩, ⟨P.bwd⟩⟩
  · rintro ⟨R, ⟨hf⟩, ⟨hb⟩⟩
    exact univRel_of_mapHas R hf hb

/-- The universe relation is reflexive, by the identity relation. -/
theorem univRel_refl (m n : MapClass) (A : Type u) : univRel m n A A :=
  ⟨paramEqAt m n A⟩

/-- The universe relation at `(m, n)` read backward is the universe relation at `(n, m)`. -/
theorem univRel_symm {m n : MapClass} {A B : Type u} (h : univRel m n A B) : univRel n m B A :=
  h.elim fun P => ⟨P.symm⟩

/-- The universe `Type u` related to itself by the universe relation at `(m, n)`, at
`(map2a, map2a)`: the maps are the identity, and the identity relation of each small type lifts
them. -/
def paramUniv (m n : MapClass) : Param .map2a .map2a (Type u) (Type u) where
  R := univRel m n
  fwd := ⟨id, fun A _ h => h ▸ univRel_refl m n A⟩
  bwd := ⟨id, fun B _ h => h ▸ univRel_refl m n B⟩

/-! ## Registration for the synthesizer -/

section Instances

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u}

/-- The dependent-pair rule as an instance at every pair of levels: the base at the levels
`sigmaBaseReq` gives and the fibers at the levels `sigmaFiberReq` gives. Instance resolution
cannot introduce the witness of the base relation, so the fiber instances do not depend on it;
`paramSigmaAt` takes fibers that do. -/
instance sigmaHasParam (t s : MapClass) [hA : HasParam (sigmaBaseReq t) (sigmaBaseReq s) A A']
    [hB : ∀ a a', HasParam (sigmaFiberReq t) (sigmaFiberReq s) (B a) (B' a')] :
    HasParam t s (Σ a, B a) (Σ a', B' a') where
  param := paramSigmaAt t s hA.param fun a a' _ => (hB a a').param

/-- The unit type as an instance at every pair of levels. -/
instance unitHasParam (m n : MapClass) : HasParam m n PUnit.{u + 1} PUnit.{u + 1} where
  param := paramUnitTop.weaken (MapClass.le_map4 m) (MapClass.le_map4 n)

/-- The identity relation as an instance at every pair of levels, at low priority, so that a
registered relation on a type is found first. -/
instance (priority := low) eqHasParam (m n : MapClass) (T : Type u) : HasParam m n T T where
  param := paramEqAt m n T

/-- The synthesizer finds the dependent pair over `Nat` with fibers `Fin (n + 1)` at
`(map4, map4)`. -/
example : HasParam .map4 .map4 (Σ n : Nat, Fin (n + 1)) (Σ n : Nat, Fin (n + 1)) :=
  inferInstance

/-- The synthesizer finds the dependent pair over the unit type at `(map2b, map1)`. -/
example : HasParam .map2b .map1 (Σ _ : PUnit.{1}, Bool) (Σ _ : PUnit.{1}, Bool) :=
  inferInstance

end Instances

end Transfer.Param
