/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Hierarchy

/-!
# The `Param` relation hierarchy

A faithful Lean port of Trocq's level lattice (`rocq-community/trocq`,
`std/Hierarchy.v`) — the `std` (non-HoTT) variant, the appropriate one for
Lean+Mathlib.

`map_class := map0 | map1 | map2a | map2b | map3 | map4` records how much structure
a relation `R : A → B → Prop` carries in one direction:

| level | fields of `Map_k.Has R` |
|---|---|
| `map0`  | (none) |
| `map1`  | `map : A → B` |
| `map2a` | `map`, `map_in_R : map a = b → R a b` |
| `map2b` | `map`, `R_in_map : R a b → map a = b` |
| `map3`  | `map`, `map_in_R`, `R_in_map` |
| `map4`  | `map3` + coherence `R_in_mapK` (automatic here by proof irrelevance) |

A `Param m n A B` packages a relation `R` with a `Map_m.Has R` (forward) and a
`Map_n.Has (sym R)` (backward) — Trocq's annotated relation `(m,n)`.

## Prop-valued relations and funext

The relations are `R : A → B → Prop` (the equation-style relations the crypto
transfer uses); the `Type`-valued generalization (needed for the universe /
dependent-`Type` motive) is noted where it applies. Lean has `funext` as a
theorem, so the combinators Coq's `std` had to gate on `` `{Funext} ``
(map2b/map3 arrow/forall) are axiom-free here — only the map4 universe relation
needs univalence. The univalence-free fragment is thus map0–map3 in every
component, wider than the paper's `{0,1,2a}`. With `Prop`-valued `R`, proof
irrelevance makes the map4 coherence `R_in_mapK` automatic, so even `Map4.Has`
is constructible for these relations.
-/

set_option autoImplicit false
-- `Param` (the annotated-relation structure) deliberately lives in the `Param`
-- namespace that groups the whole engine, giving `…Trocq.Param.Param`. Intentional.
set_option linter.dupNamespace false

universe u

namespace Transfer.Param

/-! ## The level lattice -/

/-- Trocq's `map_class` (`std/Hierarchy.v`): the six structure levels a relation
    can carry in one direction. -/
inductive MapClass | map0 | map1 | map2a | map2b | map3 | map4
  deriving DecidableEq, Repr

/-! ## The `Map_k.Has R` records (ported from `std/Hierarchy.v`) -/

/-- `map0`: no structure. -/
structure Map0Has {A B : Type u} (R : A → B → Prop) : Type u where

/-- `map1`: a forward map. -/
structure Map1Has {A B : Type u} (R : A → B → Prop) : Type u where
  map : A → B

/-- `map2a`: a map whose graph is included in `R`. -/
structure Map2aHas {A B : Type u} (R : A → B → Prop) : Type u where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b

/-- `map2b`: a map that includes `R` (so `R` is single-valued through `map`). -/
structure Map2bHas {A B : Type u} (R : A → B → Prop) : Type u where
  map : A → B
  R_in_map : ∀ a b, R a b → map a = b

/-- `map3`: `R` is exactly the graph of `map` (both inclusions). -/
structure Map3Has {A B : Type u} (R : A → B → Prop) : Type u where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b

/-- `map4`: `map3` + the coherence `R_in_mapK`. For `Prop`-valued `R` the
    coherence is automatic (proof irrelevance), so this is `map3` + a free field —
    a faithful placeholder for the univalent level (which over `Type`-valued `R`
    is the equivalence-coherence requiring univalence). -/
structure Map4Has {A B : Type u} (R : A → B → Prop) : Type u where
  map : A → B
  map_in_R : ∀ a b, map a = b → R a b
  R_in_map : ∀ a b, R a b → map a = b
  R_in_mapK : ∀ a b (r : R a b), map_in_R a b (R_in_map a b r) = r

/-- The `Map_k.Has` record type indexed by the level. -/
def MapHas {A B : Type u} : MapClass → (A → B → Prop) → Type u
  | .map0,  R => Map0Has R
  | .map1,  R => Map1Has R
  | .map2a, R => Map2aHas R
  | .map2b, R => Map2bHas R
  | .map3,  R => Map3Has R
  | .map4,  R => Map4Has R

/-! ## The annotated relation `Param (m,n)` -/

/-- The flipped relation. -/
abbrev symRel {A B : Type u} (R : A → B → Prop) : B → A → Prop := fun b a => R a b

/-- `Param m n A B`: a relation `R` with forward structure `Map_m.Has R` and
    backward structure `Map_n.Has (sym R)` — Trocq's annotated relation. -/
structure Param (m n : MapClass) (A B : Type u) where
  R : A → B → Prop
  fwd : MapHas m R
  bwd : MapHas n (symRel R)

/-- Symmetry (the data is symmetric): swap directions. -/
def Param.symm {m n : MapClass} {A B : Type u} (p : Param m n A B) :
    Param n m B A where
  R := symRel p.R
  fwd := p.bwd
  bwd := p.fwd

/-! ## Weakening (the lattice order): forget structure -/

/-- `map1 → map0`. -/
def Map1Has.forget {A B : Type u} {R : A → B → Prop} (_ : Map1Has R) : Map0Has R := ⟨⟩
/-- `map2a → map1`. -/
def Map2aHas.toMap1 {A B : Type u} {R : A → B → Prop} (h : Map2aHas R) : Map1Has R := ⟨h.map⟩
/-- `map2b → map1`. -/
def Map2bHas.toMap1 {A B : Type u} {R : A → B → Prop} (h : Map2bHas R) : Map1Has R := ⟨h.map⟩
/-- `map3 → map2a`. -/
def Map3Has.toMap2a {A B : Type u} {R : A → B → Prop} (h : Map3Has R) : Map2aHas R :=
  ⟨h.map, h.map_in_R⟩
/-- `map3 → map2b`. -/
def Map3Has.toMap2b {A B : Type u} {R : A → B → Prop} (h : Map3Has R) : Map2bHas R :=
  ⟨h.map, h.R_in_map⟩
/-- `map4 → map3`. -/
def Map4Has.toMap3 {A B : Type u} {R : A → B → Prop} (h : Map4Has R) : Map3Has R :=
  ⟨h.map, h.map_in_R, h.R_in_map⟩

/-! ## Bridge: `ReprEmbeddingClass` is a `Param`

The encoding `enc : A → α` with its graph `R a b := enc a = b` is forward-`map3`
(the graph makes both inclusions identities); without a decoder the backward
direction is `map0`. So an embedding is a `Param map3 map0`. -/

open Transfer in
/-- An embedding `A ↪ α` (graph of `enc`) as a forward-`map3`, backward-`map0`
    annotated relation. -/
def paramOfEmbedding {A α : Type u} [ReprEmbeddingClass A α] : Param .map3 .map0 A α where
  R := fun a b => (ReprMapClass.enc a : α) = b
  fwd := ⟨ReprMapClass.enc, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨⟩

open Transfer in
/-- A bare representation map as a forward-`map1`, backward-`map0` relation. -/
def paramOfMap {A α : Type u} [ReprMapClass A α] : Param .map1 .map0 A α where
  R := fun a b => (ReprMapClass.enc a : α) = b
  fwd := ⟨ReprMapClass.enc⟩
  bwd := ⟨⟩

end Transfer.Param
