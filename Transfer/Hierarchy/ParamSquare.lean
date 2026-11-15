/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Hierarchy.ParamWeaken
public import Transfer.Combinators.ParamForall

/-!
# Squares of relations: the relation between relations

Given annotated relations `PA : Param m n A A'` and `PB : Param k l B B'`, two Prop-valued
relations `R : A → B → Prop` and `R' : A' → B' → Prop` form a square (`RelSq PA PB R R'`) when
they agree on `PA`- and `PB`-related arguments. This is the relation of the universe of
Prop-valued relations over the edges `PA` and `PB`, the second dimension of ParamTransfer: a
statement that mentions a relation transfers along a square of that relation.

The relation between relations is a `Param` on `A → B → Prop` and `A' → B' → Prop`. Its
forward map pulls a relation back along the backward maps of `PA` and `PB`, so the forward
level `t` of the square needs the backward level `relSqReq t` of `PA` and `PB`, and the
backward level `s` needs their forward level `relSqReq s` (`paramRelSqAt`). From `PA` and `PB`
at `(map3, map3)` the square is at `(map4, map4)` (`paramRelSq`).

Squares have two symmetries: transposition exchanges the roles of `PA` and `PB` and flips the
relations (`relSq_transpose_iff`, `SqOf.transpose`, an involution), and the converse exchanges
the two relations along the converse edges `PA.symm`, `PB.symm` (`relSq_symm_iff`,
`SqOf.converse`, an involution).

The level of a relation is invariant under a square whose edges are at `(map3, map3)`: a
relation has `MapHas t` exactly when the other one does (`mapHas_iff_of_relSq`).

## Main definitions

* `RelSq` — the square of two relations over `PA` and `PB`;
* `relSqReq` — the level table of the relation between relations;
* `relSqMap` — the transport of a relation along a pair of maps;
* `mapHasRelSq`, `paramRelSqAt`, `paramRelSq` — the relation between relations as a `Param` at
  every pair of levels, and at `(map4, map4)`;
* `SqOf`, `SqOf.transpose`, `SqOf.converse` — squares over `PA` and `PB` and their symmetries;
* `sqMapFun`, `mapHasOfRelSq` — the transport of a map, and of `MapHas t`, along a square.

## Main results

* `relSq_relSqMap`, `eq_relSqMap_of_relSq` — the two inclusions of the graph of `relSqMap`;
* `relSq_transpose_iff`, `SqOf.transpose_transpose` — transposition of squares;
* `relSq_symm_iff`, `SqOf.converse_converse` — the converse of a square;
* `mapHas_iff_of_relSq` — the level of a relation is invariant under squares at `(map3, map3)`.

## References

* T. Altenkirch, A. Kaposi, M. Shulman, E. Üsküplü, *From parametricity to identity types*,
  TYPES 2025;
* C. Cohen, E. Crance, A. Mahboubi, *Trocq: proof transfer for free, with or without univalence*,
  ESOP 2024.

Search words: square, relation between relations, bridge between bridges, two-dimensional
parametricity, symmetry, transposition, converse, universe of relations, Narya, level transfer.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A A' B B' : Type u}

/-- **Square of relations.** Two relations `R` and `R'` form a square over `PA` and `PB` when
they agree on related arguments. -/
def RelSq {m n k l : MapClass} (PA : Param m n A A') (PB : Param k l B B')
    (R : A → B → Prop) (R' : A' → B' → Prop) : Prop :=
  ∀ a a' b b', PA.R a a' → PB.R b b' → (R a b ↔ R' a' b')

/-- The level of each edge needed by the relation between relations at a level: a forward map
of relations uses the backward maps of the edges, and each inclusion of the graph uses the
other inclusion of the edges. -/
def relSqReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map1
  | .map2a => .map2b
  | .map2b => .map2a
  | .map3 => .map3
  | .map4 => .map3

/-- The transport of a relation along a pair of maps: the relation on the images. -/
def relSqMap (f : A' → A) (g : B' → B) (R : A → B → Prop) : A' → B' → Prop :=
  fun a' b' => R (f a') (g b')

section Graph

variable {m n k l : MapClass} {PA : Param m n A A'} {PB : Param k l B B'}

/-- A relation and its transport along maps that invert the edges form a square. -/
theorem relSq_relSqMap (hA : Map2bHas (symRel PA.R)) (hB : Map2bHas (symRel PB.R))
    (R : A → B → Prop) : RelSq PA PB R (relSqMap hA.map hB.map R) := by
  intro a a' b b' ha hb
  simp only [relSqMap, hA.R_in_map a' a ha, hB.R_in_map b' b hb]

/-- A square over edges whose maps land in the edges is the transport along those maps. -/
theorem eq_relSqMap_of_relSq (hA : Map2aHas (symRel PA.R)) (hB : Map2aHas (symRel PB.R))
    {R : A → B → Prop} {R' : A' → B' → Prop} (h : RelSq PA PB R R') :
    relSqMap hA.map hB.map R = R' := by
  funext a' b'
  exact propext (h _ a' _ b' (hA.map_in_R a' _ rfl) (hB.map_in_R b' _ rfl))

end Graph

/-- The relation between relations at every output level `t`, from edges whose backward
structure is at `relSqReq t`. -/
def mapHasRelSq {m k : MapClass} :
    (t : MapClass) → (PA : Param m (relSqReq t) A A') → (PB : Param k (relSqReq t) B B') →
      MapHas t (RelSq PA PB)
  | .map0, _, _ => (⟨⟩ : Map0Has _)
  | .map1, PA, PB =>
    (⟨relSqMap (PA.bwd : Map1Has _).map (PB.bwd : Map1Has _).map⟩ : Map1Has _)
  | .map2a, PA, PB =>
    let hA : Map2bHas (symRel PA.R) := PA.bwd
    let hB : Map2bHas (symRel PB.R) := PB.bwd
    (⟨relSqMap hA.map hB.map, fun R _ e => e ▸ relSq_relSqMap hA hB R⟩ : Map2aHas _)
  | .map2b, PA, PB =>
    let hA : Map2aHas (symRel PA.R) := PA.bwd
    let hB : Map2aHas (symRel PB.R) := PB.bwd
    (⟨relSqMap hA.map hB.map, fun _ _ h => eq_relSqMap_of_relSq hA hB h⟩ : Map2bHas _)
  | .map3, PA, PB =>
    let hA : Map3Has (symRel PA.R) := PA.bwd
    let hB : Map3Has (symRel PB.R) := PB.bwd
    (⟨relSqMap hA.map hB.map, fun R _ e => e ▸ relSq_relSqMap hA.toMap2b hB.toMap2b R,
      fun _ _ h => eq_relSqMap_of_relSq hA.toMap2a hB.toMap2a h⟩ : Map3Has _)
  | .map4, PA, PB =>
    let hA : Map3Has (symRel PA.R) := PA.bwd
    let hB : Map3Has (symRel PB.R) := PB.bwd
    (⟨relSqMap hA.map hB.map, fun R _ e => e ▸ relSq_relSqMap hA.toMap2b hB.toMap2b R,
      fun _ _ h => eq_relSqMap_of_relSq hA.toMap2a hB.toMap2a h, fun _ _ _ => rfl⟩ : Map4Has _)

/-- **Converse of a square.** Two relations form a square over `PA` and `PB` exactly when the
relations exchanged form a square over the converse edges. -/
theorem relSq_symm_iff {m n k l : MapClass} {PA : Param m n A A'} {PB : Param k l B B'}
    {R : A → B → Prop} {R' : A' → B' → Prop} :
    RelSq PA PB R R' ↔ RelSq PA.symm PB.symm R' R :=
  ⟨fun h a' a b' b ha hb => (h a a' b b' ha hb).symm,
    fun h a a' b b' ha hb => (h a' a b' b ha hb).symm⟩

/-- **The relation between relations** as a `Param` at every pair of levels `(t, s)`: the
edges at `(relSqReq s, relSqReq t)`. The backward direction is the forward rule at the converse
edges. -/
def paramRelSqAt (t s : MapClass) (PA : Param (relSqReq s) (relSqReq t) A A')
    (PB : Param (relSqReq s) (relSqReq t) B B') :
    Param t s (A → B → Prop) (A' → B' → Prop) where
  R := RelSq PA PB
  fwd := mapHasRelSq t PA PB
  bwd := MapHas.ofIff (fun _ _ => relSq_symm_iff.symm) s (mapHasRelSq s PA.symm PB.symm)

/-- The relation between relations at `(map4, map4)`, from edges at `(map3, map3)`. -/
def paramRelSq (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B') :
    Param .map4 .map4 (A → B → Prop) (A' → B' → Prop) :=
  paramRelSqAt .map4 .map4 PA PB

/-! ## Symmetries of squares -/

section Symmetry

variable {m n k l : MapClass}

/-- **Transposition of a square.** Two relations form a square over `PA` and `PB` exactly when
their flips form a square over `PB` and `PA`. -/
theorem relSq_transpose_iff {PA : Param m n A A'} {PB : Param k l B B'}
    {R : A → B → Prop} {R' : A' → B' → Prop} :
    RelSq PA PB R R' ↔ RelSq PB PA (flip R) (flip R') :=
  ⟨fun h b b' a a' hb ha => h a a' b b' ha hb, fun h a a' b b' ha hb => h b b' a a' hb ha⟩

/-- The squares over `PA` and `PB`: pairs of relations that form a square. -/
def SqOf (PA : Param m n A A') (PB : Param k l B B') : Type u :=
  {p : (A → B → Prop) × (A' → B' → Prop) // RelSq PA PB p.1 p.2}

/-- The transpose of a square. -/
def SqOf.transpose {PA : Param m n A A'} {PB : Param k l B B'} (s : SqOf PA PB) : SqOf PB PA :=
  ⟨(flip s.1.1, flip s.1.2), relSq_transpose_iff.1 s.2⟩

/-- Transposition is an involution. -/
@[simp] theorem SqOf.transpose_transpose {PA : Param m n A A'} {PB : Param k l B B'}
    (s : SqOf PA PB) : s.transpose.transpose = s :=
  rfl

/-- Transposition as a bijection of squares. -/
def SqOf.transposeEquiv (PA : Param m n A A') (PB : Param k l B B') : SqOf PA PB ≃ SqOf PB PA where
  toFun := SqOf.transpose
  invFun := SqOf.transpose
  left_inv := SqOf.transpose_transpose
  right_inv := SqOf.transpose_transpose

/-- The converse of a square, over the converse edges. -/
def SqOf.converse {PA : Param m n A A'} {PB : Param k l B B'} (s : SqOf PA PB) :
    SqOf PA.symm PB.symm :=
  ⟨(s.1.2, s.1.1), relSq_symm_iff.1 s.2⟩

/-- The converse is an involution. -/
@[simp] theorem SqOf.converse_converse {PA : Param m n A A'} {PB : Param k l B B'}
    (s : SqOf PA PB) : s.converse.converse = s :=
  rfl

end Symmetry

/-! ## Transfer of levels along a square -/

section LevelTransfer

variable {R : A → B → Prop} {R' : A' → B' → Prop}

/-- The transport of a map along edges at `(map3, map3)`: `PB`'s forward map after `f` after
`PA`'s backward map. -/
def sqMapFun (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B') (f : A → B) :
    A' → B' :=
  fun a' => (PB.fwd : Map3Has PB.R).map (f ((PA.bwd : Map3Has (symRel PA.R)).map a'))

/-- The transported map of a map whose graph lies in `R` has its graph in `R'`. -/
theorem sqMapFun_in_R (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B')
    (h : RelSq PA PB R R') (hR : Map2aHas R) (a' : A') (b' : B')
    (e : sqMapFun PA PB hR.map a' = b') : R' a' b' := by
  have hA : PA.R ((PA.bwd : Map3Has (symRel PA.R)).map a') a' :=
    (PA.bwd : Map3Has (symRel PA.R)).map_in_R a' _ rfl
  have hB : PB.R (hR.map ((PA.bwd : Map3Has (symRel PA.R)).map a')) b' :=
    (PB.fwd : Map3Has PB.R).map_in_R _ _ e
  exact (h _ _ _ _ hA hB).1 (hR.map_in_R _ _ rfl)

/-- A relation `R'` whose square partner `R` lies in the graph of a map lies in the graph of the
transported map. -/
theorem R_in_sqMapFun (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B')
    (h : RelSq PA PB R R') (hR : Map2bHas R) (a' : A') (b' : B') (r : R' a' b') :
    sqMapFun PA PB hR.map a' = b' := by
  have hA : PA.R ((PA.bwd : Map3Has (symRel PA.R)).map a') a' :=
    (PA.bwd : Map3Has (symRel PA.R)).map_in_R a' _ rfl
  have hB : PB.R ((PB.bwd : Map3Has (symRel PB.R)).map b') b' :=
    (PB.bwd : Map3Has (symRel PB.R)).map_in_R b' _ rfl
  have e := hR.R_in_map _ _ ((h _ _ _ _ hA hB).2 r)
  unfold sqMapFun
  rw [e]
  exact (PB.fwd : Map3Has PB.R).R_in_map _ _ hB

/-- The transport of `MapHas t` along a square whose edges are at `(map3, map3)`, with the map
`sqMapFun`. -/
def mapHasOfRelSq (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B')
    (h : RelSq PA PB R R') : (t : MapClass) → MapHas t R → MapHas t R'
  | .map0, _ => (⟨⟩ : Map0Has _)
  | .map1, hR => (⟨sqMapFun PA PB (hR : Map1Has R).map⟩ : Map1Has _)
  | .map2a, hR =>
    let hR : Map2aHas R := hR
    (⟨sqMapFun PA PB hR.map, sqMapFun_in_R PA PB h hR⟩ : Map2aHas _)
  | .map2b, hR =>
    let hR : Map2bHas R := hR
    (⟨sqMapFun PA PB hR.map, R_in_sqMapFun PA PB h hR⟩ : Map2bHas _)
  | .map3, hR =>
    let hR : Map3Has R := hR
    (⟨sqMapFun PA PB hR.map, sqMapFun_in_R PA PB h hR.toMap2a,
      R_in_sqMapFun PA PB h hR.toMap2b⟩ : Map3Has _)
  | .map4, hR =>
    let hR : Map4Has R := hR
    (⟨sqMapFun PA PB hR.map, sqMapFun_in_R PA PB h hR.toMap3.toMap2a,
      R_in_sqMapFun PA PB h hR.toMap3.toMap2b, fun _ _ _ => rfl⟩ : Map4Has _)

/-- **The level of a relation is invariant under squares.** Over edges at `(map3, map3)`, a
relation has structure at level `t` exactly when the other side of a square has. -/
theorem mapHas_iff_of_relSq (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B')
    (h : RelSq PA PB R R') (t : MapClass) : Nonempty (MapHas t R) ↔ Nonempty (MapHas t R') :=
  ⟨fun ⟨hR⟩ => ⟨mapHasOfRelSq PA PB h t hR⟩,
    fun ⟨hR'⟩ => ⟨mapHasOfRelSq PA.symm PB.symm (relSq_symm_iff.1 h) t hR'⟩⟩

end LevelTransfer

end Transfer.Param
