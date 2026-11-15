/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Transfer.Hierarchy.ParamWeaken
public import Transfer.Combinators.ParamForall
public import Transfer.Combinators.ParamLevelsModel

/-!
# The `Param` hierarchy over proof-relevant relations

The relations of `ParamHierarchy.lean` are propositions, so the coherence `R_in_mapK` of `map4`
holds by proof irrelevance. This file defines the same hierarchy over relations
`R : A → B → Type u`, whose witnesses are data, after the `std` hierarchy of Trocq (Cohen,
Crance, Mahboubi). There the coherence is a condition: a relation at `map3` is at `map4` exactly
when its witness types are subsingletons (`tmap4Equiv`). A relation at `map4` in both directions
is a one-to-one correspondence, and one-to-one correspondences are the equivalences of types
(`TParam.toEquiv`, `TParam.ofEquiv`), the set-level form of univalent parametricity.

Truncation `Nonempty` of the witness types sends `TParam m n` to ParamTransfer's `Param m n` at
every pair of levels, and `ULift (PLift ·)` embeds `Param m n` into `TParam m n`; truncation after
embedding is the identity (`Param.toTParam_trunc`).

The function type, the dependent product and the dependent sum are closed under `TParam` at the
following tables, for an output level `t` of one direction:

| output `t` | arrow domain | arrow codomain | Π domain | Σ base | Π, Σ fibres |
|---|---|---|---|---|---|
| `map0` | `map0` | `map0` | `map0` | `map0` | `map0` |
| `map1` | `map1` | `map1` | `map2a` | `map2a` | `map1` |
| `map2a` | `map2b` | `map2a` | `map4` | `map2a` | `map2a` |
| `map2b` | `map2a` | `map2b` | `map2a` | `map4` | `map2b` |
| `map3` | `map3` | `map3` | `map4` | `map4` | `map3` |
| `map4` | `map3` | `map4` | `map4` | `map4` | `map4` |

The arrow and Π domains are read backward. The tables agree with those of `arrowReq`,
`forallReq` and `sigmaBaseReq` except at the entries that the propositional rules close by proof
irrelevance: the output `map4` asks for subsingleton witness types of the codomain and fibres, and
the Π domain at `map2a`, `map3` and the Σ base at `map2b`, `map3` ask for `map4`, because the
fibre relation is indexed by a witness that the coherence identifies with the witness of the
transported element. Each entry is at or above the propositional one (`tForallDomReq_ge`,
`tSigmaBaseReq_ge`).

The fibrancy record of Altenkirch, Kaposi, Shulman and Üsküplü has the fields `trr`, `trl`,
`liftr`, `liftl` and the coinductive field `id`, the fibrancy of every witness type. `TFibN n R`
is its depth-`n` truncation, defined by recursion on `n`, where the witness type `R a b` carries
its identity relation `eqRel`. `TFibN 1 R` is `map2a` in both directions (`tfibNOneEquiv`). The
witness types of Lean are sets, so the fibrancy of an identity relation is contractible
(`tfibN_eqRel_subsingleton`), and `TFibN (n + 1) R` is equivalent to `TFibN 1 R` for every `n`
(`tfibNSuccEquiv`); in particular `TFibN (n + 2) R` is equivalent to `TFibN 2 R`.

## Main definitions

* `TMap0Has` … `TMap4Has`, `TMapHas` — the structure of a level on a Type-valued relation;
* `TParam`, `TParam.symm`, `TParam.weaken` — the annotated relation, its converse, weakening;
* `TMap4Has.ofMap3`, `tmap4Equiv` — `map4` as `map3` with subsingleton witness types;
* `TParam.toEquiv`, `TParam.ofEquiv`, `TParam.relEquiv` — one-to-one correspondences and
  equivalences;
* `truncMapHas`, `TParam.trunc`, `embMapHas`, `Param.toTParam` — truncation and embedding;
* `tmapHasArrow`, `tparamArrowAt`, `tmapHasForall`, `tparamForallAt`, `tmapHasSigma`,
  `tparamSigmaAt` — the type formers at the tables above;
* `eqRel`, `TFibStep`, `TFibN` — the truncated fibrancy record.

## Main results

* `TMap4Has.subsingleton`, `nonempty_tmap4_iff` — the coherence is subsingleton witness types;
* `TParam.toEquiv_ofEquiv`, `nonempty_tparam_iff_equiv` — `(map4, map4)` is equivalence;
* `Param.toTParam_trunc` — truncation after embedding is the identity;
* `tForallDomReq_ge`, `tSigmaBaseReq_ge`, `arrowReq_eq_tArrow` — comparison of the tables;
* `tfibN_eqRel_subsingleton`, `tfibNOneEquiv`, `tfibNSuccEquiv`, `tfibNTwoEquiv` — the collapse
  of the truncated fibrancy record.

## References

* C. Cohen, E. Crance, A. Mahboubi, *Trocq: proof transfer for free, with or without
  univalence*, ESOP 2024.
* T. Altenkirch, A. Kaposi, M. Shulman, E. Üsküplü, *From parametricity to identity types*,
  TYPES 2025.
* T. Altenkirch, Y. Chamoun, A. Kaposi, M. Shulman, *Internal parametricity, without an
  interval*, POPL 2024.

Search words: Type-valued relation, proof-relevant relation, span, one-to-one correspondence,
univalent parametricity, equivalence, coherence, R_in_mapK, subsingleton, truncation, Nonempty,
fibrancy, isFib, Narya, level table.
-/

@[expose] public section

set_option autoImplicit false
-- `Param.toTParam` and its lemmas extend ParamTransfer's `Param`, which lives in the `Param`
-- namespace of the engine.
set_option linter.dupNamespace false

universe u

namespace Transfer.Param

/-! ## The records of the levels -/

section Records

variable {A B : Type u}

/-- `map0` over a Type-valued relation: no structure. -/
structure TMap0Has (R : A → B → Type u) : Type u where

/-- `map1` over a Type-valued relation: a forward map. -/
structure TMap1Has (R : A → B → Type u) : Type u where
  /-- The forward map. -/
  map : A → B

/-- `map2a` over a Type-valued relation: a map with a witness for each element of its graph. -/
structure TMap2aHas (R : A → B → Type u) : Type u where
  /-- The forward map. -/
  map : A → B
  /-- A witness of the relation for each element of the graph of `map`. -/
  map_in_R : ∀ a b, map a = b → R a b

/-- `map2b` over a Type-valued relation: a map through which every witness factors. -/
structure TMap2bHas (R : A → B → Type u) : Type u where
  /-- The forward map. -/
  map : A → B
  /-- Every related pair lies in the graph of `map`. -/
  R_in_map : ∀ a b, R a b → map a = b

/-- `map3` over a Type-valued relation: both inclusions. -/
structure TMap3Has (R : A → B → Type u) : Type u where
  /-- The forward map. -/
  map : A → B
  /-- A witness of the relation for each element of the graph of `map`. -/
  map_in_R : ∀ a b, map a = b → R a b
  /-- Every related pair lies in the graph of `map`. -/
  R_in_map : ∀ a b, R a b → map a = b

/-- `map4` over a Type-valued relation: `map3` with the coherence `R_in_mapK`, which makes
`map_in_R a b` and `R_in_map a b` inverse, so that `R a b` is equivalent to `map a = b`. -/
structure TMap4Has (R : A → B → Type u) : Type u where
  /-- The forward map. -/
  map : A → B
  /-- A witness of the relation for each element of the graph of `map`. -/
  map_in_R : ∀ a b, map a = b → R a b
  /-- Every related pair lies in the graph of `map`. -/
  R_in_map : ∀ a b, R a b → map a = b
  /-- The witness of the graph of a witness is that witness. -/
  R_in_mapK : ∀ a b (r : R a b), map_in_R a b (R_in_map a b r) = r

/-- The record of a level over a Type-valued relation. -/
def TMapHas : MapClass → (A → B → Type u) → Type u
  | .map0, R => TMap0Has R
  | .map1, R => TMap1Has R
  | .map2a, R => TMap2aHas R
  | .map2b, R => TMap2bHas R
  | .map3, R => TMap3Has R
  | .map4, R => TMap4Has R

end Records

/-! ## The annotated relation -/

/-- The converse of a Type-valued relation. -/
abbrev tsymRel {A B : Type u} (R : A → B → Type u) : B → A → Type u := fun b a => R a b

/-- `TParam m n A B`: a Type-valued relation with forward structure of level `m` and backward
structure of level `n`. -/
structure TParam (m n : MapClass) (A B : Type u) : Type (u + 1) where
  /-- The relation. -/
  R : A → B → Type u
  /-- The forward structure. -/
  fwd : TMapHas m R
  /-- The backward structure, on the converse relation. -/
  bwd : TMapHas n (tsymRel R)

/-- The converse annotated relation. -/
def TParam.symm {m n : MapClass} {A B : Type u} (P : TParam m n A B) : TParam n m B A where
  R := tsymRel P.R
  fwd := P.bwd
  bwd := P.fwd

/-! ## Weakening -/

section Weaken

variable {A B : Type u} {R : A → B → Type u}

/-- `map2a → map1`. -/
def TMap2aHas.toMap1 (h : TMap2aHas R) : TMap1Has R := ⟨h.map⟩
/-- `map2b → map1`. -/
def TMap2bHas.toMap1 (h : TMap2bHas R) : TMap1Has R := ⟨h.map⟩
/-- `map3 → map2a`. -/
def TMap3Has.toMap2a (h : TMap3Has R) : TMap2aHas R := ⟨h.map, h.map_in_R⟩
/-- `map3 → map2b`. -/
def TMap3Has.toMap2b (h : TMap3Has R) : TMap2bHas R := ⟨h.map, h.R_in_map⟩
/-- `map4 → map3`. -/
def TMap4Has.toMap3 (h : TMap4Has R) : TMap3Has R := ⟨h.map, h.map_in_R, h.R_in_map⟩

/-- Forgetting down the lattice of levels in one direction. -/
def forgetTMapHas : (m' m : MapClass) → m' ⊑ m → TMapHas m R → TMapHas m' R
  | .map0, _, _, _ => (⟨⟩ : TMap0Has R)
  | .map1, .map0, h, _ => by simp [MapClass.le] at h
  | .map1, .map1, _, x => x
  | .map1, .map2a, _, x => TMap2aHas.toMap1 x
  | .map1, .map2b, _, x => TMap2bHas.toMap1 x
  | .map1, .map3, _, x => (TMap3Has.toMap2a x).toMap1
  | .map1, .map4, _, x => (TMap4Has.toMap3 x).toMap2a.toMap1
  | .map2a, .map0, h, _ => by simp [MapClass.le] at h
  | .map2a, .map1, h, _ => by simp [MapClass.le] at h
  | .map2a, .map2a, _, x => x
  | .map2a, .map2b, h, _ => by simp [MapClass.le] at h
  | .map2a, .map3, _, x => TMap3Has.toMap2a x
  | .map2a, .map4, _, x => (TMap4Has.toMap3 x).toMap2a
  | .map2b, .map0, h, _ => by simp [MapClass.le] at h
  | .map2b, .map1, h, _ => by simp [MapClass.le] at h
  | .map2b, .map2a, h, _ => by simp [MapClass.le] at h
  | .map2b, .map2b, _, x => x
  | .map2b, .map3, _, x => TMap3Has.toMap2b x
  | .map2b, .map4, _, x => (TMap4Has.toMap3 x).toMap2b
  | .map3, .map0, h, _ => by simp [MapClass.le] at h
  | .map3, .map1, h, _ => by simp [MapClass.le] at h
  | .map3, .map2a, h, _ => by simp [MapClass.le] at h
  | .map3, .map2b, h, _ => by simp [MapClass.le] at h
  | .map3, .map3, _, x => x
  | .map3, .map4, _, x => TMap4Has.toMap3 x
  | .map4, .map0, h, _ => by simp [MapClass.le] at h
  | .map4, .map1, h, _ => by simp [MapClass.le] at h
  | .map4, .map2a, h, _ => by simp [MapClass.le] at h
  | .map4, .map2b, h, _ => by simp [MapClass.le] at h
  | .map4, .map3, h, _ => by simp [MapClass.le] at h
  | .map4, .map4, _, x => x

end Weaken

/-- Weakening an annotated relation down the lattice in both directions. -/
def TParam.weaken {m m' n n' : MapClass} {A B : Type u} (hm : m' ⊑ m) (hn : n' ⊑ n)
    (P : TParam m n A B) : TParam m' n' A B where
  R := P.R
  fwd := forgetTMapHas m' m hm P.fwd
  bwd := forgetTMapHas n' n hn P.bwd

/-! ## The coherence of `map4` -/

section Coherence

variable {A B : Type u} {R : A → B → Type u}

/-- The witness types of a relation at `map4` are subsingletons: each witness is the witness of
the graph of `map`, and the graph is a proposition. -/
theorem TMap4Has.subsingleton (h : TMap4Has R) (a : A) (b : B) : Subsingleton (R a b) :=
  ⟨fun r r' => (h.R_in_mapK a b r).symm.trans (h.R_in_mapK a b r')⟩

/-- A relation at `map3` with subsingleton witness types is at `map4`. -/
def TMap4Has.ofMap3 (h : TMap3Has R) (hs : ∀ a b, Subsingleton (R a b)) : TMap4Has R :=
  ⟨h.map, h.map_in_R, h.R_in_map, fun a b _ => (hs a b).elim _ _⟩

/-- `map4` is `map3` with subsingleton witness types. -/
def tmap4Equiv : TMap4Has R ≃ {_h : TMap3Has R // ∀ a b, Subsingleton (R a b)} where
  toFun h := ⟨h.toMap3, h.subsingleton⟩
  invFun h := TMap4Has.ofMap3 h.1 h.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- A relation carries `map4` exactly when it carries `map3` and its witness types are
subsingletons. -/
theorem nonempty_tmap4_iff :
    Nonempty (TMap4Has R) ↔ Nonempty (TMap3Has R) ∧ ∀ a b, Subsingleton (R a b) :=
  ⟨fun ⟨h⟩ => ⟨⟨h.toMap3⟩, h.subsingleton⟩, fun ⟨⟨h⟩, hs⟩ => ⟨TMap4Has.ofMap3 h hs⟩⟩

/-- Structure of a level transported along a pointwise equivalence of relations. -/
def TMapHas.ofEquiv {X Y : Type u} {R S : X → Y → Type u} (e : ∀ a b, R a b ≃ S a b) :
    (k : MapClass) → TMapHas k R → TMapHas k S
  | .map0, _ => (⟨⟩ : TMap0Has S)
  | .map1, h => (⟨(h : TMap1Has R).map⟩ : TMap1Has S)
  | .map2a, h =>
    let h : TMap2aHas R := h
    (⟨h.map, fun a b p => e a b (h.map_in_R a b p)⟩ : TMap2aHas S)
  | .map2b, h =>
    let h : TMap2bHas R := h
    (⟨h.map, fun a b s => h.R_in_map a b ((e a b).symm s)⟩ : TMap2bHas S)
  | .map3, h =>
    let h : TMap3Has R := h
    (⟨h.map, fun a b p => e a b (h.map_in_R a b p),
      fun a b s => h.R_in_map a b ((e a b).symm s)⟩ : TMap3Has S)
  | .map4, h =>
    let h : TMap4Has R := h
    (⟨h.map, fun a b p => e a b (h.map_in_R a b p),
      fun a b s => h.R_in_map a b ((e a b).symm s),
      fun a b s => (congrArg (e a b) (h.R_in_mapK a b _)).trans ((e a b).apply_symm_apply s)⟩ :
        TMap4Has S)

end Coherence

/-! ## One-to-one correspondences are equivalences -/

section Equivalence

variable {A B : Type u}

/-- An annotated relation at `(map4, map4)` gives an equivalence: the forward and the backward
maps are inverse. -/
def TParam.toEquiv (P : TParam .map4 .map4 A B) : A ≃ B :=
  let f : TMap4Has P.R := P.fwd
  let g : TMap4Has (tsymRel P.R) := P.bwd
  { toFun := f.map
    invFun := g.map
    left_inv := fun a => g.R_in_map (f.map a) a (f.map_in_R a _ rfl)
    right_inv := fun b => f.R_in_map (g.map b) b (g.map_in_R b _ rfl) }

/-- The graph of an equivalence as an annotated relation at `(map4, map4)`. -/
def TParam.ofEquiv (e : A ≃ B) : TParam .map4 .map4 A B where
  R a b := ULift.{u} (PLift (e a = b))
  fwd := (⟨e, fun _ _ h => ⟨⟨h⟩⟩, fun _ _ r => r.down.down, fun _ _ _ => rfl⟩ : TMap4Has _)
  bwd := (⟨e.symm, fun b a (h : e.symm b = a) => ⟨⟨h ▸ e.apply_symm_apply b⟩⟩,
    fun b a (r : ULift.{u} (PLift (e a = b))) =>
      (congrArg e.symm r.down.down).symm.trans (e.symm_apply_apply a),
    fun _ _ _ => rfl⟩ : TMap4Has (tsymRel fun a b => ULift.{u} (PLift (e a = b))))

/-- The equivalence of the graph of an equivalence is that equivalence. -/
theorem TParam.toEquiv_ofEquiv (e : A ≃ B) : (TParam.ofEquiv e).toEquiv = e :=
  Equiv.ext fun _ => rfl

/-- The relation of an annotated relation at `(map4, map4)` is equivalent, pointwise, to the
graph of its equivalence. -/
def TParam.relEquiv (P : TParam .map4 .map4 A B) (a : A) (b : B) :
    (TParam.ofEquiv P.toEquiv).R a b ≃ P.R a b :=
  let f : TMap4Has P.R := P.fwd
  { toFun := fun r => f.map_in_R a b r.down.down
    invFun := fun r => ⟨⟨f.R_in_map a b r⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun r => f.R_in_mapK a b r }

/-- Two types are joined by an annotated relation at `(map4, map4)` exactly when they are
equivalent. -/
theorem nonempty_tparam_iff_equiv :
    Nonempty (TParam .map4 .map4 A B) ↔ Nonempty (A ≃ B) :=
  ⟨fun ⟨P⟩ => ⟨P.toEquiv⟩, fun ⟨e⟩ => ⟨TParam.ofEquiv e⟩⟩

/-- An annotated relation at `(map3, map3)` with subsingleton witness types is at
`(map4, map4)`. -/
def TParam.ofMap3 (P : TParam .map3 .map3 A B) (hs : ∀ a b, Subsingleton (P.R a b)) :
    TParam .map4 .map4 A B where
  R := P.R
  fwd := TMap4Has.ofMap3 (P.fwd : TMap3Has P.R) hs
  bwd := TMap4Has.ofMap3 (P.bwd : TMap3Has (tsymRel P.R)) fun b a => hs a b

/-- The annotated relations at `(map4, map4)` are those at `(map3, map3)` with subsingleton
witness types. -/
def tparam44Equiv :
    {P : TParam .map3 .map3 A B // ∀ a b, Subsingleton (P.R a b)} ≃ TParam .map4 .map4 A B where
  toFun P := P.1.ofMap3 P.2
  invFun P := ⟨P.weaken (MapClass.le_map4 _) (MapClass.le_map4 _),
    (P.fwd : TMap4Has P.R).subsingleton⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Equivalence

/-! ## Truncation and embedding -/

section Truncation

variable {A B : Type u}

/-- The propositional truncation of a Type-valued relation. -/
abbrev truncRel (R : A → B → Type u) : A → B → Prop := fun a b => Nonempty (R a b)

/-- The Type-valued relation of a propositional relation. -/
abbrev liftRel (R : A → B → Prop) : A → B → Type u := fun a b => ULift.{u} (PLift (R a b))

/-- Truncation preserves every level. -/
def truncMapHas {R : A → B → Type u} : (k : MapClass) → TMapHas k R → MapHas k (truncRel R)
  | .map0, _ => (⟨⟩ : Map0Has _)
  | .map1, h => (⟨(h : TMap1Has R).map⟩ : Map1Has _)
  | .map2a, h =>
    let h : TMap2aHas R := h
    (⟨h.map, fun a b e => ⟨h.map_in_R a b e⟩⟩ : Map2aHas _)
  | .map2b, h =>
    let h : TMap2bHas R := h
    (⟨h.map, fun a b r => r.elim (h.R_in_map a b)⟩ : Map2bHas _)
  | .map3, h =>
    let h : TMap3Has R := h
    (⟨h.map, fun a b e => ⟨h.map_in_R a b e⟩, fun a b r => r.elim (h.R_in_map a b)⟩ :
      Map3Has _)
  | .map4, h =>
    let h : TMap4Has R := h
    (⟨h.map, fun a b e => ⟨h.map_in_R a b e⟩, fun a b r => r.elim (h.R_in_map a b),
      fun _ _ _ => rfl⟩ : Map4Has _)

/-- The propositional truncation of an annotated relation, at the same levels. -/
def TParam.trunc {m n : MapClass} (P : TParam m n A B) : Param m n A B where
  R := truncRel P.R
  fwd := truncMapHas m P.fwd
  bwd := truncMapHas n P.bwd

/-- The embedding preserves every level. -/
def embMapHas {R : A → B → Prop} : (k : MapClass) → MapHas k R → TMapHas k (liftRel R)
  | .map0, _ => (⟨⟩ : TMap0Has _)
  | .map1, h => (⟨(h : Map1Has R).map⟩ : TMap1Has _)
  | .map2a, h =>
    let h : Map2aHas R := h
    (⟨h.map, fun a b e => ⟨⟨h.map_in_R a b e⟩⟩⟩ : TMap2aHas _)
  | .map2b, h =>
    let h : Map2bHas R := h
    (⟨h.map, fun a b r => h.R_in_map a b r.down.down⟩ : TMap2bHas _)
  | .map3, h =>
    let h : Map3Has R := h
    (⟨h.map, fun a b e => ⟨⟨h.map_in_R a b e⟩⟩, fun a b r => h.R_in_map a b r.down.down⟩ :
      TMap3Has _)
  | .map4, h =>
    let h : Map4Has R := h
    (⟨h.map, fun a b e => ⟨⟨h.map_in_R a b e⟩⟩, fun a b r => h.R_in_map a b r.down.down,
      fun _ _ _ => rfl⟩ : TMap4Has _)

/-- A propositional annotated relation as a Type-valued one, at the same levels. -/
def Param.toTParam {m n : MapClass} (P : Param m n A B) : TParam m n A B where
  R := liftRel P.R
  fwd := embMapHas m P.fwd
  bwd := embMapHas n P.bwd

/-- The truncation of the embedding of a propositional relation is that relation. -/
theorem truncRel_liftRel (R : A → B → Prop) : truncRel (liftRel.{u} R) = R :=
  funext fun _ => funext fun _ =>
    propext ⟨fun ⟨r⟩ => r.down.down, fun r => ⟨⟨⟨r⟩⟩⟩⟩

/-- Truncation after embedding is the identity on the structure of each level. -/
theorem truncMapHas_embMapHas {R : A → B → Prop} (k : MapClass) (h : MapHas k R) :
    HEq (truncMapHas k (embMapHas k h)) h := by
  cases k <;> cases h <;> simp only [truncMapHas, embMapHas] <;> congr <;>
    first | exact truncRel_liftRel R | exact proof_irrel_heq _ _

/-- Truncation after embedding is the identity on annotated relations. -/
theorem Param.toTParam_trunc {m n : MapClass} (P : Param m n A B) : P.toTParam.trunc = P := by
  obtain ⟨R, f, g⟩ := P
  simp only [Param.toTParam, TParam.trunc]
  congr
  · exact truncRel_liftRel R
  · exact truncMapHas_embMapHas m f
  · exact truncMapHas_embMapHas n g

end Truncation

/-! ## The function type -/

/-- The backward level of the domain that the function type asks for at an output level. -/
def tArrowDomReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map1
  | .map2a => .map2b
  | .map2b => .map2a
  | .map3 => .map3
  | .map4 => .map3

/-- The forward level of the codomain that the function type asks for at an output level. -/
def tArrowCodReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map1
  | .map2a => .map2a
  | .map2b => .map2b
  | .map3 => .map3
  | .map4 => .map4

/-- Below `map4` the tables of the function type are those of `arrowReq`. -/
theorem arrowReq_eq_tArrow (t : MapClass) (ht : t ≠ .map4) :
    arrowReq t = some (.map0, tArrowDomReq t, tArrowCodReq t, .map0) := by
  cases t <;> simp_all [arrowReq, tArrowDomReq, tArrowCodReq]

section Arrow

variable {A A' B B' : Type u} {RA : A → A' → Type u} {RB : B → B' → Type u}

/-- The relation of functions: related arguments go to related values. -/
def tArrowRel (RA : A → A' → Type u) (RB : B → B' → Type u) : (A → B) → (A' → B') → Type u :=
  fun f f' => ∀ a a', RA a a' → RB (f a) (f' a')

/-- The relation of functions has subsingleton witness types when the codomain has. -/
theorem tArrowRel_subsingleton (hB : ∀ b b', Subsingleton (RB b b')) (f : A → B)
    (f' : A' → B') : Subsingleton (tArrowRel RA RB f f') :=
  ⟨fun _ _ => funext fun _ => funext fun _ => funext fun _ => (hB _ _).elim _ _⟩

/-- The function type at output `map2a`. -/
def tArrowMap2a (hA : TMap2bHas (tsymRel RA)) (hB : TMap2aHas RB) :
    TMap2aHas (tArrowRel RA RB) where
  map f a' := hB.map (f (hA.map a'))
  map_in_R f f' e a a' h := by
    subst e
    obtain rfl := hA.R_in_map a' a h
    exact hB.map_in_R _ _ rfl

/-- The function type at output `map2b`. -/
def tArrowMap2b (hA : TMap2aHas (tsymRel RA)) (hB : TMap2bHas RB) :
    TMap2bHas (tArrowRel RA RB) where
  map f a' := hB.map (f (hA.map a'))
  R_in_map _ _ r := funext fun a' => hB.R_in_map _ _ (r _ a' (hA.map_in_R a' _ rfl))

/-- The function type at output `map3`. -/
def tArrowMap3 (hA : TMap3Has (tsymRel RA)) (hB : TMap3Has RB) : TMap3Has (tArrowRel RA RB) :=
  ⟨fun f a' => hB.map (f (hA.map a')), (tArrowMap2a hA.toMap2b hB.toMap2a).map_in_R,
    (tArrowMap2b hA.toMap2a hB.toMap2b).R_in_map⟩

/-- The function type at every output level, at the tables `tArrowDomReq`, `tArrowCodReq`. -/
def tmapHasArrow : (t : MapClass) → TMapHas (tArrowDomReq t) (tsymRel RA) →
    TMapHas (tArrowCodReq t) RB → TMapHas t (tArrowRel RA RB)
  | .map0, _, _ => (⟨⟩ : TMap0Has _)
  | .map1, hA, hB =>
    (⟨fun f a' => (hB : TMap1Has RB).map (f ((hA : TMap1Has (tsymRel RA)).map a'))⟩ :
      TMap1Has _)
  | .map2a, hA, hB => tArrowMap2a hA hB
  | .map2b, hA, hB => tArrowMap2b hA hB
  | .map3, hA, hB => tArrowMap3 hA hB
  | .map4, hA, hB =>
    TMap4Has.ofMap3 (tArrowMap3 hA (TMap4Has.toMap3 hB))
      (tArrowRel_subsingleton (TMap4Has.subsingleton hB))

end Arrow

/-- The function-type `TParam` at every pair of output levels. -/
def tparamArrowAt {A A' B B' : Type u} (t s : MapClass)
    (PA : TParam (tArrowDomReq s) (tArrowDomReq t) A A')
    (PB : TParam (tArrowCodReq t) (tArrowCodReq s) B B') : TParam t s (A → B) (A' → B') where
  R := tArrowRel PA.R PB.R
  fwd := tmapHasArrow t PA.bwd PB.fwd
  bwd := TMapHas.ofEquiv
    (fun _ _ => ⟨fun r a a' h => r a' a h, fun r a' a h => r a a' h, fun _ => rfl, fun _ => rfl⟩)
    s (tmapHasArrow (RA := tsymRel PA.R) (RB := tsymRel PB.R) s PA.fwd PB.bwd)

/-! ## The dependent product -/

/-- The backward level of the domain that the dependent product asks for at an output level. -/
def tForallDomReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map2a
  | .map2a => .map4
  | .map2b => .map2a
  | .map3 => .map4
  | .map4 => .map4

/-- The dependent product asks for at least the domain level of `forallReq`. -/
theorem tForallDomReq_ge (t : MapClass) : forallReq t ⊑ tForallDomReq t := by
  cases t <;> rfl

/-- The dependent product asks for its fibres at least the level of `forallFiberReq`. -/
theorem forallFiberReq_le_self (t : MapClass) : forallFiberReq t ⊑ t := by
  cases t <;> rfl

section Forall

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u} {RA : A → A' → Type u}
  {RB : ∀ a a', RA a a' → B a → B' a' → Type u}

/-- The relation of dependent functions: arguments related by a witness go to values related at
that witness. -/
def tForallRel (RA : A → A' → Type u) (RB : ∀ a a', RA a a' → B a → B' a' → Type u) :
    (∀ a, B a) → (∀ a', B' a') → Type u :=
  fun f f' => ∀ a a' (h : RA a a'), RB a a' h (f a) (f' a')

/-- The map of dependent functions: the backward map of the domain, then the fibre map at its
witness. -/
def tForallMap (imap : A' → A) (wit : ∀ a', RA (imap a') a')
    (fmap : ∀ a a', RA a a' → B a → B' a') : (∀ a, B a) → ∀ a', B' a' :=
  fun f a' => fmap _ _ (wit a') (f (imap a'))

/-- The relation of dependent functions has subsingleton witness types when the fibres have. -/
theorem tForallRel_subsingleton (hB : ∀ a a' h x y, Subsingleton (RB a a' h x y))
    (f : ∀ a, B a) (f' : ∀ a', B' a') : Subsingleton (tForallRel RA RB f f') :=
  ⟨fun _ _ => funext fun _ => funext fun _ => funext fun _ => (hB _ _ _ _ _).elim _ _⟩

/-- The dependent product at output `map2a`. The coherence of the domain identifies a witness
`h : RA a a'` with the witness of the graph of the backward map, at which the fibre map acts. -/
def tForallMap2a (hA : TMap4Has (tsymRel RA)) (hB : ∀ a a' h, TMap2aHas (RB a a' h)) :
    TMap2aHas (tForallRel RA RB) where
  map := tForallMap hA.map (fun a' => hA.map_in_R a' _ rfl) fun a a' h => (hB a a' h).map
  map_in_R f g e a a' h := by
    subst e
    rw [← hA.R_in_mapK a' a h]
    generalize hA.R_in_map a' a h = w
    subst w
    exact (hB _ _ _).map_in_R _ _ rfl

/-- The dependent product at output `map2b`. -/
def tForallMap2b (hA : TMap2aHas (tsymRel RA)) (hB : ∀ a a' h, TMap2bHas (RB a a' h)) :
    TMap2bHas (tForallRel RA RB) where
  map := tForallMap hA.map (fun a' => hA.map_in_R a' _ rfl) fun a a' h => (hB a a' h).map
  R_in_map _ _ r := funext fun a' => (hB _ _ _).R_in_map _ _ (r _ a' _)

/-- The dependent product at output `map3`. -/
def tForallMap3 (hA : TMap4Has (tsymRel RA)) (hB : ∀ a a' h, TMap3Has (RB a a' h)) :
    TMap3Has (tForallRel RA RB) :=
  ⟨tForallMap hA.map (fun a' => hA.map_in_R a' _ rfl) fun a a' h => (hB a a' h).map,
    (tForallMap2a hA fun a a' h => (hB a a' h).toMap2a).map_in_R,
    (tForallMap2b hA.toMap3.toMap2a fun a a' h => (hB a a' h).toMap2b).R_in_map⟩

/-- The dependent product at every output level, at the table `tForallDomReq` and with the
fibres at the output level. -/
def tmapHasForall : (t : MapClass) → TMapHas (tForallDomReq t) (tsymRel RA) →
    (∀ a a' h, TMapHas t (RB a a' h)) → TMapHas t (tForallRel RA RB)
  | .map0, _, _ => (⟨⟩ : TMap0Has _)
  | .map1, hA, hB =>
    let hA : TMap2aHas (tsymRel RA) := hA
    let hB : ∀ a a' h, TMap1Has (RB a a' h) := hB
    (⟨tForallMap hA.map (fun a' => hA.map_in_R a' _ rfl) fun a a' h => (hB a a' h).map⟩ :
      TMap1Has _)
  | .map2a, hA, hB => tForallMap2a hA hB
  | .map2b, hA, hB => tForallMap2b hA hB
  | .map3, hA, hB => tForallMap3 hA hB
  | .map4, hA, hB =>
    let hB : ∀ a a' h, TMap4Has (RB a a' h) := hB
    TMap4Has.ofMap3 (tForallMap3 hA fun a a' h => (hB a a' h).toMap3)
      (tForallRel_subsingleton fun a a' h => (hB a a' h).subsingleton)

end Forall

/-- The dependent-product `TParam` at every pair of output levels. -/
def tparamForallAt {A A' : Type u} {B : A → Type u} {B' : A' → Type u} (t s : MapClass)
    (PA : TParam (tForallDomReq s) (tForallDomReq t) A A')
    (PB : ∀ a a', PA.R a a' → TParam t s (B a) (B' a')) :
    TParam t s (∀ a, B a) (∀ a', B' a') where
  R := tForallRel PA.R fun a a' h => (PB a a' h).R
  fwd := tmapHasForall t PA.bwd fun a a' h => (PB a a' h).fwd
  bwd := TMapHas.ofEquiv
    (fun _ _ => ⟨fun r a a' h => r a' a h, fun r a' a h => r a a' h, fun _ => rfl, fun _ => rfl⟩)
    s (tmapHasForall (B := B') (B' := B) (RA := tsymRel PA.R)
      (RB := fun a' a h => tsymRel (PB a a' h).R) s PA.fwd fun a' a h => (PB a a' h).bwd)

/-! ## The dependent sum -/

/-- The forward level of the base that the dependent sum asks for at an output level. -/
def tSigmaBaseReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map2a
  | .map2a => .map2a
  | .map2b => .map4
  | .map3 => .map4
  | .map4 => .map4

/-- The dependent sum asks for at least the base level of `sigmaBaseReq`. -/
theorem tSigmaBaseReq_ge (t : MapClass) : sigmaBaseReq t ⊑ tSigmaBaseReq t := by
  cases t <;> rfl

section Sigma

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u} {SR : A → A' → Type u}
  {FR : ∀ a a', SR a a' → B a → B' a' → Type u}

/-- The relation of dependent pairs: a witness relating the bases, and a witness relating the
second components at it. -/
def tSigmaRel (SR : A → A' → Type u) (FR : ∀ a a', SR a a' → B a → B' a' → Type u) :
    (Σ a, B a) → (Σ a', B' a') → Type u :=
  fun p q => Σ h : SR p.1 q.1, FR p.1 q.1 h p.2 q.2

/-- The map of dependent pairs: the base map, and the fibre map at the witness of the base. -/
def tSigmaFwd (smap : A → A') (wit : ∀ a, SR a (smap a))
    (fmap : ∀ a a', SR a a' → B a → B' a') : (Σ a, B a) → (Σ a', B' a') :=
  fun p => ⟨smap p.1, fmap p.1 (smap p.1) (wit p.1) p.2⟩

/-- The relation of dependent pairs has subsingleton witness types when the base and the fibres
have. -/
theorem tSigmaRel_subsingleton (hS : ∀ a a', Subsingleton (SR a a'))
    (hF : ∀ a a' h x y, Subsingleton (FR a a' h x y)) (p : Σ a, B a) (q : Σ a', B' a') :
    Subsingleton (tSigmaRel SR FR p q) := by
  constructor
  rintro ⟨h, r⟩ ⟨h', r'⟩
  obtain rfl : h = h' := (hS _ _).elim _ _
  obtain rfl : r = r' := (hF _ _ _ _ _).elim _ _
  rfl

/-- The dependent sum at output `map2a`. -/
def tSigmaMap2a (hS : TMap2aHas SR) (hF : ∀ a a' h, TMap2aHas (FR a a' h)) :
    TMap2aHas (tSigmaRel SR FR) where
  map := tSigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map
  map_in_R p q e := by
    subst e
    exact ⟨hS.map_in_R p.1 _ rfl, (hF _ _ _).map_in_R _ _ rfl⟩

/-- The graph of the map of dependent pairs contains a pair of witnesses whose base witness is
the witness of an equation. -/
theorem tSigmaFwd_eq (hS : TMap2aHas SR) (hF : ∀ a a' h, TMap2bHas (FR a a' h)) (a : A)
    (b : A') (x : B a) (y : B' b) (w : hS.map a = b) (r : FR a b (hS.map_in_R a b w) x y) :
    tSigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) (fun a a' h => (hF a a' h).map) ⟨a, x⟩ =
      ⟨b, y⟩ := by
  subst w
  exact congrArg (Sigma.mk _) ((hF _ _ _).R_in_map _ _ r)

/-- The dependent sum at output `map2b`. The coherence of the base identifies a base witness
with the witness of the graph of the base map, at which the fibre map acts. -/
def tSigmaMap2b (hS : TMap4Has SR) (hF : ∀ a a' h, TMap2bHas (FR a a' h)) :
    TMap2bHas (tSigmaRel SR FR) where
  map := tSigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map
  R_in_map := by
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨h, r⟩
    have r' : FR a b (hS.map_in_R a b (hS.R_in_map a b h)) x y := by
      rw [hS.R_in_mapK]
      exact r
    exact tSigmaFwd_eq hS.toMap3.toMap2a hF a b x y _ r'

/-- The dependent sum at output `map3`. -/
def tSigmaMap3 (hS : TMap4Has SR) (hF : ∀ a a' h, TMap3Has (FR a a' h)) :
    TMap3Has (tSigmaRel SR FR) :=
  ⟨tSigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map,
    (tSigmaMap2a hS.toMap3.toMap2a fun a a' h => (hF a a' h).toMap2a).map_in_R,
    (tSigmaMap2b hS fun a a' h => (hF a a' h).toMap2b).R_in_map⟩

/-- The dependent sum at every output level, at the table `tSigmaBaseReq` and with the fibres at
the output level. -/
def tmapHasSigma : (t : MapClass) → TMapHas (tSigmaBaseReq t) SR →
    (∀ a a' h, TMapHas t (FR a a' h)) → TMapHas t (tSigmaRel SR FR)
  | .map0, _, _ => (⟨⟩ : TMap0Has _)
  | .map1, hS, hF =>
    let hS : TMap2aHas SR := hS
    let hF : ∀ a a' h, TMap1Has (FR a a' h) := hF
    (⟨tSigmaFwd hS.map (fun a => hS.map_in_R a _ rfl) fun a a' h => (hF a a' h).map⟩ :
      TMap1Has _)
  | .map2a, hS, hF => tSigmaMap2a hS hF
  | .map2b, hS, hF => tSigmaMap2b hS hF
  | .map3, hS, hF => tSigmaMap3 hS hF
  | .map4, hS, hF =>
    let hS : TMap4Has SR := hS
    let hF : ∀ a a' h, TMap4Has (FR a a' h) := hF
    TMap4Has.ofMap3 (tSigmaMap3 hS fun a a' h => (hF a a' h).toMap3)
      (tSigmaRel_subsingleton hS.subsingleton fun a a' h => (hF a a' h).subsingleton)

end Sigma

/-- The dependent-sum `TParam` at every pair of output levels. -/
def tparamSigmaAt {A A' : Type u} {B : A → Type u} {B' : A' → Type u} (t s : MapClass)
    (PA : TParam (tSigmaBaseReq t) (tSigmaBaseReq s) A A')
    (PB : ∀ a a', PA.R a a' → TParam t s (B a) (B' a')) :
    TParam t s (Σ a, B a) (Σ a', B' a') where
  R := tSigmaRel PA.R fun a a' h => (PB a a' h).R
  fwd := tmapHasSigma t PA.fwd fun a a' h => (PB a a' h).fwd
  bwd := tmapHasSigma (B := B') (B' := B) (SR := tsymRel PA.R)
    (FR := fun a' a h => tsymRel (PB a a' h).R) s PA.bwd fun a' a h => (PB a a' h).bwd

/-! ## The truncated fibrancy record -/

/-- The identity relation of a type, Type-valued. -/
abbrev eqRel (X : Type u) : X → X → Type u := fun x y => ULift.{u} (PLift (x = y))

/-- One layer of the fibrancy record of a relation `R`: transport and lift in both directions,
and the field `id` with values in `Next`. -/
structure TFibStep {A B : Type u} (R : A → B → Type u) (Next : A → B → Type u) : Type u where
  /-- Transport to the right. -/
  trr : A → B
  /-- Transport to the left. -/
  trl : B → A
  /-- The lift of the right transport. -/
  liftr : ∀ a, R a (trr a)
  /-- The lift of the left transport. -/
  liftl : ∀ b, R (trl b) b
  /-- The field `id`: the fibrancy of the witness types, one depth lower. -/
  id : ∀ a b, Next a b

/-- The depth-`n` truncation of the fibrancy record: no field at depth `0`, and at depth `n + 1`
one layer whose field `id` is the depth-`n` fibrancy of the identity relation of each witness
type `R a b`. -/
def TFibN : Nat →{A B : Type u} → (A → B → Type u) → Type u
  | 0, _, _, _ => PUnit
  | n + 1, _, _, R => TFibStep R fun a b => TFibN n (eqRel (R a b))

/-- The fibrancy of an identity relation, at every depth: transport is the identity. -/
def tfibNEqRel : (n : Nat) → (X : Type u) → TFibN n (eqRel X)
  | 0, _ => PUnit.unit
  | n + 1, _ =>
    (⟨fun x => x, fun x => x, fun _ => ⟨⟨rfl⟩⟩, fun _ => ⟨⟨rfl⟩⟩, fun _ _ => tfibNEqRel n _⟩ :
      TFibStep _ _)

/-- The fibrancy of an identity relation is unique at every depth: the lifts force transport to
be the identity, and the witness types of an identity relation are propositions. -/
theorem tfibN_eqRel_subsingleton : (n : Nat) → (X : Type u) → Subsingleton (TFibN n (eqRel X))
  | 0, _ => ⟨fun _ _ => rfl⟩
  | n + 1, X => by
    constructor
    intro x y
    obtain ⟨t, t', l, l', i⟩ := (x : TFibStep (eqRel X) fun a b => TFibN n (eqRel (eqRel X a b)))
    obtain ⟨s, s', k, k', j⟩ := (y : TFibStep (eqRel X) fun a b => TFibN n (eqRel (eqRel X a b)))
    obtain rfl : t = s := funext fun a => (l a).down.down.symm.trans (k a).down.down
    obtain rfl : t' = s' := funext fun b => (l' b).down.down.trans (k' b).down.down.symm
    obtain rfl : l = k := funext fun _ => Subsingleton.elim _ _
    obtain rfl : l' = k' := funext fun _ => Subsingleton.elim _ _
    obtain rfl : i = j :=
      funext fun a => funext fun b => (tfibN_eqRel_subsingleton n (eqRel X a b)).elim _ _
    rfl

/-- At depth `1` the fibrancy record is `map2a` in both directions. -/
def tfibNOneEquiv {A B : Type u} (R : A → B → Type u) :
    TFibN 1 R ≃ TMap2aHas R × TMap2aHas (tsymRel R) where
  toFun x :=
    let x : TFibStep R fun a b => TFibN 0 (eqRel (R a b)) := x
    (⟨x.trr, fun a _ e => e ▸ x.liftr a⟩, ⟨x.trl, fun b _ e => e ▸ x.liftl b⟩)
  invFun p :=
    (⟨p.1.map, p.2.map, fun a => p.1.map_in_R a _ rfl, fun b => p.2.map_in_R b _ rfl,
      fun _ _ => PUnit.unit⟩ : TFibStep R fun a b => TFibN 0 (eqRel (R a b)))
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨f, hf⟩, ⟨g, hg⟩⟩
    have e1 : (fun a b (e : f a = b) => e ▸ hf a _ rfl) = hf :=
      funext fun a => funext fun b => funext fun e => by subst e; rfl
    have e2 : (fun b a (e : g b = a) => e ▸ hg b _ rfl) = hg :=
      funext fun b => funext fun a => funext fun e => by subst e; rfl
    simp only [e1, e2]

/-- From depth `1` on, the fibrancy record is determined by its first layer: the field `id` is
the fibrancy of identity relations, which is unique. -/
def tfibNSuccEquiv {A B : Type u} (n : Nat) (R : A → B → Type u) :
    TFibN (n + 1) R ≃ TFibN 1 R where
  toFun x :=
    let x : TFibStep R fun a b => TFibN n (eqRel (R a b)) := x
    (⟨x.trr, x.trl, x.liftr, x.liftl, fun _ _ => PUnit.unit⟩ :
      TFibStep R fun a b => TFibN 0 (eqRel (R a b)))
  invFun x :=
    let x : TFibStep R fun a b => TFibN 0 (eqRel (R a b)) := x
    (⟨x.trr, x.trl, x.liftr, x.liftl, fun a b => tfibNEqRel n (R a b)⟩ :
      TFibStep R fun a b => TFibN n (eqRel (R a b)))
  left_inv x := by
    obtain ⟨t, t', l, l', i⟩ := (x : TFibStep R fun a b => TFibN n (eqRel (R a b)))
    obtain rfl : (fun a b => tfibNEqRel n (R a b)) = i :=
      funext fun a => funext fun b => (tfibN_eqRel_subsingleton n (R a b)).elim _ _
    rfl
  right_inv _ := rfl

/-- From depth `2` on, the fibrancy record is determined by its truncation at depth `2`. -/
def tfibNTwoEquiv {A B : Type u} (n : Nat) (R : A → B → Type u) :
    TFibN (n + 2) R ≃ TFibN 2 R :=
  (tfibNSuccEquiv (n + 1) R).trans (tfibNSuccEquiv 1 R).symm

end Transfer.Param
