/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Related
import Transfer.Base.Levels
import Transfer.Base.Hierarchy

/-!
# **Level-annotated** relatedness

This refines the `Related` kernel (`Bridges/Transfer/Related`) with the relatedness
levels of `Bridges/Transfer/Levels`. A `RelatedAt lvl enc a b` carries the same
underlying equation `enc a = b` and additionally records the strongest encoding
strength (`RelLevel`) available along this transfer.

The level is metadata rather than a proof obligation: the equation is identical
at every level. The level provides reflection at the `embedding` level —
`transferIffAt` turns a one-way encoding equality into the two-way `↔` of
`ReprEmbeddingClass.eq_iff`, which the bare `map` level cannot supply.

Composition follows `Levels.meet`: an op-tree assembled from sub-transfers is
only as strong as its weakest part, so `composeBinOpAt` sits at the meet of the
component levels — and since `RelLevel.meet` is the view of the `MapClass`
lattice meet, the composite's level index is computed in the Trocq lattice
(`composeBinOpAt_level_toMapClass`).

## The `Param`-hierarchy foundation

The primary, lattice-indexed semantics of a level-annotated transfer is
membership in the graph `Param` at the image level: `RelLevel.graphParam lvl
enc : Param lvl.toMapClass .map0` packages the graph of `enc` with the exact
`MapHas` structure the image level carries (`map1` a bare map, `map3` both
inclusions, `map4` + the proof-irrelevance coherence), and
`relatedAt_iff_graphParam` identifies `RelatedAt lvl enc a b` with
`(graphParam lvl enc).R a b`. At the class-registered points the graph `Param`
*is* the committed hierarchy witness (`graphParam_map_eq_paramOfMap`,
`graphParam_embedding_eq_paramOfEmbedding`), and the `embedding`-level
reflection `transferIffAt` is derived from its `Param`-side form
(`transferIffParam`). The `RelatedAt` class is kept as the resolution-facing
wrapper over this semantics.

## Bridges to the unlevelled kernel

* `RelatedAt.toRelated` — forget the level (always sound: same equation).
* `Related.toRelatedAtMap` — every transfer is at least `map`-level.
-/

set_option autoImplicit false

namespace Transfer

universe u

/-- `RelatedAt lvl enc a b`: like `Related enc a b` (the value `b` is the
    encoding `enc a` of `a`), but indexed by the relatedness `lvl` recording the
    strongest encoding strength available along this transfer. The underlying
    equation is the same at every level. -/
class RelatedAt (lvl : RelLevel) {A α : Type u} (enc : A → α) (a : A) (b : α) :
    Prop where
  /-- `b` is exactly the encoding of `a`. -/
  rel : enc a = b

/-- A level-annotated registered realization of a binary operation: the
    commuting square `enc (op x y) = bop (enc x) (enc y)`, tagged with the level
    `lvl` at which the operation's encoding is realized. -/
class RelatedBinOpAt (lvl : RelLevel) {A α : Type u} (enc : A → α)
    (op : A → A → A) (bop : α → α → α) : Prop where
  /-- The commuting square for this operation. -/
  comm : ∀ x y, enc (op x y) = bop (enc x) (enc y)

/-- Composition. A composite transfer is only as strong as its weakest part.
    A realized operation at level `lop` and operands at levels `la`, `lb` give
    the composite at `meet lop (meet la lb)`. The equation proof mirrors
    `composeBinOp`. -/
instance composeBinOpAt {lop la lb : RelLevel} {A α : Type u} (enc : A → α)
    (op : A → A → A) (bop : α → α → α) (a b : A) (a' b' : α)
    [hop : RelatedBinOpAt lop enc op bop] [ha : RelatedAt la enc a a']
    [hb : RelatedAt lb enc b b'] :
    RelatedAt (RelLevel.meet lop (RelLevel.meet la lb)) enc (op a b) (bop a' b') where
  rel := (hop.comm a b).trans (by rw [ha.rel, hb.rel])

/-- Leaf (generic encoding) at an explicit level. The encoding of a value is
    related to it. Low priority so `composeBinOpAt` is preferred and resolution
    terminates at leaves. The level must be pinned by the goal. -/
instance (priority := low) leafAt {lvl : RelLevel} {A α : Type u} (enc : A → α)
    (a : A) : RelatedAt lvl enc a (enc a) where
  rel := rfl

/-- Leaf for the identity encoding at an explicit level. Gives the head
    `RelatedAt lvl id a a` directly (resolution will not reduce `id a` to `a`). -/
instance (priority := low) leafIdAt {lvl : RelLevel} {α : Type u} (a : α) :
    RelatedAt lvl (id : α → α) a a where
  rel := rfl

/-- Forget the level. A level-annotated transfer is always a plain transfer:
    same equation. -/
theorem RelatedAt.toRelated {lvl : RelLevel} {A α : Type u} {enc : A → α} {a : A}
    {b : α} (h : RelatedAt lvl enc a b) : Related enc a b where
  rel := h.rel

/-- Every transfer is at least `map`-level. A plain transfer lifts to a
    `map`-annotated one (the weakest level). -/
theorem Related.toRelatedAtMap {A α : Type u} {enc : A → α} {a : A} {b : α}
    (h : Related enc a b) : RelatedAt RelLevel.map enc a b where
  rel := h.rel

/-- Transfer corollary. Extracts the underlying equation from a level-annotated
    transfer. -/
theorem transferRelAt {lvl : RelLevel} {A α : Type u} {enc : A → α} {a : A}
    {b : α} (h : RelatedAt lvl enc a b) : enc a = b := h.rel

/-- The level a transfer used, reportable as data. -/
def levelOf {lvl : RelLevel} {A α : Type u} {enc : A → α} {a : A} {b : α}
    (_ : RelatedAt lvl enc a b) : RelLevel := lvl

/-! ## The `Param`-hierarchy foundation: graph `Param` at the image level -/

/-- The forward `MapHas` structure of the graph of `enc` at the image level
    `lvl.toMapClass`: a bare map at `map1`, both graph inclusions (identities)
    at `map3`, and the `map4` coherence free by proof irrelevance on the
    `Prop`-valued graph. -/
def RelLevel.graphMapHas {A α : Type u} (enc : A → α) :
    (lvl : RelLevel) → Param.MapHas lvl.toMapClass (fun a b => enc a = b)
  | .map => ⟨enc⟩
  | .embedding => ⟨enc, fun _ _ h => h, fun _ _ h => h⟩
  | .equiv => ⟨enc, fun _ _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩

/-- The graph of `enc` as an annotated relation at the image level: the
    **primary, lattice-indexed semantics** of a level-annotated transfer.
    Backward `map0` — no decoder is packaged (an annotation records forward
    strength only; the backward directions live in the `Param` hierarchy's
    committed witnesses). -/
def RelLevel.graphParam {A α : Type u} (lvl : RelLevel) (enc : A → α) :
    Param.Param lvl.toMapClass .map0 A α where
  R := fun a b => enc a = b
  fwd := RelLevel.graphMapHas enc lvl
  bwd := ⟨⟩

/-- Old = new: `RelatedAt lvl enc a b` is exactly membership in the graph
    `Param`'s relation at the image level. The class is the resolution-facing
    wrapper over this `Param`-hierarchy semantics. -/
theorem relatedAt_iff_graphParam {lvl : RelLevel} {A α : Type u} {enc : A → α}
    {a : A} {b : α} :
    RelatedAt lvl enc a b ↔ (RelLevel.graphParam lvl enc).R a b :=
  ⟨fun h => h.rel, fun h => ⟨h⟩⟩

/-- At the `map` point the graph `Param` of a class-registered map is the
    committed hierarchy witness `paramOfMap`. -/
theorem graphParam_map_eq_paramOfMap {A α : Type u} [ReprMapClass A α] :
    RelLevel.graphParam .map (ReprMapClass.enc : A → α) = Param.paramOfMap :=
  rfl

/-- At the `embedding` point the graph `Param` of a class-registered embedding
    is the committed hierarchy witness `paramOfEmbedding`. -/
theorem graphParam_embedding_eq_paramOfEmbedding {A α : Type u}
    [ReprEmbeddingClass A α] :
    RelLevel.graphParam .embedding (ReprMapClass.enc : A → α)
      = Param.paramOfEmbedding :=
  rfl

/-- The composite level index of `composeBinOpAt` is computed in the
    `MapClass` lattice: its `toMapClass` is the lattice meet of the images
    (immediate from the lattice definition of `RelLevel.meet`). -/
theorem composeBinOpAt_level_toMapClass (lop la lb : RelLevel) :
    (RelLevel.meet lop (RelLevel.meet la lb)).toMapClass
      = Param.MapClass.meet lop.toMapClass
          (Param.MapClass.meet la.toMapClass lb.toMapClass) := by
  rw [RelLevel.toMapClass_meet, RelLevel.toMapClass_meet]

/-! ## Reflection at the `embedding` level -/

/-- Reflection stated on the `Param` side (the primary form): membership in
    the class-registered embedding's `Param` relation reflects equality —
    the one-way graph equation becomes the two-way `↔` via
    `ReprEmbeddingClass.eq_iff`. -/
theorem transferIffParam {A α : Type u} [ReprEmbeddingClass A α] {a a' : A}
    {b : α} (h : (Param.paramOfEmbedding (A := A) (α := α)).R a b) :
    b = ReprMapClass.enc a' ↔ a = a' := by
  rw [← show (ReprMapClass.enc a : α) = b from h]
  exact ReprEmbeddingClass.eq_iff a a'

/-- Embedding-level reflection. At `embedding` level the encoding reflects
    equality, so the one-way transfer equation `enc a = b` becomes the two-way
    `b = enc a' ↔ a = a'`. This is what `embedding` provides over `map`: `map`
    transfers equality forward, while `embedding` (`ReprEmbeddingClass.eq_iff`)
    transfers it both ways. Derived from the `Param`-side primary form
    `transferIffParam`. -/
theorem transferIffAt {A α : Type u} [ReprEmbeddingClass A α] {a a' : A} {b : α}
    (h : RelatedAt RelLevel.embedding (ReprMapClass.enc : A → α) a b) :
    b = ReprMapClass.enc a' ↔ a = a' :=
  transferIffParam h.rel

/-! ## Demonstrations at explicit levels

A tiny self-contained registered operation over `Nat` keeps the file light while
exercising leaf resolution, single-op composition, and the `meet` of a
composite. -/

namespace LevelsDemo

/-- A trivially-realized `+` on `Nat` under the identity encoding, registered at
    `equiv` level (Nat ↔ Nat is a bijection). -/
instance natAddRelated :
    RelatedBinOpAt RelLevel.equiv (id : Nat → Nat) (· + ·) (· + ·) where
  comm _ _ := rfl

/-- Leaf resolution at an explicit level. -/
example (n : Nat) : RelatedAt RelLevel.equiv (id : Nat → Nat) n n := inferInstance

/-- Single registered operation: composition yields
    `meet equiv (meet equiv equiv) = equiv`. -/
example (m n : Nat) :
    RelatedAt (RelLevel.meet RelLevel.equiv
        (RelLevel.meet RelLevel.equiv RelLevel.equiv))
      (id : Nat → Nat) (m + n) (m + n) := inferInstance

/-- The composite of an `equiv`-level op with leaves still yields the underlying
    equation through `transferRelAt`, regardless of the meet-computed level. -/
example (m n : Nat) : (id : Nat → Nat) (m + n) = m + n :=
  transferRelAt (inferInstance :
    RelatedAt (RelLevel.meet RelLevel.equiv
        (RelLevel.meet RelLevel.equiv RelLevel.equiv))
      (id : Nat → Nat) (m + n) (m + n))

end LevelsDemo

end Transfer
