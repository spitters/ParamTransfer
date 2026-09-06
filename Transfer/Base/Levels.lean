/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Hierarchy.ParamLevel

/-!
# Relatedness levels — the 3-point view of the Trocq lattice

Trocq indexes each relation by a pair `(m, n)` of `MapClass` levels recording
how much structure the relation carries in each direction; the full 6-point
lattice (`map0 ⊑ map1 ⊑ {map2a, map2b} ⊑ map3 ⊑ map4`, with its order and
meet) lives in `Transfer.Hierarchy.ParamLevel`. That lattice is the **single
source of truth** for level arithmetic. This file supplies the coarse
three-point *view* of it used by the crypto encodings (which are embeddings,
never bijections):

  `map < embedding < equiv`

* `map` — the encoding transfers an equality forward (`a = a' → enc a = enc a'`);
  the image point is `map1` (a bare forward map).
* `embedding` — additionally reflects equality (injective), so equality
  transfers in both directions; the image point is `map3` (the graph of the
  encoding, both inclusions).
* `equiv` — a bijection (the univalence/SIP level the crypto encodings never
  reach); the image point is the coherent top `map4`.

`RelLevel.toMapClass` embeds the view into the lattice and `MapClass.view3`
retracts it (`view3_toMapClass`). The order `RelLevel.le` and the composite
level `RelLevel.meet` are **defined** as the images of the lattice order and
lattice meet under this view; the original three-point tables are recovered as
theorems (`le_iff_toNat`, `meet_eq_min`), so every consumer of the 3-point API
keeps its statements while the arithmetic is computed in the lattice.

The crucial operation is `meet`: a composite transfer (an op-tree assembled
from sub-transfers) supports only the weakest level of its parts, so the level
of a composite is the meet (the lower) of the component levels — computed as
the `MapClass` meet of the images (`toMapClass_meet`).
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

/-- The three relatedness levels — the univalence-free 3-point view of Trocq's
    `MapClass` lattice (see the module docstring; the embedding is
    `RelLevel.toMapClass`). Ordered `map < embedding < equiv`. -/
inductive RelLevel
  /-- A representation map: transfers equality forward only. -/
  | map
  /-- An embedding (injective map): transfers equality both ways. -/
  | embedding
  /-- An equivalence (bijection): the univalence/SIP level. -/
  | equiv
  deriving DecidableEq, Repr

namespace RelLevel

/-- Rank of a level, for the linear order (the 3-point compatibility form;
    the primary order is the `MapClass` lattice order via `toMapClass`). -/
def toNat : RelLevel → Nat
  | map => 0
  | embedding => 1
  | equiv => 2

/-- The reconciliation-table embedding of the 3-point view into the Trocq
    level lattice: a bare representation map carries a forward map (`map1`);
    an embedding's graph relation carries both inclusions (`map3`); the
    equivalence point is the coherent top (`map4`). -/
def toMapClass : RelLevel → Param.MapClass
  | .map => .map1
  | .embedding => .map3
  | .equiv => .map4

end RelLevel

/-- The coarsening retraction: every `MapClass` seen as a 3-point `RelLevel`
    (`map0`/`map1` are map-strength, `map2a`/`map2b`/`map3` are
    embedding-strength, `map4` is the equivalence level). -/
def Param.MapClass.view3 : Param.MapClass → RelLevel
  | .map0 | .map1 => .map
  | .map2a | .map2b | .map3 => .embedding
  | .map4 => .equiv

namespace RelLevel

/-- `RelLevel` is a 3-point view: `view3` retracts `toMapClass`. -/
@[simp] theorem view3_toMapClass (l : RelLevel) :
    l.toMapClass.view3 = l := by
  cases l <;> rfl

/-- The order on levels: `l₁ ≤ l₂` iff `l₁` is no stronger than `l₂` —
    **defined** as the `MapClass` lattice order on the images. -/
def le (l₁ l₂ : RelLevel) : Prop :=
  l₁.toMapClass.le l₂.toMapClass = true

instance : LE RelLevel := ⟨le⟩

/-- Old = new: the lattice-order definition of `le` agrees with the original
    3-point rank order. -/
theorem le_iff_toNat (l₁ l₂ : RelLevel) : le l₁ l₂ ↔ l₁.toNat ≤ l₂.toNat := by
  cases l₁ <;> cases l₂ <;> simp [le, toNat, toMapClass, Param.MapClass.le]

/-- The view embedding is monotone — definitionally, since `le` *is* the
    lattice order on the images. -/
theorem toMapClass_mono {l₁ l₂ : RelLevel} (h : l₁ ≤ l₂) :
    l₁.toMapClass.le l₂.toMapClass = true := h

/-- The meet (weaker) of two levels — the level a composite supports, given
    that it is only as strong as its weakest part. **Defined** as the view of
    the `MapClass` lattice meet of the images. -/
def meet (l₁ l₂ : RelLevel) : RelLevel :=
  (Param.MapClass.meet l₁.toMapClass l₂.toMapClass).view3

/-- Old = new: the lattice-computed `meet` agrees with the original 3-point
    table (the minimum in the rank order). -/
theorem meet_eq_min (l₁ l₂ : RelLevel) :
    meet l₁ l₂ = if l₁.toNat ≤ l₂.toNat then l₁ else l₂ := by
  cases l₁ <;> cases l₂ <;> rfl

/-- The view embedding is a meet-homomorphism: the 3-point meet computes the
    lattice meet on the image (the image `{map1, map3, map4}` is meet-closed,
    and `view3` retracts it). -/
theorem toMapClass_meet (l₁ l₂ : RelLevel) :
    (meet l₁ l₂).toMapClass
      = Param.MapClass.meet l₁.toMapClass l₂.toMapClass := by
  cases l₁ <;> cases l₂ <;> rfl

@[simp] theorem meet_comm (l₁ l₂ : RelLevel) : meet l₁ l₂ = meet l₂ l₁ := by
  cases l₁ <;> cases l₂ <;> rfl

@[simp] theorem meet_self (l : RelLevel) : meet l l = l := by
  cases l <;> rfl

theorem meet_le_left (l₁ l₂ : RelLevel) : meet l₁ l₂ ≤ l₁ := by
  cases l₁ <;> cases l₂ <;> (show le _ _; unfold le; decide)

theorem meet_le_right (l₁ l₂ : RelLevel) : meet l₁ l₂ ≤ l₂ := by
  cases l₁ <;> cases l₂ <;> (show le _ _; unfold le; decide)

@[simp] theorem meet_map_left (l : RelLevel) : meet map l = map := by
  cases l <;> rfl

@[simp] theorem meet_map_right (l : RelLevel) : meet l map = map := by
  cases l <;> rfl

end RelLevel

end Transfer
