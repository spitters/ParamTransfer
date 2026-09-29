/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.Related
public import ReprTransfer

/-!
# Guarded squares

A guarded square is a commuting square that holds under a side condition on the
abstract operands:

* `RelatedBinOpOn enc P op bop`: `P x y → enc (op x y) = bop (enc x) (enc y)`;
* `RelatedUnOpOn enc P op uop`: `P x → enc (op x) = uop (enc x)`;
* `RelatedRelOn enc P r br`: `P x y → (r x y ↔ br (enc x) (enc y))`.

The guard of a binary square relates both operands, so it expresses conditions
such as `y ≤ x` (saturating subtraction against a wrapping one) or
`x + y < 2 ^ 64` (no overflow), which a pair of per-operand predicates cannot.
The guard is an `outParam`: the operation pair `(op, bop)` and the encoding
determine it, and instance resolution returns it.

A total square is the guarded square with guard `True`. The instances
`RelatedBinOp.toOn` and `RelatedUnOp.toOn` register every total square as a
guarded one, so the guarded descent rules also cover the total registry.

The composition rules `rcongrBinOpOn`, `rcongrUnOpOn` and `rcongrRelOn` take the
guard as an explicit hypothesis. Instance resolution cannot prove a guard, so
guarded composition is a theorem applied by the descent tactics (`param_solve`,
`param_guard`), which leave the guard to a discharger or as a goal.

`transfer_guard_disch` is the default guard discharger. It is an extensible
tactic: a later `macro_rules | `(tactic| transfer_guard_disch) => ...` adds an
alternative that is tried before the earlier ones.

`BinOpHomOn.toRelatedBinOpOn` turns a domain-restricted homomorphism of
`ReprTransfer` into a guarded square with guard `dom x ∧ dom y`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

universe u

/-- A guarded binary square: on operands satisfying `P`, the operation `bop`
    realizes `op` along `enc`. -/
class RelatedBinOpOn {A α : Type u} (enc : A → α) (P : outParam (A → A → Prop))
    (op : A → A → A) (bop : α → α → α) : Prop where
  /-- The commuting square under the guard. -/
  comm : ∀ x y, P x y → enc (op x y) = bop (enc x) (enc y)

/-- A guarded unary square: on operands satisfying `P`, the operation `uop`
    realizes `op` along `enc`. -/
class RelatedUnOpOn {A α : Type u} (enc : A → α) (P : outParam (A → Prop))
    (op : A → A) (uop : α → α) : Prop where
  /-- The commuting square under the guard. -/
  comm : ∀ x, P x → enc (op x) = uop (enc x)

/-- A guarded relation square: on operands satisfying `P`, the relation `br` on
    encodings agrees with the relation `r`. The encoding is an `outParam` as well,
    since a goal `r a b ↔ br a' b'` does not mention it. -/
class RelatedRelOn {A α : Type u} (enc : outParam (A → α)) (P : outParam (A → A → Prop))
    (r : A → A → Prop) (br : α → α → Prop) : Prop where
  /-- The relation square under the guard. -/
  iff : ∀ x y, P x y → (r x y ↔ br (enc x) (enc y))

/-- A total binary square is a guarded square with guard `True`. -/
instance RelatedBinOp.toOn {A α : Type u} (enc : A → α) (op : A → A → A) (bop : α → α → α)
    [h : RelatedBinOp enc op bop] : RelatedBinOpOn enc (fun _ _ => True) op bop where
  comm x y _ := h.comm x y

/-- A total unary square is a guarded square with guard `True`. -/
instance RelatedUnOp.toOn {A α : Type u} (enc : A → α) (op : A → A) (uop : α → α)
    [h : RelatedUnOp enc op uop] : RelatedUnOpOn enc (fun _ => True) op uop where
  comm x _ := h.comm x

/-- A guarded binary square whose guard holds everywhere is a total square. -/
theorem RelatedBinOpOn.toRelatedBinOp {A α : Type u} {enc : A → α} {P : A → A → Prop}
    {op : A → A → A} {bop : α → α → α} (h : RelatedBinOpOn enc P op bop)
    (hP : ∀ x y, P x y) : RelatedBinOp enc op bop where
  comm x y := h.comm x y (hP x y)

/-- A guarded unary square whose guard holds everywhere is a total square. -/
theorem RelatedUnOpOn.toRelatedUnOp {A α : Type u} {enc : A → α} {P : A → Prop}
    {op : A → A} {uop : α → α} (h : RelatedUnOpOn enc P op uop)
    (hP : ∀ x, P x) : RelatedUnOp enc op uop where
  comm x := h.comm x (hP x)

/-- Guarded binary composition: from related operands and the guard on the
    abstract operands, `bop a' b'` is the encoding of `op a b`. -/
theorem rcongrBinOpOn {A α : Type u} (enc : A → α) {P : A → A → Prop}
    (op : A → A → A) (bop : α → α → α) {a b : A} {a' b' : α}
    [h : RelatedBinOpOn enc P op bop] (ha : Related enc a a') (hb : Related enc b b')
    (hg : P a b) : Related enc (op a b) (bop a' b') where
  rel := by rw [h.comm a b hg, ha.rel, hb.rel]

/-- Guarded unary composition: from a related operand and the guard on the
    abstract operand, `uop a'` is the encoding of `op a`. -/
theorem rcongrUnOpOn {A α : Type u} (enc : A → α) {P : A → Prop}
    (op : A → A) (uop : α → α) {a : A} {a' : α}
    [h : RelatedUnOpOn enc P op uop] (ha : Related enc a a') (hg : P a) :
    Related enc (op a) (uop a') where
  rel := by rw [h.comm a hg, ha.rel]

/-- Guarded relation transfer: from related operands and the guard on the
    abstract operands, `r a b` holds exactly when `br a' b'` does. -/
theorem rcongrRelOn {A α : Type u} (enc : A → α) {P : A → A → Prop}
    (r : A → A → Prop) (br : α → α → Prop) {a b : A} {a' b' : α}
    [h : RelatedRelOn enc P r br] (ha : Related enc a a') (hb : Related enc b b')
    (hg : P a b) : r a b ↔ br a' b' := by
  rw [h.iff a b hg, ha.rel, hb.rel]

/-- A domain-restricted homomorphism `BinOpHomOn φ dom src tgt` of `ReprTransfer`
    is the guarded square along `φ` with guard `dom x ∧ dom y`. -/
theorem BinOpHomOn.toRelatedBinOpOn {α A : Type u} {φ : α → A} {dom : α → Prop}
    {src : α → α → α} {tgt : A → A → A} (H : ReprTransfer.BinOpHomOn φ dom src tgt) :
    RelatedBinOpOn φ (fun x y => dom x ∧ dom y) src tgt where
  comm x y hg := H.app_eq x y hg.1 hg.2

/-- The default discharger for the guards of guarded squares. Extensible: a
    `macro_rules` for `transfer_guard_disch` adds an alternative tried before the
    default one, `first | trivial | assumption | omega | bv_omega | decide`. -/
syntax "transfer_guard_disch" : tactic

macro_rules
  | `(tactic| transfer_guard_disch) =>
    `(tactic| first | trivial | assumption | omega | bv_omega | decide)

end Transfer
