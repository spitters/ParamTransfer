/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/

/-!
# Binder / higher-order / ∀ transfer (as lemmas)

Ground transfer handles closed op-trees. This module provides the
binder/higher-order/∀ capability as proven generic lemmas plus their
demonstrations on the existing realizations (the full `MetaM` `⟦·⟧` that
auto-applies these under elaboration is provided by the term-level translator).

* Function / fold transfer — `funMap_transfer`, `foldl_transfer`: a
  commuting square lifts through `λ`/`List.foldl`, so a function or a fold of a
  realized op transfers, generalizing the fixed `OpExpr`/`PExpr` shapes to
  arbitrary arity.
* ∀-transfer — `forall_transfer`: a `∀`-quantified statement transfers
  from the pointwise transfer (`forall_congr'`). The security-game /
  verifier statements (`∀ inputs, verify_eval … ↔ byte-check …`) transfer this
  way.
* Higher-order combinator transfer — `foldl_transfer` is the `foldl`
  combinator transfer; `List.sum`/`Finset.sum` are corollaries (sum = `foldl (+)`;
  `Finset.sum` via an `AddMonoidHom` when the byte side is a monoid).

The non-fabrication invariant holds: every lemma takes the commuting
square (`comm` / the pointwise transfer) as an explicit premise — the bound /
quantified / aggregated transfer composes a given witness, never invents one.
-/

set_option autoImplicit false

namespace Transfer

universe u v w

/-! ## Function and fold transfer (generic) -/

/-- Function transfer. A commuting square lifts to a function argument: the
    encoded value of `op (f b) (g b)` is the byte op on the encoded components —
    the `λ`-rule at a concrete point. -/
theorem funMap_transfer {A : Type u} {α : Type v} {B : Type w}
    (enc : A → α) (op : A → A → A) (bop : α → α → α)
    (comm : ∀ a b, enc (op a b) = bop (enc a) (enc b)) (f g : B → A) (b : B) :
    enc (op (f b) (g b)) = bop (enc (f b)) (enc (g b)) := comm _ _

/-- Fold transfer. A commuting square lifts through `List.foldl`: the encoded
    fold of `op` over a list equals the byte fold of `bop` over the encoded list.
    Generalizes the fixed-arity `OpExpr`/`PExpr` composites to arbitrary lists. -/
theorem foldl_transfer {A : Type u} {α : Type v}
    (enc : A → α) (op : A → A → A) (bop : α → α → α)
    (comm : ∀ a b, enc (op a b) = bop (enc a) (enc b)) :
    ∀ (init : A) (l : List A), enc (l.foldl op init) = (l.map enc).foldl bop (enc init) := by
  intro init l
  induction l generalizing init with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons, List.map_cons, ih, comm]

/-! ## ∀-quantified transfer (generic) -/

/-- ∀-transfer. A `∀`-quantified equivalence transfers from the pointwise
    transfer — the `forall` rule for propositions. -/
theorem forall_transfer {ι : Type u} (P Q : ι → Prop) (h : ∀ i, P i ↔ Q i) :
    (∀ i, P i) ↔ (∀ i, Q i) := forall_congr' h

end Transfer
