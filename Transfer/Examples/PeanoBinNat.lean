/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.Hierarchy
public import Transfer.Base.Core
public import Mathlib.Data.Num.Lemmas

/-!
# The `peano_bin_nat` flagship, first-order slice

The Trocq flagship example (`peano_bin_nat.v`) transfers facts across the
binary-vs-unary natural-number equivalence `N ≃ nat`. The paper's headline is
that this needs no univalence. It splits into two parts of very different
difficulty; this module realizes the tractable one and describes the
harder one.

Mathlib's binary naturals are `Num` (with `PosNum`), and the cast `Num → ℕ`
(`Num.toNat`) is a ring homomorphism that is injective (`Num.to_nat_inj`) — i.e.
a `ReprEmbeddingClass Num ℕ` in the relation hierarchy. So:

## First-order arithmetic transfer (this file)

Every first-order arithmetic theorem over `Num` transfers from its `ℕ`
counterpart across the embedding: reflect the goal `f a b = g a b` through
`Num.to_nat_inj`, apply the cast with the homomorphism lemmas
(`Num.add_to_nat`/`Num.mul_to_nat`, the registered `@[transfer]` realizations), and
close with the `ℕ` fact. Commutativity, associativity and distributivity on `Num`
derive this way — the univalence-free first-order flagship the Trocq paper
stresses needs no UA. These are `Num` theorems with no `Num` arithmetic done by
hand; the work is entirely the transfer.

## The induction principle, manually transferred (this file)

The flagship's headline is transferring the induction principle
`∀ P : Num → Prop, P 0 → (∀ n, P n → P (n+1)) → ∀ n, P n` across the equivalence.
This file derives it as `binNatInduction : BinNatInductionTarget`, by transfer
along the bijection `Num ≃ ℕ`: to prove `∀ n : Num, P n`, rewrite
`n = Num.ofNat' (n : ℕ)` (the round-trip `Num.of_to_nat'`), generalize `(n : ℕ)`
and run `Nat`'s recursor, mapping each `ℕ` step back to `Num` through the decoder
(`num_ofNat'_succ : Num.ofNat' (k+1) = Num.ofNat' k + 1`). This is the recursor
pulled back along the equivalence — the manual instance of what the flagship
automates. It needs the full bijection, registered below as
`instance : ReprEquivClass Num ℕ` (Trocq's top `equiv` level, which `Num`/`ℕ`
reach because the cast is bijective, unlike the crypto byte encodings).

What is not done here is the MetaM motive
synthesis that produces this transfer automatically for an arbitrary dependent
motive `P : Num → Type`. That quantifies over a motive with both covariant and
contravariant occurrences, so the automatic route needs the relation on
`Num → Type` (a parametricity `Param` of types) and the `(m,n)` level inference
that computes the minimal relation level each subterm requires. That engine is
not implemented here (no Lean/Mathlib precedent). This file provides the manual
recursor transfer; `BinNatInductionTarget` records its statement.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.PeanoBinNat

open Transfer

/-! ## The embedding `Num ↪ ℕ` as a relation-hierarchy instance -/

/-- The binary naturals embed into the unary naturals via the (injective) cast
    `(↑· : Num → ℕ)`. This is a `ReprEmbeddingClass` — the level at which a
    decidable equality transfers in both directions. -/
instance : ReprEmbeddingClass Num ℕ where
  enc := fun m => (m : ℕ)
  enc_inj := fun {_ _} h => Num.to_nat_inj.mp h

-- The cast realizations, registered so the transfer machinery applies them.
attribute [transfer] Num.add_to_nat Num.mul_to_nat

/-! ## First-order arithmetic on `Num`, transferred from `ℕ` (no `Num` algebra by hand)

Each proof reflects through `Num.to_nat_inj`, applies the cast with the
homomorphism lemmas, and closes with the corresponding `ℕ` fact. -/

/-- Commutativity of `+` on `Num`, transferred from `Nat.add_comm`. -/
theorem num_add_comm (a b : Num) : a + b = b + a := by
  rw [← Num.to_nat_inj, Num.add_to_nat, Num.add_to_nat, Nat.add_comm]

/-- Commutativity of `*` on `Num`, transferred from `Nat.mul_comm`. -/
theorem num_mul_comm (a b : Num) : a * b = b * a := by
  rw [← Num.to_nat_inj, Num.mul_to_nat, Num.mul_to_nat, Nat.mul_comm]

/-- Associativity of `+` on `Num`, transferred from `Nat.add_assoc`. -/
theorem num_add_assoc (a b c : Num) : a + b + c = a + (b + c) := by
  rw [← Num.to_nat_inj]
  simp only [Num.add_to_nat, Nat.add_assoc]

/-- Associativity of `*` on `Num`, transferred from `Nat.mul_assoc`. -/
theorem num_mul_assoc (a b c : Num) : a * b * c = a * (b * c) := by
  rw [← Num.to_nat_inj]
  simp only [Num.mul_to_nat, Nat.mul_assoc]

/-- Left distributivity on `Num`, transferred from `Nat.mul_add`. -/
theorem num_mul_add (a b c : Num) : a * (b + c) = a * b + a * c := by
  rw [← Num.to_nat_inj]
  simp only [Num.mul_to_nat, Num.add_to_nat, Nat.mul_add]

/-- Right distributivity on `Num`, transferred from `Nat.add_mul`. -/
theorem num_add_mul (a b c : Num) : (a + b) * c = a * c + b * c := by
  rw [← Num.to_nat_inj]
  simp only [Num.mul_to_nat, Num.add_to_nat, Nat.add_mul]

/-- Left identity for `+` on `Num`, transferred from `Nat.zero_add`. -/
theorem num_zero_add (a : Num) : 0 + a = a := by
  rw [← Num.to_nat_inj]
  simp only [Num.add_to_nat, Num.cast_zero, Nat.zero_add]

/-- Right identity for `+` on `Num`, transferred from `Nat.add_zero`. -/
theorem num_add_zero (a : Num) : a + 0 = a := by
  rw [← Num.to_nat_inj]
  simp only [Num.add_to_nat, Num.cast_zero, Nat.add_zero]

/-- The `Num` order transferred from the `ℕ` order across the embedding:
    `a ≤ b` on `Num` iff `(a:ℕ) ≤ (b:ℕ)`. The embedding `Num ↪ ℕ` is an order
    embedding, so `≤`-facts transfer just like the equational ones. -/
theorem num_le_iff_to_nat_le (a b : Num) : a ≤ b ↔ (a : ℕ) ≤ (b : ℕ) :=
  Num.le_to_nat.symm

/-- Transitivity of `≤` on `Num`, transferred from `Nat.le_trans` through the
    order embedding. -/
theorem num_le_trans {a b c : Num} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [num_le_iff_to_nat_le] at hab hbc ⊢
  exact le_trans hab hbc

/-! ## The full equivalence `Num ≃ ℕ` as the top hierarchy level

The embedding above is in fact a bijection: `Num.ofNat'` decodes
`ℕ → Num` and round-trips on the encoding (`Num.of_to_nat'`). So — unlike the
crypto byte encodings, which are injective-but-not-surjective and therefore
bottom out at `ReprEmbeddingClass` — `Num ↪ ℕ` reaches Trocq's top
`equiv`-level relation. This is the structure the `peano_bin_nat` flagship's
automatic recursor transfer is built over. -/

/-- `Num ≃ ℕ` registered at the equivalence level of the hierarchy: `enc` is
    the cast `Num → ℕ`, `dec` is `Num.ofNat' : ℕ → Num`, and `dec_enc` is the
    round-trip `Num.of_to_nat'`. The top level the SIP/univalence route uses;
    `Num`/`ℕ` reach it because the cast is a bijection. -/
instance : ReprEquivClass Num ℕ where
  enc := fun m => (m : ℕ)
  enc_inj := fun {_ _} h => Num.to_nat_inj.mp h
  dec := Num.ofNat'
  dec_enc := Num.of_to_nat'

/-! ## The induction principle: statement, then the manual recursor transfer

`BinNatInductionTarget` names the `Num` induction principle as a proposition;
`binNatInduction` below proves it by transferring `Nat`'s recursor across the
`Num ≃ ℕ` equivalence. What is not done here is the MetaM motive synthesis
that would emit this proof automatically for an
arbitrary dependent motive (the Trocq `peano_bin_nat` one-liner), which needs
the relation on `Num → Type` and the `(m,n)` level inference `transfer` cannot
yet synthesize. -/

/-- The `Num` induction principle, named as a proposition. Proved below as
    `binNatInduction` by the manual recursor transfer across `Num ≃ ℕ`. -/
def BinNatInductionTarget : Prop :=
  ∀ (P : Num → Prop), P 0 → (∀ n : Num, P n → P (n + 1)) → ∀ n : Num, P n

/-- Round-trip helper: `Num.ofNat'` (the `ℕ → Num` decoder) maps through
    successor, `Num.ofNat' (k+1) = Num.ofNat' k + 1`. Via `Num.ofNat'_eq`
    (`Num.ofNat' n = ↑n`) this is `Nat.cast`-of-successor in `Num`. -/
theorem num_ofNat'_succ (k : ℕ) : Num.ofNat' (k + 1) = Num.ofNat' k + 1 := by
  simp only [Num.ofNat'_eq, Nat.cast_add, Nat.cast_one]

theorem binNatInduction : BinNatInductionTarget := by
  intro P h0 hstep n
  rw [← Num.of_to_nat' n]
  generalize (n : ℕ) = k
  induction k with
  | zero => simpa using h0
  | succ j ih => rw [num_ofNat'_succ]; exact hstep _ ih

end Transfer.PeanoBinNat
