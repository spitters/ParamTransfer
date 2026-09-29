/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Congruence.ParamGuard

/-!
# Guarded squares on machine words

The abstract side is `ℕ` with the operations of a Rust reference semantics that
does not wrap: saturating addition `satAdd64`, saturating (truncated)
subtraction `-` and the right shift `>>>`. The encoded side is `BitVec 64` with
the wrapping operations of a machine semantics. The encoding is
`BitVec.ofNat 64`. Each square holds only on a range:

* `satAdd64 x y` against wrapping `+`: when `x + y < 2 ^ 64`;
* `x - y` against wrapping `-`: when `y ≤ x`;
* `x >>> s` against `>>>` on words: when `x < 2 ^ 64` and `s < 64`.

Wrapping `+` against `ℕ` addition is total and registered as a `RelatedBinOp`.

The examples compose these squares through programs with `param_guard` and
`param_solve`, discharge the guards by the default discharger, by a supplied one,
or leave them as goals, and show the error for a subterm with no square.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.GuardedSquares

open Transfer

/-- Saturating addition on `u64` values, as Rust's `u64::saturating_add`. -/
def satAdd64 (x y : ℕ) : ℕ := min (x + y) (2 ^ 64 - 1)

/-- The encoding of a natural number as a 64-bit word. -/
abbrev enc64 : ℕ → BitVec 64 := BitVec.ofNat 64

/-- Wrapping addition realizes `ℕ` addition along `enc64`, with no guard. -/
instance addRelated : RelatedBinOp enc64 (· + ·) (· + ·) where
  comm x y := by apply BitVec.eq_of_toNat_eq; simp [Nat.add_mod]

/-- Wrapping addition realizes saturating addition when the sum does not
    overflow. -/
instance satAddRelatedOn :
    RelatedBinOpOn enc64 (fun x y => x + y < 2 ^ 64) satAdd64 (· + ·) where
  comm x y h := by
    have : satAdd64 x y = x + y := by unfold satAdd64; omega
    rw [this]; exact addRelated.comm x y

/-- Wrapping subtraction realizes truncated subtraction when the subtrahend is
    at most the minuend. -/
instance subRelatedOn : RelatedBinOpOn enc64 (fun x y => y ≤ x) (· - ·) (· - ·) where
  comm x y h := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_sub]
    omega

/-- The word right shift realizes the `ℕ` right shift on a value below `2 ^ 64`
    and a shift below `64`. -/
instance shrRelatedOn :
    RelatedBinOpOn enc64 (fun x s => x < 2 ^ 64 ∧ s < 64) (· >>> ·) (· >>> ·) where
  comm x s h := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight, BitVec.ushiftRight_eq',
      Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) h.1)

/-- One guarded square: saturating addition without overflow is wrapping
    addition. -/
theorem satAdd_wrapping (a b : ℕ) (h : a + b < 2 ^ 64) :
    enc64 (satAdd64 a b) = enc64 a + enc64 b := by
  param_guard

/-- Two guarded squares composed through a program: `(a - b) >>> s`. The guard
    `b ≤ a` of the subtraction and the guard `a - b < 2 ^ 64 ∧ s < 64` of the shift
    are closed by `omega` from the hypotheses. -/
theorem sub_shr (a b s : ℕ) (ha : a < 2 ^ 64) (hb : b ≤ a) (hs : s < 64) :
    enc64 ((a - b) >>> s) = (enc64 a - enc64 b) >>> enc64 s := by
  param_guard

/-- The same program as a `Related` goal, closed by `param_solve`. -/
theorem sub_shr_param_solve (a b s : ℕ) (ha : a < 2 ^ 64) (hb : b ≤ a) (hs : s < 64) :
    Related enc64 ((a - b) >>> s) ((enc64 a - enc64 b) >>> enc64 s) := by
  param_solve

/-- A total square and two guarded squares: `satAdd64 a b - (c + d)`. The guard
    of the subtraction mentions `satAdd64`, which `omega` does not unfold, so the
    discharger is supplied. -/
theorem satAdd_sub_add (a b c d : ℕ) (h : a + b < 2 ^ 64) (hc : c + d ≤ a + b) :
    enc64 (satAdd64 a b - (c + d)) = (enc64 a + enc64 b) - (enc64 c + enc64 d) := by
  param_guard (disch := first | omega | (unfold satAdd64; omega))

/-- A guard the discharger does not close is left as a goal: with the discharger
    `fail`, `param_guard` returns the guard `b ≤ a` of the subtraction. -/
theorem sub_guard_left (a b : ℕ) (h : b ≤ a) :
    enc64 (a - b) = enc64 a - enc64 b := by
  param_guard (disch := fail)
  guard_target =ₛ b ≤ a
  exact h

/-- The word comparison `<` agrees with `<` on `ℕ` for values below `2 ^ 64`. -/
instance ltRelatedOn :
    RelatedRelOn enc64 (fun x y => x < 2 ^ 64 ∧ y < 2 ^ 64) (· < ·) (· < ·) where
  iff x y h := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.1,
      Nat.mod_eq_of_lt h.2]

/-- A guarded relation square over a guarded operation: the comparison
    `a - b < c` is the word comparison of the encodings. -/
theorem sub_lt_iff (a b c : ℕ) (ha : a < 2 ^ 64) (hb : b ≤ a) (hc : c < 2 ^ 64) :
    a - b < c ↔ enc64 a - enc64 b < enc64 c := by
  param_guard

/-- A domain-restricted homomorphism of `ReprTransfer` as a guarded square:
    `BitVec.toNat` carries word addition to `ℕ` addition on words below `2 ^ 63`. -/
theorem toNat_add_homOn :
    ReprTransfer.BinOpHomOn (BitVec.toNat : BitVec 64 → ℕ) (fun x => x.toNat < 2 ^ 63)
      (· + ·) (· + ·) where
  app_eq x y hx hy := by rw [BitVec.toNat_add]; omega

/-- The guarded square obtained from `toNat_add_homOn`, used by `param_guard`. -/
theorem toNat_add_of_lt (x y : BitVec 64) (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    (x + y).toNat = x.toNat + y.toNat := by
  have := BinOpHomOn.toRelatedBinOpOn toNat_add_homOn
  param_guard (disch := exact ⟨hx, hy⟩)

/-! A subterm with no registered square: `a * b` against wrapping `*`. The error
names the leaf `Related enc64 (a * b) (enc64 a * enc64 b)`, not the root. -/

/--
error: param_guard: no registered square or leaf closes
  Related enc64 (a * b) (enc64 a * enc64 b)
abstract head: @HMul.hMul, encoded head: @HMul.hMul, encoding: enc64
-/
#guard_msgs in
example (a b c : ℕ) (h : c ≤ a * b) :
    enc64 (a * b - c) = enc64 a * enc64 b - enc64 c := by
  param_guard

end Transfer.GuardedSquares
