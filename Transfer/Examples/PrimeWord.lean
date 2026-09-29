/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Examples.MachineLimbField
public import Transfer.Congruence.ParamGuard

/-!
# The canonical prime word

An element `x : ZMod p` of a prime field with `p ≤ 2 ^ 64` is carried on one 64-bit
word as its canonical representative `BitVec.ofNat 64 x.val`. This module fixes that
encoding, `primeWord p`, and its decoder `primeDec p w = (w.toNat : ZMod p)`, which is
the relation of the single-limb retraction `Transfer.Param.limbFieldParam`: the
encoding is the section of that retraction (`primeWord_eq_section`), and a word is
related to a field element exactly when it decodes to it (`limbFieldParam_R_iff`).

The operation squares are registered along both maps.

* Along the encoding `primeWord p` (field to word) the squares are total: the
  reference word operations `addModW`, `subModW`, `mulModW`, `negModW` realize
  `+`, `-`, `*` and negation, and word equality and word order agree with equality
  and with the order of `ZMod.val`.
* Along the decoder `primeDec p` (word to field) the wrapping word operations
  realize the field operations under a no-overflow guard (`+`, `*`) or an order
  guard (`-`), and the reduction `modW p` realizes the identity. Word equality
  agrees with field equality on canonical words.

The instances take the bound `p ≤ 2 ^ 64` as a `Fact`, as
`Transfer.Param.instTransferDomLimbField` does.

## Main definitions

* `primeWord p`, `primeDec p`: the canonical encoding and its decoder.
* `addModW p`, `subModW p`, `mulModW p`, `negModW p`, `modW p`: the reference word
  operations modulo `p`.

## Main results

* `primeWord_toNat`, `primeWord_injective`, `eq_primeWord_of_toNat`,
  `primeDec_primeWord`, `primeWord_primeDec`, `primeWord_natCast`: the encoding API.
* `addRelated`, `subRelated`, `mulRelated`, `negRelated`, `eqRelated`,
  `valLtRelated`: the total squares along `primeWord p`.
* `decAddRelatedOn`, `decMulRelatedOn`, `decSubRelatedOn`, `decModRelated`,
  `decEqRelatedOn`: the squares along `primeDec p`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.PrimeWord

open Transfer Transfer.Param

variable (p : ℕ)

/-- The canonical prime word: a field element as the 64-bit word of its canonical
    representative. -/
def primeWord (x : ZMod p) : BitVec 64 := BitVec.ofNat 64 x.val

/-- The decoder of the canonical prime word: a 64-bit word read modulo `p`. -/
def primeDec (w : BitVec 64) : ZMod p := (w.toNat : ZMod p)

/-- The word sum reduced modulo `p`. -/
def addModW (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((a.toNat + b.toNat) % p)

/-- The word difference modulo `p`, computed as `a + (p - b)` reduced modulo `p`. -/
def subModW (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((a.toNat + (p - b.toNat)) % p)

/-- The word product reduced modulo `p`. -/
def mulModW (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((a.toNat * b.toNat) % p)

/-- The word negation modulo `p`, computed as `p - a` reduced modulo `p`. -/
def negModW (a : BitVec 64) : BitVec 64 := BitVec.ofNat 64 ((p - a.toNat) % p)

/-- The reduction of a word modulo `p`. -/
def modW (a : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat % p)

variable {p}

/-! ## The encoding and the retraction -/

/-- The canonical prime word is the section of the retraction `limbFieldParam`. -/
theorem primeWord_eq_section [NeZero p] (hp : p ≤ 2 ^ 64) (x : ZMod p) :
    primeWord p x = (limbFieldParam p hp).bwd.map x := rfl

/-- A word is related to a field element by `limbFieldParam` exactly when it decodes
    to it. -/
theorem limbFieldParam_R_iff [NeZero p] (hp : p ≤ 2 ^ 64) (w : BitVec 64) (x : ZMod p) :
    (limbFieldParam p hp).R w x ↔ primeDec p w = x := Iff.rfl

/-- The value of the canonical prime word is the canonical representative. -/
theorem primeWord_toNat [NeZero p] (hp : p ≤ 2 ^ 64) (x : ZMod p) :
    (primeWord p x).toNat = x.val := by
  rw [primeWord, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt x) hp)

/-- The value of the canonical prime word is below `p`. -/
theorem primeWord_toNat_lt [NeZero p] (hp : p ≤ 2 ^ 64) (x : ZMod p) :
    (primeWord p x).toNat < p := by
  rw [primeWord_toNat hp]; exact ZMod.val_lt x

/-- The canonical prime word lies below the word of `p`. -/
theorem primeWord_lt [NeZero p] (hp : p < 2 ^ 64) (x : ZMod p) :
    primeWord p x < BitVec.ofNat 64 p := by
  rw [BitVec.lt_def, primeWord_toNat hp.le, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp]
  exact ZMod.val_lt x

/-- The canonical prime word is injective. -/
theorem primeWord_injective [NeZero p] (hp : p ≤ 2 ^ 64) :
    Function.Injective (primeWord p) := by
  intro x y h
  have := congrArg BitVec.toNat h
  rw [primeWord_toNat hp, primeWord_toNat hp] at this
  exact ZMod.val_injective p this

/-- A word whose value is `z.val` is the canonical prime word of `z`. -/
theorem eq_primeWord_of_toNat [NeZero p] (hp : p ≤ 2 ^ 64) (w : BitVec 64) (z : ZMod p)
    (h : w.toNat = z.val) : w = primeWord p z :=
  BitVec.eq_of_toNat_eq (by rw [h, primeWord_toNat hp])

/-- The canonical prime word of the cast of `n < p` is the word of `n`. -/
theorem primeWord_natCast [NeZero p] (n : ℕ) (h : n < p) :
    primeWord p (n : ZMod p) = BitVec.ofNat 64 n := by
  rw [primeWord, ZMod.val_natCast, Nat.mod_eq_of_lt h]

/-- Decoding the canonical prime word returns the field element. -/
theorem primeDec_primeWord [NeZero p] (hp : p ≤ 2 ^ 64) (x : ZMod p) :
    primeDec p (primeWord p x) = x := by
  rw [primeDec, primeWord_toNat hp, ZMod.natCast_zmod_val]

/-- The canonical prime word of a decoded word is its reduction modulo `p`. -/
theorem primeWord_primeDec [NeZero p] (w : BitVec 64) :
    primeWord p (primeDec p w) = modW p w := by
  rw [primeWord, primeDec, ZMod.val_natCast, modW]

/-- A word below `p` is the canonical prime word of its decoding. -/
theorem primeWord_primeDec_of_lt [NeZero p] (w : BitVec 64) (h : w.toNat < p) :
    primeWord p (primeDec p w) = w := by
  rw [primeWord_primeDec, modW, Nat.mod_eq_of_lt h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The canonical prime word is related to its field element by `limbFieldParam`. -/
theorem limbFieldParam_R_primeWord [NeZero p] (hp : p ≤ 2 ^ 64) (x : ZMod p) :
    (limbFieldParam p hp).R (primeWord p x) x :=
  primeDec_primeWord hp x

/-! ## Total squares along the encoding -/

section Encoding

variable [NeZero p] [hp : Fact (p ≤ 2 ^ 64)]

/-- `addModW p` realizes `+` along `primeWord p`. -/
instance addRelated : RelatedBinOp (primeWord p) (· + ·) (addModW p) where
  comm x y := by
    rw [addModW, primeWord_toNat hp.out, primeWord_toNat hp.out, primeWord, ZMod.val_add]

/-- `subModW p` realizes `-` along `primeWord p`. -/
instance subRelated : RelatedBinOp (primeWord p) (· - ·) (subModW p) where
  comm x y := by
    rw [subModW, primeWord_toNat hp.out, primeWord_toNat hp.out, primeWord]
    congr 1
    have hy := ZMod.val_lt y
    have hc : x - y = (((x.val + (p - y.val)) : ℕ) : ZMod p) := by
      rw [Nat.cast_add, Nat.cast_sub hy.le, ZMod.natCast_self, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val, zero_sub, sub_eq_add_neg]
    rw [hc, ZMod.val_natCast]

/-- `mulModW p` realizes `*` along `primeWord p`. -/
instance mulRelated : RelatedBinOp (primeWord p) (· * ·) (mulModW p) where
  comm x y := by
    rw [mulModW, primeWord_toNat hp.out, primeWord_toNat hp.out, primeWord, ZMod.val_mul]

/-- `negModW p` realizes negation along `primeWord p`. -/
instance negRelated : RelatedUnOp (primeWord p) (fun x => -x) (negModW p) where
  comm x := by
    rw [negModW, primeWord_toNat hp.out, primeWord]
    congr 1
    have hc : -x = (((p - x.val) : ℕ) : ZMod p) := by
      rw [Nat.cast_sub (ZMod.val_lt x).le, ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
    rw [hc, ZMod.val_natCast]

/-- Word equality agrees with field equality along `primeWord p`. -/
instance eqRelated :
    RelatedRelOn (primeWord p) (fun _ _ => True) (· = ·) (· = ·) where
  iff _ _ _ := (primeWord_injective hp.out).eq_iff.symm

/-- The word order agrees with the order of canonical representatives along
    `primeWord p`. -/
instance valLtRelated :
    RelatedRelOn (primeWord p) (fun _ _ => True) (fun x y => x.val < y.val) (· < ·) where
  iff x y _ := by rw [BitVec.lt_def, primeWord_toNat hp.out, primeWord_toNat hp.out]

end Encoding

/-! ## Guarded squares along the decoder -/

section Decoder

/-- The wrapping word sum realizes `+` along `primeDec p` when the sum does not
    overflow. -/
instance decAddRelatedOn :
    RelatedBinOpOn (primeDec p) (fun a b => a.toNat + b.toNat < 2 ^ 64) (· + ·) (· + ·) where
  comm a b h := by rw [primeDec, primeDec, primeDec, BitVec.toNat_add, Nat.mod_eq_of_lt h,
    Nat.cast_add]

/-- The wrapping word product realizes `*` along `primeDec p` when the product does
    not overflow. -/
instance decMulRelatedOn :
    RelatedBinOpOn (primeDec p) (fun a b => a.toNat * b.toNat < 2 ^ 64) (· * ·) (· * ·) where
  comm a b h := by rw [primeDec, primeDec, primeDec, BitVec.toNat_mul, Nat.mod_eq_of_lt h,
    Nat.cast_mul]

/-- The wrapping word difference realizes `-` along `primeDec p` when the subtrahend
    is at most the minuend. -/
instance decSubRelatedOn :
    RelatedBinOpOn (primeDec p) (fun a b => b.toNat ≤ a.toNat) (· - ·) (· - ·) where
  comm a b h := by
    rw [primeDec, primeDec, primeDec, BitVec.toNat_sub_of_le (BitVec.le_def.mpr h),
      Nat.cast_sub h]

/-- The reduction `modW p` realizes the identity along `primeDec p`. -/
instance decModRelated : RelatedUnOp (primeDec p) (modW p) id where
  comm a := by
    rw [primeDec, primeDec, modW, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mod_le _ _) a.isLt), ZMod.natCast_mod, id]

/-- Field equality agrees with word equality along `primeDec p` on words below
    `p`. -/
instance decEqRelatedOn [NeZero p] :
    RelatedRelOn (primeDec p) (fun a b => a.toNat < p ∧ b.toNat < p) (· = ·) (· = ·) where
  iff a b h := by
    constructor
    · rintro rfl; rfl
    · intro e
      rw [← primeWord_primeDec_of_lt a h.1, ← primeWord_primeDec_of_lt b h.2, e]

end Decoder

/-! ## Descent through the squares -/

/-- The decoded field expression `x * y + z` is the decoding of the wrapping word
    expression, under the no-overflow guards `param_guard` returns. -/
theorem primeDec_mul_add (a b c : BitVec 64) (h1 : a.toNat * b.toNat < 2 ^ 64)
    (h2 : (a * b).toNat + c.toNat < 2 ^ 64) :
    primeDec p (a * b + c) = primeDec p a * primeDec p b + primeDec p c := by
  param_guard

/-- A field expression over encoded operands, closed by `param_solve` along
    `primeWord p`. -/
theorem primeWord_mul_add [NeZero p] [Fact (p ≤ 2 ^ 64)] (x y z : ZMod p) :
    Related (primeWord p) (x * y + z)
      (addModW p (mulModW p (primeWord p x) (primeWord p y)) (primeWord p z)) := by
  param_solve

end Transfer.PrimeWord
