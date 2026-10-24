/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedFamily
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Binomial extensions on coefficient families

An element of `F[X]/(X^n − ξ)` is a coefficient family `Fin n → F`, and an
implementation carries it as an array of `n` encoded coefficients. This file
defines the product of that quotient on coefficient families, identifies it with
the product of `AdjoinRoot (X ^ n - C ξ)`, and lifts the squares of an element
encoding `enc : A → α` to arrays of coefficients.

## Main definitions

* `sumOp add zero m f`: the left fold `f 0 + ⋯ + f (m − 1)` over an arbitrary
  addition and zero.
* `binomMulOp add mul zero ξ n x y k`: coefficient `k` of the binomial product of
  two readers `x y : ℕ → A`, over arbitrary operations; `famCoeff zero x` reads a
  family `Fin n → A`, with `zero` out of range.
* `binomMul ξ x y`: the binomial product on `Fin n → F` over a semiring,
  `(binomMul ξ x y) k = Σ_{i+j=k} x i * y j + ξ * Σ_{i+j=k+n} x i * y j`.
* `extPoly x`: the polynomial `Σ i, C (x i) * X ^ i`.
* `extEnc enc x`: the array of encodings of a family.
* `binomMulW addW mulW zeroW ξW n a b`: the binomial product on arrays of encoded
  coefficients.

## Main results

* `binomMulOp_eq_binomMul`: over a semiring the fold form is `binomMul`.
* `sum_binomMul_mul_pow`: for a ring homomorphism `φ` and `r` with `r ^ n = φ ξ`,
  the evaluation `x ↦ Σ i, φ (x i) * r ^ i` sends `binomMul ξ` to the product.
* `mk_extPoly_binomMul`: in `AdjoinRoot (X ^ n - C ξ)`, the class of
  `extPoly (binomMul ξ x y)` is the product of the classes of `extPoly x` and
  `extPoly y`.
* `sumOp_map`, `binomMulOp_map`: an encoding that commutes with the operations
  commutes with the folds.
* `extAdd`, `extSub`, `extNeg`, `extSMul`, `extBinomMul`: the squares along
  `extEnc enc` for the coefficientwise sum, difference and negation
  (`Array.zipWith`, `Array.map`), the multiple by a base element
  (`Array.map (mulW c')`) and the binomial product (`binomMulW`), each from the
  squares of `enc`.
* `RelatedArray.zipWith`, `RelatedArray.map`, `RelatedArray.binomMulOp`,
  `RelatedArray.binomMul`, `RelatedArray.ofFn_related`: the same rules for arrays
  related entry by entry, and the rule for an array given by its entries.
* `RelatedArray.related_extEnc`: a related array of size `n` is the encoding of
  its family.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

universe u

open Polynomial

/-! ## Folds over arbitrary operations -/

section Op

variable {A α : Type u}

/-- The left fold `f 0 + ⋯ + f (m − 1)` over an addition `add` and a zero `zero`. -/
def sumOp (add : A → A → A) (zero : A) : ℕ → (ℕ → A) → A
  | 0, _ => zero
  | m + 1, f => add (sumOp add zero m f) (f m)

/-- Coefficient `k` of the product in `A[v]/(vⁿ − ξ)` of two readers, over
    arbitrary operations: the fold over `i j < n` of `x i * y j` when `i + j = k`,
    of `ξ * (x i * y j)` when `i + j = k + n`, and of `zero` otherwise. -/
def binomMulOp (add mul : A → A → A) (zero ξ : A) (n : ℕ) (x y : ℕ → A) (k : ℕ) : A :=
  sumOp add zero n fun i => sumOp add zero n fun j =>
    if i + j = k then mul (x i) (y j)
    else if i + j = k + n then mul ξ (mul (x i) (y j))
    else zero

/-- The reader of a family: entry `i` in range, `zero` out of range. -/
def famCoeff {n : ℕ} (zero : A) (x : Fin n → A) (i : ℕ) : A :=
  if h : i < n then x ⟨i, h⟩ else zero

/-- The reader of a family at an in-range position. -/
theorem famCoeff_of_lt {n : ℕ} (zero : A) (x : Fin n → A) {i : ℕ} (h : i < n) :
    famCoeff zero x i = x ⟨i, h⟩ := dite_eq_left h

/-- The reader of a family at a position of `Fin n`. -/
@[simp] theorem famCoeff_val {n : ℕ} (zero : A) (x : Fin n → A) (i : Fin n) :
    famCoeff zero x i = x i := dite_eq_left i.isLt

/-- The fold depends only on the summands below the bound. -/
theorem sumOp_congr (add : A → A → A) (zero : A) (m : ℕ) {f g : ℕ → A}
    (h : ∀ i, i < m → f i = g i) : sumOp add zero m f = sumOp add zero m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [sumOp]
    rw [ih fun i hi => h i (Nat.lt_succ_of_lt hi), h m (Nat.lt_succ_self m)]

/-- The binomial product depends only on the entries of the readers below `n`. -/
theorem binomMulOp_congr (add mul : A → A → A) (zero ξ : A) (n : ℕ) {x x' y y' : ℕ → A}
    (hx : ∀ i, i < n → x i = x' i) (hy : ∀ i, i < n → y i = y' i) (k : ℕ) :
    binomMulOp add mul zero ξ n x y k = binomMulOp add mul zero ξ n x' y' k := by
  unfold binomMulOp
  refine sumOp_congr _ _ _ fun i hi => sumOp_congr _ _ _ fun j hj => ?_
  rw [hx i hi, hy j hj]

/-- An encoding that commutes with the addition and the zero commutes with the
    fold. -/
theorem sumOp_map (enc : A → α) {add : A → A → A} {addW : α → α → α} {zero : A} {zeroW : α}
    (hadd : ∀ a b, enc (add a b) = addW (enc a) (enc b)) (hzero : enc zero = zeroW)
    (m : ℕ) (f : ℕ → A) :
    enc (sumOp add zero m f) = sumOp addW zeroW m fun i => enc (f i) := by
  induction m with
  | zero => exact hzero
  | succ m ih => simp only [sumOp, hadd, ih]

/-- An encoding that commutes with the addition, the multiplication, the zero and
    the constant `ξ` commutes with the binomial product. -/
theorem binomMulOp_map (enc : A → α) {add mul : A → A → A} {addW mulW : α → α → α}
    {zero ξ : A} {zeroW ξW : α}
    (hadd : ∀ a b, enc (add a b) = addW (enc a) (enc b))
    (hmul : ∀ a b, enc (mul a b) = mulW (enc a) (enc b))
    (hzero : enc zero = zeroW) (hξ : enc ξ = ξW) (n : ℕ) (x y : ℕ → A) (k : ℕ) :
    enc (binomMulOp add mul zero ξ n x y k)
      = binomMulOp addW mulW zeroW ξW n (fun i => enc (x i)) (fun i => enc (y i)) k := by
  unfold binomMulOp
  rw [sumOp_map enc hadd hzero]
  refine sumOp_congr _ _ _ fun i _ => ?_
  rw [sumOp_map enc hadd hzero]
  refine sumOp_congr _ _ _ fun j _ => ?_
  split_ifs <;> simp only [hmul, hξ, hzero]

end Op

/-! ## The binomial product over a semiring -/

section Semiring

variable {F : Type u} [Semiring F] {n : ℕ}

/-- The product of `F[X]/(X^n − ξ)` on coefficient families. -/
def binomMul (ξ : F) (x y : Fin n → F) : Fin n → F := fun k =>
  (∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) + j = k then x i * y j else 0)
    + ξ * ∑ i : Fin n, ∑ j : Fin n, if (i : ℕ) + j = k + n then x i * y j else 0

/-- Over a semiring the fold is the finite sum. -/
theorem sumOp_eq_sum (m : ℕ) (f : ℕ → F) :
    sumOp (· + ·) 0 m f = ∑ i ∈ Finset.range m, f i := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [sumOp, ih, Finset.sum_range_succ]

/-- Over a semiring the fold form of the binomial product is `binomMul`. -/
theorem binomMulOp_eq_binomMul (ξ : F) (x y : Fin n → F) (k : Fin n) :
    binomMulOp (· + ·) (· * ·) 0 ξ n (famCoeff 0 x) (famCoeff 0 y) k = binomMul ξ x y k := by
  have hn : 0 < n := k.pos
  unfold binomMulOp binomMul
  simp only [sumOp_eq_sum, Finset.sum_range, famCoeff_val, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h1 h2 <;> first | omega | simp

end Semiring

/-! ## The product of the quotient by `X ^ n - C ξ` -/

section Eval

variable {F R : Type*} [CommSemiring F] [CommSemiring R] {n : ℕ}

/-- Evaluation of coefficient families at an `n`-th root `r` of `ξ` sends
    `binomMul ξ` to the product. -/
theorem sum_binomMul_mul_pow (φ : F →+* R) (ξ : F) (r : R) (hr : r ^ n = φ ξ)
    (x y : Fin n → F) :
    ∑ k : Fin n, φ (binomMul ξ x y k) * r ^ (k : ℕ)
      = (∑ i : Fin n, φ (x i) * r ^ (i : ℕ)) * ∑ j : Fin n, φ (y j) * r ^ (j : ℕ) := by
  have key : ∀ i j : Fin n,
      ∑ k : Fin n, ((if (i : ℕ) + j = k then φ (x i * y j) else 0)
          + φ ξ * (if (i : ℕ) + j = k + n then φ (x i * y j) else 0)) * r ^ (k : ℕ)
        = φ (x i) * r ^ (i : ℕ) * (φ (y j) * r ^ (j : ℕ)) := by
    intro i j
    by_cases h : (i : ℕ) + j < n
    · rw [Finset.sum_eq_single ⟨(i : ℕ) + j, h⟩]
      · have h2 : ¬ (i : ℕ) + j = (i : ℕ) + j + n := by omega
        simp only [h2, ite_true, ite_false, mul_zero, add_zero, map_mul, pow_add]
        ring
      · intro k _ hk
        have h1 : ¬ (i : ℕ) + j = k := fun e => hk (Fin.ext e.symm)
        have h2 : ¬ (i : ℕ) + j = k + n := by omega
        simp [h1, h2]
      · simp
    · have hlt : (i : ℕ) + j - n < n := by omega
      rw [Finset.sum_eq_single ⟨(i : ℕ) + j - n, hlt⟩]
      · have h1 : ¬ (i : ℕ) + j = (i : ℕ) + j - n := by omega
        have h2 : (i : ℕ) + j = (i : ℕ) + j - n + n := by omega
        have h3 : r ^ (i : ℕ) * r ^ (j : ℕ) = φ ξ * r ^ ((i : ℕ) + j - n) := by
          rw [← pow_add, ← hr, ← pow_add]; congr 1; omega
        simp only [h1, ← h2, ite_true, ite_false, zero_add, map_mul]
        calc φ ξ * (φ (x i) * φ (y j)) * r ^ ((i : ℕ) + j - n)
            = φ (x i) * φ (y j) * (φ ξ * r ^ ((i : ℕ) + j - n)) := by ring
          _ = φ (x i) * r ^ (i : ℕ) * (φ (y j) * r ^ (j : ℕ)) := by rw [← h3]; ring
      · intro k _ hk
        have h1 : ¬ (i : ℕ) + j = k := by omega
        have h2 : ¬ (i : ℕ) + j = k + n := fun e => hk (Fin.ext (by simp; omega))
        simp [h1, h2]
      · simp
  calc ∑ k : Fin n, φ (binomMul ξ x y k) * r ^ (k : ℕ)
      = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          ((if (i : ℕ) + j = k then φ (x i * y j) else 0)
            + φ ξ * (if (i : ℕ) + j = k + n then φ (x i * y j) else 0)) * r ^ (k : ℕ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [binomMul, map_add, map_mul, map_sum, Finset.mul_sum, Finset.sum_mul,
          add_mul, Finset.sum_add_distrib, apply_ite φ, map_zero]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          ((if (i : ℕ) + j = k then φ (x i * y j) else 0)
            + φ ξ * (if (i : ℕ) + j = k + n then φ (x i * y j) else 0)) * r ^ (k : ℕ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by simp only [key, Finset.sum_mul_sum]

end Eval

section AdjoinRoot

variable {F : Type*} [CommRing F] {n : ℕ}

/-- The polynomial with the coefficients of a family. -/
noncomputable def extPoly (x : Fin n → F) : F[X] := ∑ i : Fin n, C (x i) * X ^ (i : ℕ)

/-- In `AdjoinRoot (X ^ n - C ξ)` the class of `extPoly (binomMul ξ x y)` is the
    product of the classes of `extPoly x` and `extPoly y`. -/
theorem mk_extPoly_binomMul (ξ : F) (x y : Fin n → F) :
    AdjoinRoot.mk (X ^ n - C ξ) (extPoly (binomMul ξ x y))
      = AdjoinRoot.mk (X ^ n - C ξ) (extPoly x) * AdjoinRoot.mk (X ^ n - C ξ) (extPoly y) := by
  have hr : (AdjoinRoot.root (X ^ n - C ξ : F[X])) ^ n = AdjoinRoot.of (X ^ n - C ξ) ξ := by
    have h := AdjoinRoot.mk_self (f := (X ^ n - C ξ : F[X]))
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have h := sum_binomMul_mul_pow (AdjoinRoot.of (X ^ n - C ξ : F[X])) ξ _ hr x y
  simpa only [extPoly, map_sum, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h

end AdjoinRoot

/-! ## Arrays of encoded coefficients -/

section Enc

variable {A α : Type u} {n : ℕ}

/-- The array of encodings of a coefficient family. -/
def extEnc (enc : A → α) (x : Fin n → A) : Array α := Array.ofFn fun i => enc (x i)

/-- The encoding of a family has one entry per coefficient. -/
@[simp] theorem size_extEnc (enc : A → α) (x : Fin n → A) : (extEnc enc x).size = n := by
  simp [extEnc]

/-- Entry `i` of the encoding of a family. -/
@[simp] theorem getElem_extEnc (enc : A → α) (x : Fin n → A) (i : ℕ)
    (h : i < (extEnc enc x).size) :
    (extEnc enc x)[i] = enc (x ⟨i, by simpa using h⟩) := by
  simp [extEnc]

/-- The encoding of a family is related to it entry by entry. -/
instance extEncRelated (enc : A → α) (x : Fin n → A) : RelatedArray enc x (extEnc enc x) :=
  RelatedArray.ofFn _ _

/-- The binomial product on arrays of encoded coefficients: entry `k` is
    `binomMulOp` of the word operations on the entries of `a` and `b`. -/
def binomMulW (addW mulW : α → α → α) (zeroW ξW : α) (n : ℕ) (a b : Array α) : Array α :=
  Array.ofFn (n := n) fun k =>
    binomMulOp addW mulW zeroW ξW n (fun i => a.getD i zeroW) (fun j => b.getD j zeroW) k

/-- The binomial product on arrays has `n` entries. -/
@[simp] theorem size_binomMulW (addW mulW : α → α → α) (zeroW ξW : α) (n : ℕ)
    (a b : Array α) : (binomMulW addW mulW zeroW ξW n a b).size = n := by
  simp [binomMulW]

namespace RelatedArray

variable {enc : A → α} {x y : Fin n → A} {a b : Array α}

/-- A related array of size `n` is the encoding of its family. -/
theorem related_extEnc [h : RelatedArray enc x a] (hs : a.size = n) :
    Related (extEnc enc) x a where
  rel := (eq_ofFn (enc := enc) (s := x) hs).symm

/-- Reading a related array with a default at an in-range position gives the
    encoding of the entry. -/
theorem getD_eq [h : RelatedArray enc x a] (k : ℕ) (hk : k < n) (d : α) :
    a.getD k d = enc (x ⟨k, hk⟩) := by
  have := h.getElem?_eq ⟨k, hk⟩
  simp only at this
  simp [Array.getD_eq_getD_getElem?, this]

/-- An array given by entries related to those of a family is related to the
    family. -/
theorem ofFn_related {f : Fin n → α} (h : ∀ i, Related enc (x i) (f i)) :
    RelatedArray enc x (Array.ofFn f) where
  getElem?_eq i := by simp [(h i).rel]

/-- The coefficientwise image of two related arrays under a registered binary
    operation is related to the coefficientwise operation. -/
theorem zipWith {op : A → A → A} {bop : α → α → α} [h : RelatedBinOp enc op bop]
    [hx : RelatedArray enc x a] [hy : RelatedArray enc y b] :
    RelatedArray enc (fun i => op (x i) (y i)) (Array.zipWith bop a b) where
  getElem?_eq i := by
    have ha := lt_size (enc := enc) (s := x) (a := a) i.isLt
    have hb := lt_size (enc := enc) (s := y) (a := b) i.isLt
    rw [Array.getElem?_eq_getElem (by simp only [Array.size_zipWith]; omega)]
    simp [getElem_eq (enc := enc) (s := x) i.val i.isLt,
      getElem_eq (enc := enc) (s := y) i.val i.isLt, h.comm]

/-- The coefficientwise image of a related array under a registered unary
    operation is related to the coefficientwise operation. -/
theorem map {op : A → A} {uop : α → α} [h : RelatedUnOp enc op uop]
    [hx : RelatedArray enc x a] :
    RelatedArray enc (fun i => op (x i)) (Array.map uop a) where
  getElem?_eq i := by
    simp [hx.getElem?_eq i, h.comm]

/-- The binomial product of two related arrays is related to the binomial product
    of the families, over arbitrary operations with which the encoding commutes. -/
theorem binomMulOp {add mul : A → A → A} {addW mulW : α → α → α} {zero ξ : A} {zeroW ξW : α}
    [hadd : RelatedBinOp enc add addW] [hmul : RelatedBinOp enc mul mulW]
    (hzero : Related enc zero zeroW) (hξ : Related enc ξ ξW)
    [RelatedArray enc x a] [RelatedArray enc y b] :
    RelatedArray enc
      (fun k : Fin n => Transfer.binomMulOp add mul zero ξ n (famCoeff zero x) (famCoeff zero y) k)
      (binomMulW addW mulW zeroW ξW n a b) where
  getElem?_eq k := by
    simp only [binomMulW, Array.getElem?_ofFn, k.isLt, dite_true]
    rw [binomMulOp_map enc hadd.comm hmul.comm hzero.rel hξ.rel]
    congr 1
    refine binomMulOp_congr _ _ _ _ _ (fun i hi => ?_) (fun i hi => ?_) _
    · rw [getD_eq (enc := enc) (x := x) i hi, famCoeff_of_lt _ _ hi]
    · rw [getD_eq (enc := enc) (x := y) i hi, famCoeff_of_lt _ _ hi]

/-- The binomial product of two related arrays over a semiring is related to
    `binomMul` of the families. -/
theorem binomMul [Semiring A] {addW mulW : α → α → α} {ξ : A} {zeroW ξW : α}
    [RelatedBinOp enc (· + ·) addW] [RelatedBinOp enc (· * ·) mulW]
    (hzero : Related enc 0 zeroW) (hξ : Related enc ξ ξW)
    [RelatedArray enc x a] [RelatedArray enc y b] :
    RelatedArray enc (Transfer.binomMul ξ x y) (binomMulW addW mulW zeroW ξW n a b) := by
  have h := binomMulOp (enc := enc) (x := x) (y := y) (a := a) (b := b)
    (add := (· + ·)) (mul := (· * ·)) (addW := addW) (mulW := mulW) hzero hξ
  simpa only [binomMulOp_eq_binomMul] using h

end RelatedArray

/-! ## Squares along `extEnc` -/

variable (enc : A → α)

/-- The coefficientwise sum along `extEnc enc`. -/
instance extAdd [Add A] (addW : α → α → α) [RelatedBinOp enc (· + ·) addW] :
    RelatedBinOp (extEnc enc (n := n)) (· + ·) (Array.zipWith addW) where
  comm x y :=
    (RelatedArray.related_extEnc (enc := enc)
      (h := RelatedArray.zipWith (op := (· + ·)) (bop := addW) (x := x) (y := y)) (by simp)).rel

/-- The coefficientwise difference along `extEnc enc`. -/
instance extSub [Sub A] (subW : α → α → α) [RelatedBinOp enc (· - ·) subW] :
    RelatedBinOp (extEnc enc (n := n)) (· - ·) (Array.zipWith subW) where
  comm x y :=
    (RelatedArray.related_extEnc (enc := enc)
      (h := RelatedArray.zipWith (op := (· - ·)) (bop := subW) (x := x) (y := y)) (by simp)).rel

/-- The coefficientwise negation along `extEnc enc`. -/
instance extNeg [Neg A] (negW : α → α) [RelatedUnOp enc (- ·) negW] :
    RelatedUnOp (extEnc enc (n := n)) (- ·) (Array.map negW) where
  comm x :=
    (RelatedArray.related_extEnc (enc := enc)
      (h := RelatedArray.map (op := (- ·)) (uop := negW) (x := x)) (by simp)).rel

/-- The multiple by a base element `c` along `extEnc enc`: every entry is
    multiplied by the encoding of `c`. -/
instance extSMul [Mul A] (mulW : α → α → α) [h : RelatedBinOp enc (· * ·) mulW]
    (c : A) (cW : α) [hc : Related enc c cW] :
    RelatedUnOp (extEnc enc (n := n)) (fun x => c • x) (Array.map (mulW cW)) where
  comm x := by
    have : RelatedUnOp enc (fun z => c * z) (mulW cW) := ⟨fun z => by rw [h.comm, hc.rel]⟩
    exact (RelatedArray.related_extEnc (enc := enc)
      (h := RelatedArray.map (op := fun z => c * z) (uop := mulW cW) (x := x)) (by simp)).rel

/-- The binomial product along `extEnc enc`. -/
instance extBinomMul [Semiring A] (addW mulW : α → α → α) (ξ : A) (zeroW ξW : α)
    [RelatedBinOp enc (· + ·) addW] [RelatedBinOp enc (· * ·) mulW]
    [hzero : Related enc 0 zeroW] [hξ : Related enc ξ ξW] :
    RelatedBinOp (extEnc enc (n := n)) (binomMul ξ) (binomMulW addW mulW zeroW ξW n) where
  comm x y :=
    (RelatedArray.related_extEnc (enc := enc)
      (h := RelatedArray.binomMul (x := x) (y := y) (addW := addW) (mulW := mulW) hzero hξ)
      (by simp)).rel

end Enc

end Transfer
