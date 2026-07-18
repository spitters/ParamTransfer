/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Matrix.Mul

/-!
# CoqEAL `seqmatrix` multiplication refinement — `List (List R)` row-col product

This file extends the CoqEAL `seqmatrix` add-refinement of `SeqMatrix.lean` from
addition to multiplication.

CoqEAL's `seqmatrix` refines MathComp matrices `'M[R]_(m,n)` to lists of lists.
`SeqMatrix.lean` ported the `Radd_seqmx` square (concrete row-wise `addMx`
refines the abstract entrywise add). Matrix *multiplication* is the next
refinement: it is a `foldl`-shaped dot-product of rows against columns. Here we
build the concrete row-major multiply `mulMx` and prove the **multiplication
refinement square**

  `entry (mulMx p ncols m n) i j = ∑ k : Fin p, entry m i k * entry n k j`

(the sum runs over the shared/contraction dimension `p`), under the well-formed
rectangular hypotheses that the row index is in range and the contracted row has
length `p`. This is the CoqEAL `Rmul_seqmx`-shaped square restricted to the
dimension-matching case — a correct restricted statement, as opposed to an
unproven fully-general one.

A matrix-vector product `A · v` is `mulMx` with a single-column right operand,
recorded as the specialization `matVec` / `getD_matVec`. The suite's frontier —
fast matrix multiply (`Strassen`), and the linear-solve, determinant, and
normal-form developments — is in the `CoqEAL` aggregator.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.SeqMatrixMul

variable {R : Type*} [NonUnitalNonAssocSemiring R]

/-- The CoqEAL `seqmatrix` refinement relation (re-stated here matching
    `SeqMatrix.entry`): a row-major list of lists denotes the abstract entry
    function `ℕ → ℕ → R`, with absent rows and entries `0`. -/
def entry (m : List (List R)) (i j : ℕ) : R := (m.getD i []).getD j 0

/-- List dot product `Σ pᵢ·qᵢ`, truncating at the shorter length. This is the
    inner fold that matrix multiplication contracts over. -/
def dotProd : List R → List R → R
  | [], _ => 0
  | _, [] => 0
  | a :: p, b :: q => a * b + dotProd p q

/-- **Dot-product refinement.** Over two length-`p` lists, the concrete
    `dotProd` equals the abstract finite sum of pointwise products. This is the
    induction-on-the-shared-dimension core that the multiply square reuses. -/
theorem dotProd_eq_sum (p : ℕ) (u v : List R)
    (hu : u.length = p) (hv : v.length = p) :
    dotProd u v = ∑ k : Fin p, u.getD k 0 * v.getD k 0 := by
  induction p generalizing u v with
  | zero =>
    have : u = [] := List.length_eq_zero_iff.mp hu
    subst this; simp [dotProd]
  | succ n ih =>
    match u, v with
    | a :: u', b :: v' =>
      have hu' : u'.length = n := by simpa using hu
      have hv' : v'.length = n := by simpa using hv
      rw [Fin.sum_univ_succ]
      simp only [dotProd, Fin.val_zero, Fin.val_succ, List.getD_cons_zero,
        List.getD_cons_succ]
      rw [ih u' v' hu' hv']

/-- Column `j` (first `p` rows) of a matrix `n`: the length-`p` list
    `[entry n 0 j, …, entry n (p-1) j]`. Materializing the column lets the
    row-col product reuse the row-shaped `dotProd`. -/
def column (n : List (List R)) (p j : ℕ) : List R :=
  (List.range p).map (fun k => entry n k j)

@[simp] theorem column_length (n : List (List R)) (p j : ℕ) :
    (column n p j).length = p := by simp [column]

theorem getD_column (n : List (List R)) (p j k : ℕ) (hk : k < p) :
    (column n p j).getD k 0 = entry n k j := by
  unfold column
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- **Concrete (computational) row-major matrix multiply.** Row `i` of the
    product is the length-`ncols` list whose `j`-th entry is the dot product of
    row `i` of `m` with column `j` of `n`; `p` is the shared (contraction)
    dimension and `ncols` the column count of the result. -/
def mulMx (p ncols : ℕ) (m n : List (List R)) : List (List R) :=
  m.map (fun r => (List.range ncols).map (fun j => dotProd r (column n p j)))

/-- Row `i` of `mulMx` (in range) is the explicit map of dot products. -/
theorem getD_mulMx_row (p ncols : ℕ) (m n : List (List R)) (i : ℕ)
    (hi : i < m.length) :
    (mulMx p ncols m n).getD i [] =
      (List.range ncols).map (fun j => dotProd (m.getD i []) (column n p j)) := by
  unfold mulMx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  simp

/-- **The CoqEAL `Rmul_seqmx` refinement square (well-formed case).** The
    concrete row-col list multiply `mulMx` refines the abstract entrywise matrix
    product: entry `(i,j)` is the sum over the shared dimension `p` of
    `entry m i k * entry n k j`. Hypotheses pin the well-formed rectangular
    shape — the result row `i` is present (`hi`), the output has a `j`-th column
    (`hj`), and the contracted row `i` of `m` has length `p` (`hrow`). -/
theorem entry_mulMx (p ncols : ℕ) (m n : List (List R)) (i j : ℕ)
    (hi : i < m.length) (hj : j < ncols) (hrow : (m.getD i []).length = p) :
    entry (mulMx p ncols m n) i j = ∑ k : Fin p, entry m i k * entry n k j := by
  unfold entry
  rw [getD_mulMx_row p ncols m n i hi]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some]
  rw [dotProd_eq_sum p _ _ hrow (column_length n p j)]
  apply Finset.sum_congr rfl
  intro x _
  rw [getD_column n p j x x.isLt]
  rfl

/-- Functional form of the multiply square (over the fixed in-range row `i`,
    in-bounds columns, well-formed contracted row) — the commuting square the
    `ReprTransfer` registry consumes (concrete `mulMx` ↦ abstract entrywise
    product). -/
theorem entry_mulMx_fun (p ncols : ℕ) (m n : List (List R)) (i : ℕ)
    (hi : i < m.length) (hrow : (m.getD i []).length = p) :
    ∀ j, j < ncols →
      entry (mulMx p ncols m n) i j = ∑ k : Fin p, entry m i k * entry n k j :=
  fun j hj => entry_mulMx p ncols m n i j hi hj hrow

/-! ## Specialization: matrix-vector product

A matrix-vector product `A · v` is `mulMx` with a single-column right operand. We
give the direct form: the concrete `matVec` maps each row of `A` to its dot
product with `v`, and refines the abstract matrix-vector product
`(A·v)_i = ∑_k A_{i,k} v_k`. -/

/-- Concrete matrix-vector product: each row of `A` dotted with `v`. -/
def matVec (A : List (List R)) (v : List R) : List R :=
  A.map (fun r => dotProd r v)

/-- **Matrix-vector refinement square (well-formed case).** The `i`-th entry of
    the concrete `A · v` equals the abstract sum `∑ k, A_{i,k} v_k` over the
    shared dimension `p`, given the row is in range, the row has length `p`, and
    `v` has length `p`. -/
theorem getD_matVec (p : ℕ) (A : List (List R)) (v : List R) (i : ℕ)
    (hi : i < A.length) (hrow : (A.getD i []).length = p) (hv : v.length = p) :
    (matVec A v).getD i 0 = ∑ k : Fin p, (A.getD i []).getD k 0 * v.getD k 0 := by
  have hrow' : A[i] = A.getD i [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  unfold matVec
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi]
  simp only [Option.map_some, Option.getD_some, hrow']
  exact dotProd_eq_sum p _ _ hrow hv

/-! ## Agreement with Mathlib `Matrix.mulVec`

The matrix-vector refinement square above (`getD_matVec`) relates the concrete
`List`-rep `matVec` to a raw `Finset` sum `∑ k, A_{i,k} v_k`. We now turn that
into the *real linear-algebra operation*: the abstract matrix-vector product
`Matrix.mulVec` of Mathlib, under the canonical conversion from the seq-matrix
representation to a `Matrix (Fin m) (Fin p) R` and from the coefficient `List`
to a `Fin p → R` vector.

This certifies the concrete matrix-vector product as Mathlib's `Matrix.mulVec`
under the canonical conversions — the data refinement carried up to the real
linear-algebra operation.
-/

/-- Convert a seq-matrix `A : List (List R)` to an abstract
    `Matrix (Fin m) (Fin p) R` via the entry function. -/
def toMatrix (A : List (List R)) (m p : ℕ) : Matrix (Fin m) (Fin p) R :=
  Matrix.of (fun i j => entry A i.val j.val)

/-- Convert a coefficient `List R` to an abstract column vector `Fin p → R`. -/
def toVec (v : List R) (p : ℕ) : Fin p → R := fun j => v.getD j.val 0

/-- **Matrix-vector refinement = Mathlib `Matrix.mulVec`.** Under the canonical
    seq-matrix → `Matrix` and `List` → `Fin p → R` conversions, the `i`-th entry
    of the concrete `matVec A v` equals the abstract `Matrix.mulVec` of the
    converted matrix applied to the converted vector — the data refinement carried
    up to the real linear-algebra operation. -/
theorem getD_matVec_eq_mulVec (m p : ℕ) (A : List (List R)) (v : List R) (i : ℕ)
    (hi : i < A.length) (hrow : (A.getD i []).length = p) (hv : v.length = p)
    (him : i < m) :
    (matVec A v).getD i 0 = (toMatrix A m p).mulVec (toVec v p) ⟨i, him⟩ := by
  rw [getD_matVec p A v i hi hrow hv]
  rw [Matrix.mulVec_eq_sum]
  simp only [toMatrix, toVec, Matrix.of_apply, Matrix.transpose_apply,
    Finset.sum_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  rfl

end Transfer.Examples.CoqEAL.SeqMatrixMul
