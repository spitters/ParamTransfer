/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Strassen one-level 2×2 block multiplication identity

This file states and proves the classic Strassen fast-matrix-multiply identity
at one level over a `CommRing R`: the product of two `2×2` matrices can be
computed with **seven** scalar multiplications (`M1 … M7`) and a handful of
additions, rather than the naive eight. The result entries are recombinations
of the seven products, and they reproduce the ordinary matrix product `A * B`
(Mathlib `Matrix.mul`, i.e. `*`).

This is the matrix-multiplication-tail companion to the CoqEAL `seqmatrix`
multiply refinement of `SeqMatrixMul.lean`: that file establishes the *naive*
row-col multiply refinement square; here we record the *fast* (Strassen)
recombination identity for the base `2×2` case.

## Scope and the named residual

We prove only the **one-level** `2×2` block identity. Genuine recursive
Strassen — recursing on `2×2` *block* matrices down to a base case, with the
associated termination/complexity argument — is the named residual and is **not**
attempted here. The one-level identity is the algebraic heart of the recursion
(at the leaf the blocks are scalars), so it is the right deliverable to check;
the recursion bookkeeping is orthogonal library plumbing.

## API

* `Strassen.M1 … M7` — the seven Strassen products of the `2×2` entries.
* `Strassen.result` — the `2×2` matrix recombined from `M1 … M7`.
* `Strassen.result_eq_mul` — `result A B = A * B` (the verified identity).
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.Strassen

variable {R : Type*} [CommRing R]

/-- The seven Strassen products, computed from the entries of `A` and `B`
    (`2×2` matrices over a commutative ring). With `A = [[a11,a12],[a21,a22]]`
    and `B = [[b11,b12],[b21,b22]]` (`0`/`1`-indexed via `Fin 2`):

    * `M1 = (a11 + a22)(b11 + b22)`
    * `M2 = (a21 + a22) b11`
    * `M3 = a11 (b12 - b22)`
    * `M4 = a22 (b21 - b11)`
    * `M5 = (a11 + a12) b22`
    * `M6 = (a21 - a11)(b11 + b12)`
    * `M7 = (a12 - a22)(b21 + b22)` -/
def M1 (A B : Matrix (Fin 2) (Fin 2) R) : R := (A 0 0 + A 1 1) * (B 0 0 + B 1 1)
/-- Strassen product `M2 = (a21 + a22) b11`. -/
def M2 (A B : Matrix (Fin 2) (Fin 2) R) : R := (A 1 0 + A 1 1) * B 0 0
/-- Strassen product `M3 = a11 (b12 - b22)`. -/
def M3 (A B : Matrix (Fin 2) (Fin 2) R) : R := A 0 0 * (B 0 1 - B 1 1)
/-- Strassen product `M4 = a22 (b21 - b11)`. -/
def M4 (A B : Matrix (Fin 2) (Fin 2) R) : R := A 1 1 * (B 1 0 - B 0 0)
/-- Strassen product `M5 = (a11 + a12) b22`. -/
def M5 (A B : Matrix (Fin 2) (Fin 2) R) : R := (A 0 0 + A 0 1) * B 1 1
/-- Strassen product `M6 = (a21 - a11)(b11 + b12)`. -/
def M6 (A B : Matrix (Fin 2) (Fin 2) R) : R := (A 1 0 - A 0 0) * (B 0 0 + B 0 1)
/-- Strassen product `M7 = (a12 - a22)(b21 + b22)`. -/
def M7 (A B : Matrix (Fin 2) (Fin 2) R) : R := (A 0 1 - A 1 1) * (B 1 0 + B 1 1)

/-- The `2×2` result matrix recombined from the seven Strassen products:

    * `c11 = M1 + M4 - M5 + M7`
    * `c12 = M3 + M5`
    * `c21 = M2 + M4`
    * `c22 = M1 - M2 + M3 + M6` -/
def result (A B : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of (fun i j =>
    match i, j with
    | 0, 0 => M1 A B + M4 A B - M5 A B + M7 A B
    | 0, 1 => M3 A B + M5 A B
    | 1, 0 => M2 A B + M4 A B
    | 1, 1 => M1 A B - M2 A B + M3 A B + M6 A B)

/-- **Strassen one-level identity.** The seven-multiplication recombination
    `result A B` equals the ordinary matrix product `A * B` for `2×2` matrices
    over a commutative ring. -/
theorem result_eq_mul (A B : Matrix (Fin 2) (Fin 2) R) :
    result A B = A * B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [result, M1, M2, M3, M4, M5, M6, M7, Matrix.of_apply,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue, Fin.mk_zero,
      Fin.mk_one] <;> ring

end Transfer.Examples.CoqEAL.Strassen
