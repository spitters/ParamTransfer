/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Gaussian elimination: single forward-elimination pivot step (refinement)

This file records **one** forward-elimination pivot step of Gaussian elimination
as a refinement statement on the Mathlib `Matrix` representation, and proves the
property the whole elimination relies on: the step **preserves the solution
set** of the linear system `A · x = b`.

A forward-elimination pivot step toward eliminating column entry `r` against
pivot row `p` replaces

* row `r` of the coefficient matrix `A` with `row r − c • row p`, and
* the target entry `b r` with `b r − c • b p`,

leaving every other row and target entry untouched. Because the modified
`r`-equation is exactly `(original r-equation) − c · (original p-equation)` and
the `p`-equation is unchanged, a vector `x` satisfies the new system iff it
satisfies the original one. That single-step solution-set invariance is what
the full elimination iterates.

This is the `CoqEAL` linear-solve / Gaussian-elimination tail flagged as a
residual in `SeqMatrixMul.lean`. Here we discharge the **single pivot step**;
the full forward sweep (choosing pivots, iterating over all rows, and the
back-substitution / termination argument) is the named residual and is **not**
attempted.

## API

* `pivotStepMat` — the coefficient matrix after one pivot step.
* `pivotStepRhs` — the target vector after one pivot step.
* `pivotStep_preserves_solution` — `x` solves the stepped system iff it solves
  the original one (the solution-set invariance).
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.GaussPivotStep

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The coefficient matrix after one forward-elimination pivot step: row `r` is
    replaced by `row r − c • row p`; all other rows are unchanged. -/
def pivotStepMat (A : Matrix n n R) (p r : n) (c : R) : Matrix n n R :=
  A.updateRow r (A r - c • A p)

/-- The target vector after one forward-elimination pivot step: entry `r` is
    replaced by `b r − c • b p`; all other entries are unchanged. -/
def pivotStepRhs (b : n → R) (p r : n) (c : R) : n → R :=
  Function.update b r (b r - c • b p)

/-- Off-pivot rows are unchanged by the step: for `i ≠ r`, the `i`-th equation
    of the stepped system is the `i`-th equation of the original. -/
theorem pivotStepMat_mulVec_ne (A : Matrix n n R) (p r : n) (c : R) (x : n → R)
    {i : n} (hi : i ≠ r) :
    (pivotStepMat A p r c).mulVec x i = A.mulVec x i := by
  simp [pivotStepMat, mulVec, Matrix.updateRow_ne hi]

/-- The pivot row `r` of the stepped system is the original `r`-equation minus
    `c` times the original `p`-equation. -/
theorem pivotStepMat_mulVec_self (A : Matrix n n R) (p r : n) (c : R)
    (x : n → R) :
    (pivotStepMat A p r c).mulVec x r =
      A.mulVec x r - c • A.mulVec x p := by
  simp only [pivotStepMat, mulVec, Matrix.updateRow_self, sub_dotProduct,
    smul_dotProduct]

/-- **Single pivot step preserves the solution set.** A vector `x` satisfies the
    stepped system `pivotStepMat A p r c · x = pivotStepRhs b p r c` iff it
    satisfies the original system `A · x = b`. This is the solution-set
    invariance that the full Gaussian forward sweep iterates. -/
theorem pivotStep_preserves_solution (A : Matrix n n R) (b : n → R)
    (p r : n) (c : R) (hpr : p ≠ r) (x : n → R) :
    (pivotStepMat A p r c).mulVec x = pivotStepRhs b p r c ↔
      A.mulVec x = b := by
  rw [funext_iff, funext_iff]
  constructor
  · intro h i
    -- From the unchanged pivot-`p` equation we recover `A.mulVec x p = b p`.
    have hp := h p
    rw [pivotStepMat_mulVec_ne A p r c x hpr,
      pivotStepRhs, Function.update_of_ne hpr] at hp
    by_cases hi : i = r
    · subst hi
      have hr := h i
      rw [pivotStepMat_mulVec_self, pivotStepRhs, Function.update_self,
        hp] at hr
      exact sub_left_inj.mp hr
    · have hi' := h i
      rwa [pivotStepMat_mulVec_ne A p r c x hi, pivotStepRhs,
        Function.update_of_ne hi] at hi'
  · intro h i
    have hp := h p
    by_cases hi : i = r
    · subst hi
      rw [pivotStepMat_mulVec_self, pivotStepRhs, Function.update_self,
        h i, hp]
    · rw [pivotStepMat_mulVec_ne A p r c x hi, pivotStepRhs,
        Function.update_of_ne hi, h i]

end Transfer.Examples.CoqEAL.GaussPivotStep
