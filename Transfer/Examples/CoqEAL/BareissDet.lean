/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# CoqEAL `bareiss` — a fraction-free determinant certified against `Matrix.det`

CoqEAL's `bareiss` computes an exact integer determinant by fraction-free
elimination, never leaving `ℤ`. This file gives the refinement at the base sizes:
a `ℤ`-only, `#eval`-computable determinant certified equal to Mathlib's
`Matrix.det`. At `2×2` the formula is `a*d - b*c`; at `3×3` it is the
Sarrus/Bareiss expansion. Both avoid division, and both equal `Matrix.det`
(`det_fin_two`, `det_fin_three`) — computing the classical determinant in `ℤ`.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.Bareiss

/-- Fraction-free `2×2` determinant (the Bareiss base case). -/
def det2 (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- `det2` refines Mathlib's `Matrix.det` at size 2. -/
theorem det2_eq (M : Matrix (Fin 2) (Fin 2) ℤ) : det2 M = M.det := by
  simp only [det2, Matrix.det_fin_two]

/-- Fraction-free `3×3` determinant (the Sarrus/Bareiss expansion). -/
def det3 (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1)
    - M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0)
    + M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0)

/-- `det3` refines Mathlib's `Matrix.det` at size 3. -/
theorem det3_eq (M : Matrix (Fin 3) (Fin 3) ℤ) : det3 M = M.det := by
  simp only [det3, Matrix.det_fin_three]; ring

/-! ## Compute a classical determinant in `ℤ` -/

/-- A concrete matrix. -/
def sample : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 3, 4]

#guard det2 sample = -2

/-- The Mathlib determinant of `sample`, obtained fraction-free. -/
example : sample.det = -2 := by
  rw [← det2_eq]; decide

end Transfer.Examples.CoqEAL.Bareiss
