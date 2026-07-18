/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib

/-!
# CoqEAL `multipoly` — multivariate polynomials as finite maps

CoqEAL's `multipoly` refines multivariate polynomials to finite maps from monomial
exponent vectors to coefficients. In Mathlib `MvPolynomial σ R` *is* such a finite
map (`σ →₀ ℕ` exponents to coefficients), so the refinement is exhibited by reading
coefficients: a monomial's exponent vector selects its coefficient. This file pins
that reading down on `X` and on a monomial, the base of the `multipoly`
representation; the arithmetic refinement (`coeff_mul` over the exponent
antidiagonal) is the suite's frontier.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.Multipoly

open MvPolynomial

/-- The coefficient of the variable `X 0` at its exponent vector is `1` — reading a
    `multipoly` coefficient off the finite-map representation. -/
example : (X 0 : MvPolynomial (Fin 2) ℤ).coeff (Finsupp.single 0 1) = 1 := by
  simp

/-- A monomial's coefficient at its own exponent vector is its scalar; at any other
    exponent it is `0`. This is the finite-map view of `multipoly`. -/
example (m : Fin 2 →₀ ℕ) (c : ℤ) : (monomial m c).coeff m = c := by
  simp [MvPolynomial.coeff_monomial]

end Transfer.Examples.CoqEAL.Multipoly
