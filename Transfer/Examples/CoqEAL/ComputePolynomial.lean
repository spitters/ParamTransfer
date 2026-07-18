/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import CompPoly.Univariate.ToPoly.Equiv
import CompPoly.Univariate.ToPoly.Impl
import ReprTransfer

/-!
# Computing with Mathlib's `Polynomial` through a CompPoly refinement

Mathlib's `Polynomial R` is the proof-oriented object — a `Finsupp`, with the
operations that matter for evaluation `noncomputable`. CompPoly's `CPolynomial R`
is the computation-oriented refinement: an `Array`-backed representation
(`CPolynomial.Raw R := Array R`) with a `RingEquiv` to `Polynomial R`
(`CompPoly.CPolynomial.ringEquiv`, forward map `toPoly`).

This is the CoqEAL data refinement, and the Kaliszyk–O'Connor move that
`ReprTransfer` records: *compute with a classical object* by running the
computational representation and certifying the result against the classical one
through the isomorphism. Here the classical object is Mathlib's `Polynomial ℤ`;
the computation runs in `CPolynomial ℤ`; and `coeff_toPoly` / `toPoly_mul` certify
that a coefficient computed by array arithmetic *is* the coefficient of the Mathlib
product.

The `ReprTransfer` view: `CPolynomial`'s `*` realizes `Polynomial`'s `*` along the
decoder `toPoly` — a `BinOpHomOn` (a homomorphism on the whole domain, no
injectivity needed), the map-level rung of the transfer hierarchy.
-/

set_option autoImplicit false

open CompPoly CompPoly.CPolynomial

namespace Transfer.Param.CoqEAL

/-- The computational (array-backed) polynomial carrier over `ℤ`. -/
abbrev CP : Type := CPolynomial ℤ

/-- `2X + 1`, stored as an array. -/
def poly1 : CP := C 1 + C 2 * X

/-- `3X + 1`, stored as an array. -/
def poly2 : CP := C 1 + C 3 * X

/-! ## Compute

`(2X + 1)(3X + 1) = 6X² + 5X + 1`, by array arithmetic — `#guard` forces the
computation and asserts each coefficient. -/

#guard (poly1 * poly2).coeff 0 = 1
#guard (poly1 * poly2).coeff 1 = 5
#guard (poly1 * poly2).coeff 2 = 6

/-! ## Certify against Mathlib's `Polynomial` -/

/-- `toPoly` is a `*`-homomorphism into Mathlib's `Polynomial` (the `map_mul` of
    `ringEquiv`). -/
theorem toPoly_mul' (a b : CP) : (a * b).toPoly = a.toPoly * b.toPoly :=
  CompPoly.CPolynomial.toPoly_mul a b

/-- A coefficient computed on the array representation equals the coefficient of
    the Mathlib polynomial it denotes. -/
theorem coeff_eq (a : CP) (i : ℕ) : a.coeff i = a.toPoly.coeff i :=
  CompPoly.CPolynomial.coeff_toPoly a i

/-- **The punchline.** A coefficient of the *Mathlib `Polynomial`* product
    `(2X + 1)(3X + 1)` is obtained by array computation: through `toPoly_mul` and
    `coeff_toPoly` the goal reduces to the computable `CPolynomial.coeff`, which the
    compiled array algorithm evaluates to `6`. `native_decide` runs that algorithm
    — the classical `Polynomial` fact is decided by computation, at the cost of the
    compiler-trust axiom. This is the Kaliszyk–O'Connor trade in the open: the
    `#guard`s above and the correspondence lemmas are axiom-free; deciding the
    classical fact by running the code trusts the compiler. -/
example : (poly1.toPoly * poly2.toPoly).coeff 2 = 6 := by
  rw [← toPoly_mul', ← coeff_eq]; native_decide

/-! ## The `ReprTransfer` realization -/

open ReprTransfer in
/-- `CPolynomial`'s `*` realizes Mathlib `Polynomial`'s `*` along the decoder
    `toPoly`: decoding the computed product equals the Mathlib product of the
    decoded operands, on the whole domain. This is the map-level `BinOpHomOn` — the
    field-arithmetic realizations (STARK / Baby Bear) share this rung. -/
noncomputable def polyMulRealization :
    BinOpHomOn (CompPoly.CPolynomial.toPoly : CP → Polynomial ℤ) (fun _ => True)
      (· * ·) (· * ·) where
  app_eq := fun a b _ _ => toPoly_mul' a b

end Transfer.Param.CoqEAL
