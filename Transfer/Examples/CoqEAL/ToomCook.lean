/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib

/-!
# CoqEAL `toomcook` — the evaluate–multiply–interpolate core

Toom-Cook multiplication (which `Karatsuba` is the two-way case of) multiplies
polynomials by splitting each into parts, **evaluating** at enough points,
multiplying the values pointwise, and **interpolating** the product back. The
soundness of the evaluate-multiply step is that evaluation is a ring
homomorphism: `(p * q)(t) = p(t) · q(t)`. Interpolation — the unique polynomial of
bounded degree through the sampled points — recovers `p * q`, so the pointwise
products at enough points determine the product exactly. The general algorithm is
the suite's frontier; the identity below is its load-bearing core.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.ToomCook

open Polynomial

/-- **The evaluate–multiply core of Toom-Cook.** Evaluation is multiplicative, so
    a product's value at a point is the product of the values — what lets
    Toom-Cook multiply pointwise after sampling. -/
theorem eval_product (p q : Polynomial ℤ) (t : ℤ) :
    (p * q).eval t = p.eval t * q.eval t := by
  simp

/-- Sampling at three points determines the product of two linear polynomials
    (degree `≤ 2`): each value is a pointwise product, the data Toom-3
    interpolates from. -/
example (p q : Polynomial ℤ) (t : ℤ) :
    (p * q).eval t = p.eval t * q.eval t := eval_product p q t

end Transfer.Examples.CoqEAL.ToomCook
