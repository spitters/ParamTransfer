/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Examples.CoqEAL.ComputePolynomial
import Transfer.Examples.CoqEAL.SeqPoly
import Transfer.Examples.CoqEAL.BinNat
import Transfer.Examples.CoqEAL.BinInt
import Transfer.Examples.CoqEAL.BinRat
import Transfer.Examples.CoqEAL.SeqMatrix
import Transfer.Examples.CoqEAL.SeqMatrixMul
import Transfer.Examples.CoqEAL.Strassen
import Transfer.Examples.CoqEAL.StrassenRec
import Transfer.Examples.CoqEAL.Karatsuba
import Transfer.Examples.CoqEAL.KaratsubaRec
import Transfer.Examples.CoqEAL.GaussPivotStep
import Transfer.Examples.CoqEAL.GaussSweep
import Transfer.Examples.CoqEAL.BareissDet
import Transfer.Examples.CoqEAL.Rank
import Transfer.Examples.CoqEAL.ToomCook
import Transfer.Examples.CoqEAL.Multipoly

/-!
# The CoqEAL / Trocq example suite

Worked examples demonstrating the engine on the CoqEAL data-refinement patterns —
a computational representation of a proof-oriented Mathlib object, related by a
refinement across which statements, terms, and computations transfer.

This suite is a **separate library** (`TransferCoqEAL`) from the core engine
(`Transfer`), so its dependency on [CompPoly](https://github.com/Verified-zkEVM/CompPoly)
stays out of the core graph: a consumer of the engine does not build CompPoly. For
CompPoly's own documentation, see that repository's handbook and wiki.

Members:
* `ComputePolynomial` — compute with Mathlib's `Polynomial` through CompPoly's
  array-backed `CPolynomial` and its `RingEquiv` (the Kaliszyk–O'Connor /
  CoqEAL "refinements for free" move).
* `SeqPoly` — CoqEAL `seqpoly`: polynomials refined to coefficient lists.
* `BinNat` — CoqEAL `binnat`: binary naturals refined to unary `ℕ`.
* `BinInt` — CoqEAL `binint`: sign + magnitude refined to `ℤ`.
* `BinRat` — CoqEAL `rational`: numerator/denominator pairs refined to `ℚ`.
* `SeqMatrix` — CoqEAL `seqmatrix`: matrices refined to lists of lists (addition).
* `SeqMatrixMul` — the `seqmatrix` multiplication refinement (row-column product).
* `Strassen` — Strassen's `2×2` block matrix multiply (7 multiplications).
* `StrassenRec` — the recursive Strassen multiply over `⊕`-doubled dimensions.
* `Karatsuba` — Karatsuba polynomial multiplication over CompPoly, refined to
  Mathlib's `Polynomial`.
* `KaratsubaRec` — the fuel-recursive Karatsuba multiply.
* `GaussPivotStep` — one Gaussian-elimination pivot step, solution-set preserving.
* `GaussSweep` — the multi-row forward-elimination sweep.
* `BareissDet` — CoqEAL `bareiss`: a fraction-free determinant certified against
  `Matrix.det` at the base sizes.
* `Rank` — CoqEAL `rank`: matrix rank certified against `Matrix.rank`.
* `ToomCook` — CoqEAL `toomcook`: the evaluate–multiply–interpolate core.
* `Multipoly` — CoqEAL `multipoly`: multivariate polynomials as finite maps.

The Trocq examples (including `summable`) live in the sibling `Examples/Trocq` suite.

## Frontier (documented, not ported)

The following upstream members are larger developments — CoqEAL's research
contribution — recorded here rather than ported:

* the general elimination algorithms behind `BareissDet`/`Rank` (arbitrary size,
  certified against `Matrix.det`/`Matrix.rank`) and the full `ToomCook` interpolation;
* normal-form theory (CoqEAL) — Smith, Jordan, Frobenius forms, the EDR hierarchy.

Trocq's `setoid_rewrite` (rewriting up to a registered relation) is already
exercised by `param_cc` in `Examples/ExampleField`.
-/
