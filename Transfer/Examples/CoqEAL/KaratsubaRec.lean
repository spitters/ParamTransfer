/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Examples.CoqEAL.Karatsuba

/-!
# Recursive Karatsuba on `CPolynomial R`

This file extends the one-level Karatsuba step of `Karatsuba.lean` to the **full
recursion**. Where `karatsubaMul` takes the four already-split halves as explicit
arguments, `karatsubaRec` is a genuine binary multiply `CPolynomial R →
CPolynomial R → CPolynomial R` that splits each input itself, recurses on the
three Karatsuba subproducts, and recombines.

## Termination via fuel

Rather than a well-founded recursion on a decreasing degree measure (which would
require carrying split-size proofs through every recursive call), `karatsubaRec`
takes an explicit `fuel : ℕ` and bottoms out in the schoolbook product `p * q`
at `fuel = 0`. This is the standard structurally-recursive presentation and is
sufficient for the algebraic-correctness statement, which is the point of the
CoqEAL refinement: for *every* fuel value, `karatsubaRec fuel p q` denotes the
true product `p · q`.

## The split

The high part `hiPart k p` drops the `k` lowest coefficients (`divX` iterated
`k` times); the low part is then *defined* as `loPart k p := p − Xᵏ · hiPart k p`.
With this definition the **split–recompose identity**

```
  loPart k p + Xᵏ · hiPart k p = p
```

is a one-line commutative-ring fact (`(p − Xᵏ·h) + Xᵏ·h = p`), needing no
coefficient reasoning and no appeal to a CompPoly division-with-remainder
lemma (CompPoly only provides `divByMonic`/`modByMonic` over a `Field`, whereas
this development is over a `CommRing`). The split point `k` does **not** affect
correctness — only performance — so `karatsubaRec` is correct for any choice;
we pick the balanced `⌊max(deg p, deg q)/2⌋ + 1`.

## Correctness

`karatsubaRec_eq : (karatsubaRec fuel p q).toPoly = p.toPoly * q.toPoly` is by
induction on `fuel`. The base case is `toPoly_mul`. The step case rewrites the
three recursive subproducts to true products via the induction hypothesis, then
discharges the recombination — recompose both inputs and expand — by transferring
across `CPolynomial.ringEquiv` to Mathlib `Polynomial R`, exactly as
`karatsubaMul_eq` does for the one-level step.

## Registry entry

`karatsubaRec_repr` is tagged `@[transfer]` in the refine direction (`p * q ↦
karatsubaRec fuel p q`), registering recursive Karatsuba as a refinement of the
schoolbook product, mirroring `karatsuba_repr` for the one-level step. Because
the recursion carries a `fuel` argument that appears only on the right, the
rewrite is applied with the fuel supplied (`rw [karatsubaRec_repr fuel]`) rather
than via bare `repr_transfer`.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.Karatsuba

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- **High part of a split at degree `k`.** Drops the `k` lowest coefficients by
    iterating `divX` (pseudo-division by `X`) `k` times. -/
noncomputable def hiPart (k : ℕ) (p : CPolynomial R) : CPolynomial R :=
  CPolynomial.divX^[k] p

/-- **Low part of a split at degree `k`,** defined so that recomposition is a
    ring identity: `p = loPart k p + Xᵏ · hiPart k p`. -/
noncomputable def loPart (k : ℕ) (p : CPolynomial R) : CPolynomial R :=
  p - (CPolynomial.X ^ k) * hiPart k p

/-- **Split–recompose identity.** Recomposing the low and high parts at any
    degree `k` returns the original polynomial. By construction `loPart` is the
    complement of `Xᵏ · hiPart`, so this is a commutative-ring fact — no
    coefficient reasoning required. -/
theorem loPart_add_hiPart (k : ℕ) (p : CPolynomial R) :
    loPart k p + (CPolynomial.X ^ k) * hiPart k p = p := by
  apply (CompPoly.CPolynomial.ringEquiv (R := R)).injective
  show CPolynomial.toPoly _ = CPolynomial.toPoly _
  unfold loPart
  simp only [toPoly_add, toPoly_sub, toPoly_mul, toPoly_pow]
  ring

/-- A reasonable balanced split point: half the larger degree, plus one (so a
    nonconstant input is split nontrivially). Correctness is independent of this
    choice. -/
noncomputable def splitPoint (p q : CPolynomial R) : ℕ :=
  (max p.natDegree q.natDegree) / 2 + 1

/-- **Recursive Karatsuba multiplication** with explicit `fuel`.

    At `fuel = 0` it is the schoolbook product. Otherwise it splits both inputs
    at `splitPoint p q`, recursively forms the three Karatsuba subproducts
    `z₀ = plo·qlo`, `z₂ = phi·qhi`, `(plo+phi)·(qlo+qhi)`, and recombines as
    `z₀ + Xᵏ·z₁ + X²ᵏ·z₂` with `z₁ = (plo+phi)(qlo+qhi) − z₀ − z₂`. -/
noncomputable def karatsubaRec : ℕ → CPolynomial R → CPolynomial R → CPolynomial R
  | 0, p, q => p * q
  | fuel + 1, p, q =>
    let k := splitPoint p q
    let plo := loPart k p
    let phi := hiPart k p
    let qlo := loPart k q
    let qhi := hiPart k q
    let z0 := karatsubaRec fuel plo qlo
    let z2 := karatsubaRec fuel phi qhi
    let z1 := karatsubaRec fuel (plo + phi) (qlo + qhi) - z0 - z2
    z0 + (CPolynomial.X ^ k) * z1 + (CPolynomial.X ^ (2 * k)) * z2

/-- **Correctness of recursive Karatsuba.** For every fuel value,
    `karatsubaRec fuel p q` denotes the true product `p · q`.

    Induction on `fuel`: the base case is `toPoly_mul`; the step case rewrites
    the three recursive subproducts via the induction hypothesis and then
    discharges the recombination — recompose both inputs (`loPart_add_hiPart`)
    and expand — by transferring across `CPolynomial.ringEquiv` to Mathlib
    `Polynomial R`, where it is a `ring` identity. -/
theorem karatsubaRec_eq (fuel : ℕ) (p q : CPolynomial R) :
    (karatsubaRec fuel p q).toPoly = p.toPoly * q.toPoly := by
  induction fuel generalizing p q with
  | zero => simp only [karatsubaRec, toPoly_mul]
  | succ fuel ih =>
    -- Abbreviations matching the `let`-bindings in `karatsubaRec`.
    set k := splitPoint p q with hk
    set plo := loPart k p with hplo
    set phi := hiPart k p with hphi
    set qlo := loPart k q with hqlo
    set qhi := hiPart k q with hqhi
    -- Recompose the two inputs from their halves (degree-`k` split).
    have hp : p = plo + (CPolynomial.X ^ k) * phi := (loPart_add_hiPart k p).symm
    have hq : q = qlo + (CPolynomial.X ^ k) * qhi := (loPart_add_hiPart k q).symm
    -- Unfold one step and push `toPoly` through the recombination, rewriting the
    -- three recursive subproducts to true products via the induction hypothesis.
    show (karatsubaRec (fuel + 1) p q).toPoly = p.toPoly * q.toPoly
    rw [karatsubaRec]
    simp only [toPoly_add, toPoly_sub, toPoly_mul, toPoly_pow, ih]
    -- Now substitute the recompositions and finish with `ring`.
    conv_rhs => rw [hp, hq]
    simp only [toPoly_add, toPoly_mul, toPoly_pow]
    ring

/-- **Registry entry (refinement direction).** Tagged `@[transfer]` so that
    `repr_transfer` rewrites a plain `CPolynomial` product `p · q` to its
    recursive-Karatsuba form `karatsubaRec fuel p q`. Mirrors `karatsuba_repr`
    for the one-level step. -/
@[transfer] theorem karatsubaRec_repr (fuel : ℕ) (p q : CPolynomial R) :
    p * q = karatsubaRec fuel p q := by
  apply (CompPoly.CPolynomial.ringEquiv (R := R)).injective
  show CPolynomial.toPoly _ = CPolynomial.toPoly _
  rw [toPoly_mul, karatsubaRec_eq]

/-- Sanity check that the recursive registry entry fires. Unlike the one-level
    `karatsuba_repr` (whose split point `k` appears on both sides), the recursive
    entry carries an extra `fuel` argument that appears only on the right, so it
    is applied with the fuel supplied (`rw [karatsubaRec_repr fuel]`) — `simp`'s
    bare `repr_transfer` cannot invent a fuel value. With the fuel given the
    rewrite to recursive-Karatsuba form is immediate. -/
example (fuel : ℕ) (p q : CPolynomial R) :
    p * q = karatsubaRec fuel p q := by
  rw [karatsubaRec_repr fuel]

end Transfer.Examples.CoqEAL.Karatsuba
