/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import CompPoly.Univariate.ToPoly.Equiv
import Transfer.Base.Core

/-!
# CoqEAL Karatsuba polynomial multiplication, ported to Lean

CoqEAL's `karatsuba` is the headline algorithm refinement of the library: a fast
polynomial multiply proven to refine the schoolbook product. This file ports the
algebraic core of that refinement onto CompPoly's computable `CPolynomial R`, and
registers it in the engine's `@[transfer]` registry (`Transfer.Base.Core`).

## What is proved

The Karatsuba trick rewrites a single split product

```
  (lo + Xᵏ·hi) · (lo' + Xᵏ·hi')
    = z₀ + Xᵏ·z₁ + X²ᵏ·z₂
```

with `z₀ = lo·lo'`, `z₂ = hi·hi'`, and `z₁ = (lo+hi)·(lo'+hi') − z₀ − z₂` — i.e.
three multiplications instead of four. `karatsubaMul` is exactly this
recombination on the four halves, and `karatsubaMul_eq` proves it equals the
product of the two reconstructed polynomials.

The proof is genuine: it transfers the goal across CompPoly's `RingEquiv`
`CPolynomial R ≃+* Polynomial R` (`CPolynomial.ringEquiv`, whose underlying map
`toPoly` is injective) to Mathlib's `Polynomial R`, where the recombination
identity is a commutative-ring fact discharged by `ring`. The transfer is sound
because `toPoly` is a ring homomorphism on `+`, `-`, `*`, `^` (CompPoly's
`toPoly_add` / `toPoly_sub` / `toPoly_mul` / `toPoly_pow`), so no coefficient
reasoning is duplicated and canonicalization (trailing-zero trimming) is handled
inside those CompPoly lemmas.

## Scope — the residual is the *recursion*, not the identity

This is the **one-level** Karatsuba step, taking the four halves as explicit
arguments. A full `karatsubaMul' : CPolynomial R → CPolynomial R → CPolynomial R`
would (a) split each input at a chosen degree `k` (a `divByMonic`/`modByMonic`
or array-`extract` operation on the canonical representation), (b) recurse on
the three half-products, and (c) terminate by a decreasing-degree measure with a
base case below a cutoff. The *splitting* and the *recursion/termination* are the
genuine library tail (matching CoqEAL's `Rmorph_karatsuba` over MathComp
`{poly R}`); they are **not** built here. What is delivered is the proven
algebraic identity plus `karatsubaMul = (· * ·)` for the structured (already
split) case. `KaratsubaRec` supplies the splitting and the fuel recursion.

## Registry entry

`karatsuba_repr` is tagged `@[transfer]` in the *refine* direction (structured
product ↦ Karatsuba recombination), so `repr_transfer` automatically rewrites a
`CPolynomial` product presented in split form `(lo + Xᵏ·hi)·(lo' + Xᵏ·hi')` to
its three-multiplication Karatsuba form. Karatsuba is now a registered
refinement in the transfer engine.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.Karatsuba

open CompPoly CompPoly.CPolynomial

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- **One-level Karatsuba recombination** on the four halves of a split product.

    Given the low/high halves `lo, hi` of `p = lo + Xᵏ·hi` and `lo', hi'` of
    `q = lo' + Xᵏ·hi'`, this computes the product `p · q` using only three
    half-multiplications (`z₀`, `z₂`, and the middle `(lo+hi)·(lo'+hi')`)
    instead of the four a naive cross product would use:

    `z₀ + Xᵏ·z₁ + X²ᵏ·z₂` with `z₁ = (lo+hi)·(lo'+hi') − z₀ − z₂`. -/
noncomputable def karatsubaMul (k : ℕ) (lo hi lo' hi' : CPolynomial R) : CPolynomial R :=
  let z0 := lo * lo'
  let z2 := hi * hi'
  let z1 := (lo + hi) * (lo' + hi') - z0 - z2
  z0 + (CPolynomial.X ^ k) * z1 + (CPolynomial.X ^ (2 * k)) * z2

/-- **Correctness of the Karatsuba step.** The recombination equals the product
    of the two reconstructed polynomials `lo + Xᵏ·hi` and `lo' + Xᵏ·hi'`.

    Proved by transferring across the ring equivalence
    `CPolynomial.ringEquiv : CPolynomial R ≃+* Polynomial R` (injective `toPoly`)
    to Mathlib `Polynomial R`, where the identity is a `ring` fact. This is the
    Karatsuba algebraic identity in full; the recursion/termination/splitting is
    the named residual (see the module docstring). -/
theorem karatsubaMul_eq (k : ℕ) (lo hi lo' hi' : CPolynomial R) :
    karatsubaMul k lo hi lo' hi'
      = (lo + (CPolynomial.X ^ k) * hi) * (lo' + (CPolynomial.X ^ k) * hi') := by
  -- `toPoly` is injective (it is the forward map of the `RingEquiv`), so it
  -- suffices to prove the identity on Mathlib polynomials.
  apply (CompPoly.CPolynomial.ringEquiv (R := R)).injective
  show CPolynomial.toPoly _ = CPolynomial.toPoly _
  unfold karatsubaMul
  -- Push `toPoly` through `+`, `-`, `*`, `^` (it is a ring hom), then `ring`.
  simp only [toPoly_add, toPoly_sub, toPoly_mul, toPoly_pow]
  ring

/-- **Registry entry (refinement direction).** Tagged `@[transfer]` so that
    `repr_transfer` rewrites a structured `CPolynomial` product
    `(lo + Xᵏ·hi)·(lo' + Xᵏ·hi')` to its Karatsuba three-multiplication form
    `karatsubaMul k lo hi lo' hi'`. This makes Karatsuba a registered refinement
    in the transfer engine, alongside the field-kernel and `SeqPoly`
    add refinements. -/
@[transfer] theorem karatsuba_repr (k : ℕ) (lo hi lo' hi' : CPolynomial R) :
    (lo + (CPolynomial.X ^ k) * hi) * (lo' + (CPolynomial.X ^ k) * hi')
      = karatsubaMul k lo hi lo' hi' :=
  (karatsubaMul_eq k lo hi lo' hi').symm

/-- Sanity check that the registry entry fires: `repr_transfer` rewrites the
    structured product to Karatsuba form automatically. -/
example (k : ℕ) (lo hi lo' hi' : CPolynomial R) :
    (lo + (CPolynomial.X ^ k) * hi) * (lo' + (CPolynomial.X ^ k) * hi')
      = karatsubaMul k lo hi lo' hi' := by
  repr_transfer

end Transfer.Examples.CoqEAL.Karatsuba
