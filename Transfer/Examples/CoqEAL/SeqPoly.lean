/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Algebra.Group.Defs

/-!
# CoqEAL `seqpoly`, ported to Lean — `List R` refines the coefficient function

CoqEAL's `seqpoly` refines MathComp polynomials `{poly R}` to lists `seq R`. Here
we port the **data-refinement core** of that example into the `ReprTransfer`
framework: a coefficient list `List R` refines the abstract coefficient function
`ℕ → R`, and the concrete list addition `addSeq` refines the abstract
coefficient-wise addition — the CoqEAL `Radd_seqpoly` refinement square.

The refinement mechanism — a relation between an abstract and a concrete
representation, plus transfer of operations — is the `ReprTransfer` layer; this
file is one worked instance over the `seqpoly` representation. The `CoqEAL`
aggregator records the suite's frontier (the general-size algorithms and the
normal-form theory).
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.SeqPoly

variable {R : Type*} [AddZeroClass R]

/-- The CoqEAL `seqpoly` refinement relation: a coefficient list denotes the
    abstract coefficient function (absent coefficients are `0`). -/
def coeff (l : List R) (i : ℕ) : R := l.getD i 0

/-- The concrete (computational) polynomial addition on coefficient lists. -/
def addSeq : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addSeq p q

/-- **The CoqEAL `Radd_seqpoly` refinement square.** The concrete list addition
    refines the abstract coefficient-wise addition. -/
theorem coeff_addSeq (p q : List R) (i : ℕ) :
    coeff (addSeq p q) i = coeff p i + coeff q i := by
  induction p generalizing q i with
  | nil => simp [addSeq, coeff]
  | cons a p ih =>
    cases q with
    | nil => simp [addSeq, coeff]
    | cons b q =>
      cases i with
      | zero => simp [addSeq, coeff]
      | succ i => simp only [addSeq, coeff, List.getD_cons_succ]; exact ih q i

/-- Functional form of the refinement square — the commuting square the
    `ReprTransfer` registry consumes (concrete add ↦ abstract pointwise add). -/
theorem coeff_addSeq_fun (p q : List R) :
    coeff (addSeq p q) = fun i => coeff p i + coeff q i := by
  funext i; exact coeff_addSeq p q i

end Transfer.Examples.CoqEAL.SeqPoly
