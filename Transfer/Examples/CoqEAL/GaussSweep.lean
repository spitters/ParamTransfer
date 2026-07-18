/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Examples.CoqEAL.GaussPivotStep

/-!
# Gaussian elimination: multi-row forward sweep (refinement)

`GaussPivotStep.lean` discharged a **single** forward-elimination pivot step and
proved it preserves the solution set of `A · x = b`. This file iterates that
step across a **list of target rows** — the genuine *forward sweep* that
eliminates one fixed pivot column from each of a batch of rows — and proves the
whole sweep preserves the solution set, by induction over the row list using the
single-step lemma.

A sweep is parameterized by a fixed pivot row `p` and a list `targets` of
`(row, coefficient)` pairs: it folds the single pivot step `pivotStepMat … r c`
across the list, in order. The matrix transform is `gaussSweepMat` and the
target-vector transform is `gaussSweepRhs`. As long as every target row in the
list is distinct from the pivot row `p` (`hp : ∀ rc ∈ targets, p ≠ rc.1`), the
single-step invariance composes:

  `gaussSweep_preserves_solution :`
  `  (gaussSweepMat A p targets).mulVec x = gaussSweepRhs b p targets ↔`
  `    A.mulVec x = b`

This is the **forward-elimination-preserves-solutions** result. The remaining
Gaussian-elimination tail — pivot selection (search for a nonzero pivot, row
swaps), back-substitution, and the termination argument — is the suite's
frontier.

## API

* `gaussSweepMat` — coefficient matrix after sweeping the pivot step across
  `targets`.
* `gaussSweepRhs` — target vector after the same sweep.
* `gaussSweep_preserves_solution` — `x` solves the swept system iff it solves
  the original one (solution-set invariance of the whole forward sweep).
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.GaussSweep

open Matrix
open Transfer.Examples.CoqEAL.GaussPivotStep

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- The coefficient matrix after a forward sweep: fold the single pivot step
    (against the fixed pivot row `p`) across the list `targets` of
    `(target row, coefficient)` pairs, in order. -/
def gaussSweepMat (A : Matrix n n R) (p : n) :
    List (n × R) → Matrix n n R
  | [] => A
  | rc :: rest => gaussSweepMat (pivotStepMat A p rc.1 rc.2) p rest

/-- The target vector after the same forward sweep. -/
def gaussSweepRhs (b : n → R) (p : n) :
    List (n × R) → (n → R)
  | [] => b
  | rc :: rest => gaussSweepRhs (pivotStepRhs b p rc.1 rc.2) p rest

omit [Fintype n] in
@[simp] theorem gaussSweepMat_nil (A : Matrix n n R) (p : n) :
    gaussSweepMat A p [] = A := rfl

omit [Fintype n] in
@[simp] theorem gaussSweepMat_cons (A : Matrix n n R) (p : n) (rc : n × R)
    (rest : List (n × R)) :
    gaussSweepMat A p (rc :: rest) =
      gaussSweepMat (pivotStepMat A p rc.1 rc.2) p rest := rfl

omit [Fintype n] in
@[simp] theorem gaussSweepRhs_nil (b : n → R) (p : n) :
    gaussSweepRhs b p [] = b := rfl

omit [Fintype n] in
@[simp] theorem gaussSweepRhs_cons (b : n → R) (p : n) (rc : n × R)
    (rest : List (n × R)) :
    gaussSweepRhs b p (rc :: rest) =
      gaussSweepRhs (pivotStepRhs b p rc.1 rc.2) p rest := rfl

/-- **The forward sweep preserves the solution set.** A vector `x` satisfies the
    swept system `gaussSweepMat A p targets · x = gaussSweepRhs b p targets` iff
    it satisfies the original system `A · x = b`, provided every target row in
    the sweep is distinct from the pivot row `p`. Proof: induction over the row
    list, peeling one pivot step at a time via
    `pivotStep_preserves_solution`. -/
theorem gaussSweep_preserves_solution (p : n) (x : n → R) :
    ∀ (targets : List (n × R)) (A : Matrix n n R) (b : n → R),
      (∀ rc ∈ targets, p ≠ rc.1) →
      ((gaussSweepMat A p targets).mulVec x = gaussSweepRhs b p targets ↔
        A.mulVec x = b)
  | [], A, b, _ => by simp
  | rc :: rest, A, b, hp => by
    rw [gaussSweepMat_cons, gaussSweepRhs_cons]
    have hpr : p ≠ rc.1 := hp rc List.mem_cons_self
    have hrest : ∀ rc' ∈ rest, p ≠ rc'.1 := fun rc' h => hp rc' (List.mem_cons_of_mem _ h)
    rw [gaussSweep_preserves_solution p x rest _ _ hrest]
    exact pivotStep_preserves_solution A b p rc.1 rc.2 hpr x

end Transfer.Examples.CoqEAL.GaussSweep
