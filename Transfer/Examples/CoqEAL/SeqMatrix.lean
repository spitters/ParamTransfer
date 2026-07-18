/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Algebra.Group.Defs

/-!
# CoqEAL `seqmatrix`, ported to Lean — `List (List R)` refines the entry function

CoqEAL's `seqmatrix` refines MathComp matrices `'M[R]_(m,n)` to lists of lists
`seq (seq R)`. Here we port the **data-refinement core** of that example: a
matrix-as-rows `List (List R)` refines the abstract entry function `ℕ → ℕ → R`
(absent entries are `0`), and the concrete row-wise list addition `addMx`
refines the abstract entrywise addition — the CoqEAL `Radd_seqmx` refinement
square.

This mirrors the companion `SeqPoly.lean` (`seqpoly` add) one dimension up: the
inner row addition reuses the same `addSeq`-style coefficientwise add, and the
outer `addMx` zips rows. The refinement *mechanism* — a relation between an
abstract and a concrete representation, plus transfer of operations — is the
same `ReprTransfer` layer; this file is one worked instance over the `seqmatrix`
representation. `SeqMatrixMul` refines the multiplication; the `CoqEAL`
aggregator records the suite's frontier.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.SeqMatrix

variable {R : Type*} [AddZeroClass R]

/-- The CoqEAL `seqmatrix` refinement relation: a row-major list of lists denotes
    the abstract entry function (absent rows and entries are `0`). -/
def entry (m : List (List R)) (i j : ℕ) : R := (m.getD i []).getD j 0

/-- The concrete (computational) row addition on coefficient lists — the inner
    `addSeq`-style coefficientwise add, shared with the `seqpoly` example. -/
def addSeq : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: addSeq p q

/-- The inner row-refinement square: the concrete row add refines pointwise add. -/
theorem getD_addSeq (p q : List R) (j : ℕ) :
    (addSeq p q).getD j 0 = p.getD j 0 + q.getD j 0 := by
  induction p generalizing q j with
  | nil => simp [addSeq]
  | cons a p ih =>
    cases q with
    | nil => simp [addSeq]
    | cons b q =>
      cases j with
      | zero => simp [addSeq]
      | succ j => simp only [addSeq, List.getD_cons_succ]; exact ih q j

/-- The concrete (computational) matrix addition on lists of rows. -/
def addMx : List (List R) → List (List R) → List (List R)
  | [], n => n
  | m, [] => m
  | r :: m, s :: n => addSeq r s :: addMx m n

/-- **The CoqEAL `Radd_seqmx` refinement square.** The concrete row-wise list
    addition refines the abstract entrywise matrix addition. -/
theorem entry_addMx (m n : List (List R)) (i j : ℕ) :
    entry (addMx m n) i j = entry m i j + entry n i j := by
  induction m generalizing n i with
  | nil => simp [addMx, entry]
  | cons r m ih =>
    cases n with
    | nil => simp [addMx, entry]
    | cons s n =>
      cases i with
      | zero => simp only [addMx, entry, List.getD_cons_zero]; exact getD_addSeq r s j
      | succ i => simp only [addMx, entry, List.getD_cons_succ]; exact ih n i

/-- Functional form of the refinement square — the commuting square the
    `ReprTransfer` registry consumes (concrete add ↦ abstract entrywise add). -/
theorem entry_addMx_fun (m n : List (List R)) :
    entry (addMx m n) = fun i j => entry m i j + entry n i j := by
  funext i j; exact entry_addMx m n i j

end Transfer.Examples.CoqEAL.SeqMatrix
