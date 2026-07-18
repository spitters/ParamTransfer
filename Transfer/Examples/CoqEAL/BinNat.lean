/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Ring

/-!
# CoqEAL `binnat`, ported to Lean — `List Bool` refines the natural numbers

CoqEAL's `binnat` refines MathComp `nat` to a binary representation `N`. Here we
port the **data-refinement core** of that example: a little-endian (lsb-first)
bit list `List Bool` refines the abstract `ℕ` via `toNat`, and the concrete
binary increment `binSucc` refines the abstract `Nat.succ` — the CoqEAL
`Rsucc_N` (carry-ripple) refinement square.

This mirrors the companion `SeqPoly.lean` (`seqpoly` add) and `SeqMatrix.lean`
(`seqmatrix` add): the refinement *mechanism* — a relation between an abstract
and a concrete representation, plus transfer of operations — is the same
`ReprTransfer` layer, and this file is one worked instance over the `binnat`
representation. The carry ripple of `binSucc` (flip trailing `true`s to `false`,
then set the first `false`/append) is exactly the structural recursion whose
refinement square `toNat_binSucc` discharges.

## Scope (the rest of CoqEAL)

The first-order data refinements — `binnat` (here), `binint`, `binrat`, `seqpoly`,
`seqmatrix` — and the fast algorithms — Karatsuba and Strassen multiplication,
Gaussian elimination — are ported alongside this file in the suite. The remaining
tail — Toom-Cook multiplication, the Bareiss fraction-free determinant, matrix
rank, multivariate polynomials, and the normal-form theory (Smith, Jordan,
Frobenius) — is CoqEAL's research contribution, a much larger development,
documented as the suite's frontier rather than ported.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.BinNat

/-- The CoqEAL `binnat` refinement relation: a little-endian (lsb-first) bit list
    denotes the natural number it encodes (`true`/`false` are bits `1`/`0`). -/
def toNat : List Bool → ℕ :=
  fun l => l.foldr (fun b acc => acc * 2 + (if b then 1 else 0)) 0

/-- The concrete (computational) binary increment, with explicit carry ripple:
    `[]` becomes `[1]`; a low `0` becomes `1`; a low `1` becomes `0` and the
    carry propagates into the higher bits. -/
def binSucc : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: binSucc l

/-- **The CoqEAL `Rsucc_N` refinement square.** The concrete binary increment
    refines the abstract `Nat.succ`: `toNat (binSucc l) = toNat l + 1`. -/
theorem toNat_binSucc (l : List Bool) : toNat (binSucc l) = toNat l + 1 := by
  induction l with
  | nil => simp [toNat, binSucc]
  | cons b l ih =>
    cases b with
    | false => simp [toNat, binSucc]
    | true =>
      simp only [binSucc, toNat, List.foldr_cons, if_true, if_false,
        Bool.false_eq_true] at ih ⊢
      rw [ih]
      ring

end Transfer.Examples.CoqEAL.BinNat
