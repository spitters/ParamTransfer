/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing

/-!
# Recursive (fuel-driven) Strassen block multiplication

`Strassen.lean` proved the **one-level** `2×2` Strassen identity over a
commutative ring. This file lifts it to a genuinely **recursive** Strassen
multiply on block matrices: a matrix on a doubled index type `B ⊕ B` is split
into four `B`-indexed blocks, the seven Strassen products are computed by
*recursive* sub-multiplications (one fuel level down), and the four result
blocks are recombined via `Matrix.fromBlocks`.

## Design

* **Block index family.** `dim fuel m₀` doubles the base index type `m₀` once
  per fuel level: `dim 0 m₀ = m₀`, `dim (k+1) m₀ = dim k m₀ ⊕ dim k m₀`. This
  sidesteps the dependent `Fin (2*n)` reindexing (`finSumFinEquiv` / `reindex`)
  that fights the recursion — the recursion is on the *type-level* doubling
  directly, exactly the shape `Matrix.fromBlocks` consumes.
* **Recursion.** `strassenRec fuel` multiplies two `dim fuel m₀`-indexed
  matrices. At fuel `0` it is the ordinary product `*`; at fuel `k+1` it splits
  both operands into four blocks (`toBlocks₁₁ …`), forms the seven Strassen
  block products with seven recursive `strassenRec k` calls, and recombines.
* **Correctness.** `strassenRec_eq : strassenRec fuel A B = A * B`, by induction
  on fuel. The step rewrites the seven recursive products to `*` (IH), folds the
  blocks back with `Matrix.fromBlocks_toBlocks`, and discharges the algebraic
  Strassen identity with `Matrix.fromBlocks_multiply` + `noncomm_ring` (the
  blocks form a *non-commutative* matrix ring, and the Strassen recombination is
  order-preserving, so it holds over that ring).

## Scope and the named residual

This is the genuine recursion (real sub-multiplications down the fuel tower),
generalizing one level. The complexity/termination *accounting* (that fuel `k`
uses `7^k` base multiplications, the `O(n^log₂7)` bound) and pivoting to the
ragged `Fin (2*n)` data layout are the remaining residual and are not done here.

## API

* `dim` — the fuel-indexed doubled block index type.
* `strassenRec` — fuel-recursive Strassen multiply.
* `strassen_blocks_eq` — the non-commutative block Strassen recombination
  identity (the algebraic heart).
* `strassenRec_eq` — `strassenRec fuel A B = A * B`.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.StrassenRec

open Matrix

variable {R : Type*} [CommRing R]

/-- The fuel-indexed doubled block index type: doubles the base index `m₀` once
    per fuel level. -/
def dim (m₀ : Type*) : ℕ → Type _
  | 0 => m₀
  | (k + 1) => dim m₀ k ⊕ dim m₀ k

instance dimFintype (m₀ : Type*) [Fintype m₀] : (fuel : ℕ) → Fintype (dim m₀ fuel)
  | 0 => inferInstanceAs (Fintype m₀)
  | (k + 1) => @instFintypeSum _ _ (dimFintype m₀ k) (dimFintype m₀ k)

instance dimDecEq (m₀ : Type*) [DecidableEq m₀] :
    (fuel : ℕ) → DecidableEq (dim m₀ fuel)
  | 0 => inferInstanceAs (DecidableEq m₀)
  | (k + 1) => @instDecidableEqSum _ _ (dimDecEq m₀ k) (dimDecEq m₀ k)

/-- **The non-commutative block Strassen recombination identity.** For four
    blocks of each operand (over any matrix ring `Matrix m m R`, which is *not*
    commutative), the Strassen seven-product recombination of the blocks equals
    the block product `fromBlocks … * fromBlocks …`. The seven products appear
    in operand order, so the identity holds over the non-commutative block ring.
    -/
theorem strassen_blocks_eq {m : Type*} [Fintype m] [DecidableEq m]
    (A11 A12 A21 A22 B11 B12 B21 B22 : Matrix m m R) :
    Matrix.fromBlocks
        ((A11 + A22) * (B11 + B22) + A22 * (B21 - B11) - (A11 + A12) * B22
          + (A12 - A22) * (B21 + B22))
        (A11 * (B12 - B22) + (A11 + A12) * B22)
        ((A21 + A22) * B11 + A22 * (B21 - B11))
        ((A11 + A22) * (B11 + B22) - (A21 + A22) * B11 + A11 * (B12 - B22)
          + (A21 - A11) * (B11 + B12))
      = Matrix.fromBlocks A11 A12 A21 A22 * Matrix.fromBlocks B11 B12 B21 B22 := by
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring

/-- Fuel-recursive Strassen multiply on the doubled block index `dim m₀ fuel`.
    Fuel `0` is the ordinary product; each fuel step splits into four blocks,
    forms seven Strassen products with recursive calls, and recombines. -/
def strassenRec (m₀ : Type*) [Fintype m₀] [DecidableEq m₀] :
    (fuel : ℕ) → Matrix (dim m₀ fuel) (dim m₀ fuel) R →
      Matrix (dim m₀ fuel) (dim m₀ fuel) R →
      Matrix (dim m₀ fuel) (dim m₀ fuel) R
  | 0, A, B => A * B
  | (k + 1), A, B =>
    let A11 := A.toBlocks₁₁; let A12 := A.toBlocks₁₂
    let A21 := A.toBlocks₂₁; let A22 := A.toBlocks₂₂
    let B11 := B.toBlocks₁₁; let B12 := B.toBlocks₁₂
    let B21 := B.toBlocks₂₁; let B22 := B.toBlocks₂₂
    let M1 := strassenRec m₀ k (A11 + A22) (B11 + B22)
    let M2 := strassenRec m₀ k (A21 + A22) B11
    let M3 := strassenRec m₀ k A11 (B12 - B22)
    let M4 := strassenRec m₀ k A22 (B21 - B11)
    let M5 := strassenRec m₀ k (A11 + A12) B22
    let M6 := strassenRec m₀ k (A21 - A11) (B11 + B12)
    let M7 := strassenRec m₀ k (A12 - A22) (B21 + B22)
    Matrix.fromBlocks
      (M1 + M4 - M5 + M7)
      (M3 + M5)
      (M2 + M4)
      (M1 - M2 + M3 + M6)

/-- **Recursive Strassen correctness.** The fuel-recursive Strassen multiply
    equals the ordinary matrix product, for any fuel. Induction on fuel: the base
    is `*`; the step rewrites the seven recursive products to `*` via the IH,
    reassembles via `Matrix.fromBlocks_toBlocks`, and closes with the
    non-commutative block Strassen identity `strassen_blocks_eq`. -/
theorem strassenRec_eq (m₀ : Type*) [Fintype m₀] [DecidableEq m₀] :
    ∀ (fuel : ℕ) (A B : Matrix (dim m₀ fuel) (dim m₀ fuel) R),
      strassenRec m₀ fuel A B = A * B
  | 0, A, B => rfl
  | (k + 1), A, B => by
    simp only [strassenRec, strassenRec_eq m₀ k]
    rw [strassen_blocks_eq, Matrix.fromBlocks_toBlocks, Matrix.fromBlocks_toBlocks]
    rfl

end Transfer.Examples.CoqEAL.StrassenRec
