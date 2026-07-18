/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# CoqEAL `rational`/`binrat`, ported to Lean — num/den pairs refine `ℚ`

CoqEAL's `rational` refines MathComp rationals to numerator/denominator pairs.
Here a pair `ℤ × ℤ` refines `ℚ` via `toRat` (division by zero folds to `0`, so the
relation is a total map, non-injective). The concrete componentwise product
`binMul` refines `ℚ` multiplication — the CoqEAL `Rmul` square — and it holds
*unconditionally*, without a `den ≠ 0` side condition, because `div_mul_div_comm`
is an identity in a division ring.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Transfer.Examples.CoqEAL.BinRat

/-- A numerator/denominator pair, refining `ℚ`. -/
abbrev BinRat : Type := ℤ × ℤ

/-- Decode a pair to the rational it denotes (`/` folds a zero denominator to `0`). -/
def toRat : BinRat → ℚ
  | (n, d) => (n : ℚ) / (d : ℚ)

/-- Concrete multiplication: multiply numerators and denominators. -/
def binMul : BinRat → BinRat → BinRat
  | (n₁, d₁), (n₂, d₂) => (n₁ * n₂, d₁ * d₂)

/-- **The CoqEAL `Rmul` refinement square.** Componentwise multiplication of pairs
    refines `ℚ` multiplication: `toRat (binMul x y) = toRat x * toRat y`,
    unconditionally (via `div_mul_div_comm`). -/
theorem toRat_binMul (x y : BinRat) : toRat (binMul x y) = toRat x * toRat y := by
  obtain ⟨n₁, d₁⟩ := x
  obtain ⟨n₂, d₂⟩ := y
  simp only [toRat, binMul]
  push_cast
  rw [div_mul_div_comm]

end Transfer.Examples.CoqEAL.BinRat
