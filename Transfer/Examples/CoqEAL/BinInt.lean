/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Examples.CoqEAL.BinNat
import Mathlib.Data.Int.Cast.Lemmas

/-!
# CoqEAL `binint`, ported to Lean — sign + magnitude refines `ℤ`

CoqEAL's `binint` refines MathComp integers to a signed representation. Here a
`Bool × List Bool` — a sign bit (`true = negative`) with a little-endian
magnitude — refines `ℤ` via `toInt`, reusing `BinNat.toNat` for the magnitude.
The concrete sign flip `binNeg` refines `ℤ` negation (the CoqEAL `Rneg` square).

The relation is non-injective (`+0` and `-0` both denote `0`), a map-level
refinement — the same shape as the companion `binnat`, `seqpoly`, and `seqmatrix`
data refinements.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Transfer.Examples.CoqEAL.BinInt

open Transfer.Examples.CoqEAL.BinNat (toNat)

/-- A sign bit (`true = negative`) with a little-endian magnitude, refining `ℤ`. -/
abbrev BinInt : Type := Bool × List Bool

/-- Decode a signed binary to the integer it denotes. -/
def toInt : BinInt → ℤ
  | (s, l) => if s then -(toNat l : ℤ) else (toNat l : ℤ)

/-- Concrete negation: flip the sign bit. -/
def binNeg : BinInt → BinInt
  | (s, l) => (!s, l)

/-- **The CoqEAL `Rneg` refinement square.** The concrete sign flip refines `ℤ`
    negation: `toInt (binNeg x) = -(toInt x)`. -/
theorem toInt_binNeg (x : BinInt) : toInt (binNeg x) = -(toInt x) := by
  obtain ⟨s, l⟩ := x
  cases s <;> simp [toInt, binNeg]

end Transfer.Examples.CoqEAL.BinInt
