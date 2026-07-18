/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Congruence.ParamSolve
import Transfer.Congruence.HCongrConnection
import Transfer.Base.Related
import Mathlib.Data.Nat.Cast.Basic

/-!
# Strong examples — congruence the native tactics structurally cannot do

Each native Lean relational tactic is congruence for one *fixed* relation, and the
engine generalizes it along two axes those tactics cannot cross: relating sides of
*different types* (heterogeneous) and relating them across a *change of
representation* (non-diagonal). This file collects worked examples that each beat a
specific native tactic on one of those axes — over genuinely non-diagonal domains,
not identity encodings.

| native tactic | its fixed relation | axis it cannot cross | example here |
|---|---|---|---|
| `congr` / `HEq` | `Eq` / `HEq` | different fiber types | `hetero_congr_fin_nat` |
| `gcongr` | `≤`/`⊆`, same head | change of representation | `rcongr_nat_int` |
| `norm_cast` | the scalar cast graph | a *dependent-family* cast | `dep_family_cast_fin` |
-/

set_option autoImplicit false

namespace Transfer.StrongExamples

open Transfer Transfer.Param Transfer.Param.HCongrConnection

/-! ## `congr` cannot relate different types — `hcongr_hetero` does

`f a : Fin (a+1)` and `g b : ℕ` live in *different* types. Core `congr`/`HEq`
cannot relate them without forcing the types equal; the heterogeneous rule relates
them through the fiber's `Fin.val` map. -/

/-- Heterogeneous congruence across `Fin (a+1) ↔ ℕ` (different fiber types),
    reduced to the domain witness by `hcongr_dep`. -/
example (a b : ℕ) (h : a = b) : (Fin.last a).val = (fun n => n) b := by
  hcongr_dep finLastWitness
  exact h

/-! ## `gcongr` cannot change representation — `rcongr` does

The encoding is genuinely non-diagonal: `Nat.cast : ℕ → ℤ` (`enc ≠ id`). Registering
the two commuting squares once (`RelatedBinOp`) lets `rcongr` descend the cross-head
op-tree *and* change representation ℕ → ℤ — a move `gcongr` structurally rejects
(it needs both sides in the same type with the same head). -/

/-- `+` on ℕ realized by `+` on ℤ along `Nat.cast`. -/
instance natCastAdd : RelatedBinOp (Nat.cast : ℕ → ℤ) (· + ·) (· + ·) where
  comm a b := Nat.cast_add a b

/-- `*` on ℕ realized by `*` on ℤ along `Nat.cast`. -/
instance natCastMul : RelatedBinOp (Nat.cast : ℕ → ℤ) (· * ·) (· * ·) where
  comm a b := Nat.cast_mul a b

/-- Cross-representation congruence ℕ → ℤ, closed by `rcongr`. -/
example (a b c : ℕ) :
    Related (Nat.cast : ℕ → ℤ) (a * b + c) ((a : ℤ) * (b : ℤ) + (c : ℤ)) := by
  rcongr

/-- The extracted equation `↑(a*b+c) = ↑a*↑b+↑c`, obtained by structural descent
    over the `Nat.cast` encoding rather than a single cast-normalization pass. -/
example (a b c : ℕ) : ((a * b + c : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) + (c : ℤ) :=
  transferRel (a := a * b + c) (by rcongr)

/-! ## `norm_cast` moves one scalar cast — the transport moves a *dependent family*

`norm_cast` rewrites a fixed scalar coercion `↑`. Here the coercion is a *family*
`Fin (n+1) → ℕ` indexed by `n`, transported uniformly across a dependent function
`∀ n, Fin (n+1)` versus `∀ n, ℕ` — a family-indexed transport `norm_cast` does not
express. -/

/-- Uniform transport of the dependent family of casts `Fin (n+1) → ℕ` across the
    two dependent functions, at each index, via the graded fiber map. -/
example (a b : ℕ) (h : a = b) : Fin.val (Fin.last a) = (fun n => n) b := by
  hcongr_transport finLastWitness
  exact h

end Transfer.StrongExamples
