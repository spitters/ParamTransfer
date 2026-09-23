/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer
open Transfer Transfer.Param Transfer.ExampleField

/-!
# The examples of `README.md`

Every code block of the repository's `README.md` is a verbatim excerpt of this
file. The field `F` and its operations `bbFieldMul`/`bbFieldAdd` come from
`Transfer.Examples.ExampleField`; `Transfer.Base.Related` registers `bbFieldMul`
and `bbFieldAdd` as `RelatedBinOp` realizations of `*` and `+`.
-/

set_option autoImplicit false

namespace Transfer.Readme

/-! ## Synthesis -/

example (a b c : F) : Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c) :=
  inferInstance        -- composed from the registered RelatedBinOp squares

/-! ## Transfer -/

-- ℤ ↠ ZMod p: an integer fact transfers to its modular image.
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) + 0 = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, x + 0 = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) h
  rw [← hix]; exact h

#transfer (fun x : Nat => Nat.succ x * x)   -- ⟦·⟧ : the term + its relatedness proof

/-! ## Congruence -/

example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_solve

/-! ## `param_auto` -/

example (a : Nat) : a + 0 = a := by param_auto                    -- Eq
example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by param_auto  -- ≤, via gcongr
example (a b : Nat) :                                             -- cast graph, via norm_cast
    ((a + b : Nat) : Int) = (a : Int) + b := by param_auto
example (a b c : F) :                                             -- registered rep. change, via rcongr
    a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_auto

/-! ## Deriving -/

namespace Derive

inductive Pair (A B : Type) | mk : A → B → Pair A B
  deriving Param

end Derive

/-! ## Quick start -/

namespace QuickStart

-- register a witness
def double (n : ℕ) : ℕ := 2 * n
@[param] theorem doubleR : RArrow Eq Eq double double := fun _ _ h => congrArg double h

-- transfer a ∀-statement across ℤ ↠ ZMod p (domain relation auto-resolved)
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) + 0 = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, x + 0 = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) h
  rw [← hix]; exact h

-- derive the relation for a data type
inductive Pair (A B : Type) | mk : A → B → Pair A B deriving Param

-- close a representation-change equation by congruence
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_solve

end QuickStart

end Transfer.Readme
