/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: ParamTransfer Contributors
-/
module

public import Transfer.Integrations.ParamRCompOk

/-!
# `RCompOk` over a two-outcome test monad

`OkFail` is a monad with a successful outcome `ok a` and a failure `fail`,
registered with `Std.Do` at postcondition shape `.except PUnit .pure` (a `fail`
is an exception, so a partial-correctness postcondition `⇓?` holds of it
trivially). Programs over `OkFail` model machine arithmetic that fails on
overflow; programs over `Id Int` model the same computation over unbounded
integers. The value relation is the cast `castRel x y := ((x : Int) = y)`.

* `addChk_rcompOk` — a checked addition (an `ite` on the `OkFail` side only)
  against `pure (x + y)`; `rcomp_ok` applies `RCompOk.ite_left`, the failing
  branch is closed by the supplied lemma `OkFail.rcompOk_fail`.
* `prog_rcompOk` — two sequenced checked additions, with `addChk_rcompOk`
  supplied as a lemma for the calls.
* `sum_rcompOk` — a `for` loop over `[0:n]` with a checked accumulator.
* `clamp_rcompOk` — conditionals on both sides, with conditions equivalent under
  the cast.
* `prog_spec` — a fact proved about the `Id` program, transferred to every
  successful execution of the `OkFail` program by `RCompOk.transfer`.
* `transfer_reverse_false` — the reverse direction of `RCompOk.transfer` is
  false: `fail` is related to `pure 0` and satisfies the partial postcondition
  `False`, which `pure 0` does not satisfy.
* `ofFn_arrayRel` — `ArrayRel` between an array of naturals and its cast.
-/

@[expose] public section

set_option autoImplicit false

open Std.Do

namespace Transfer.Param.RCompOkDemo

/-- A monad with a successful outcome and a failure outcome. -/
inductive OkFail (α : Type) where
  /-- Successful termination with a value. -/
  | ok (a : α)
  /-- Failure. -/
  | fail

namespace OkFail

/-- Sequencing: `fail` propagates, `ok a` continues with `a`. -/
def bind {α β : Type} : OkFail α → (α → OkFail β) → OkFail β
  | .ok a, f => f a
  | .fail, _ => .fail

instance : Monad OkFail where
  pure := .ok
  bind := OkFail.bind

instance : LawfulMonad OkFail := LawfulMonad.mk'
  (id_map := by intro α x; cases x <;> rfl)
  (pure_bind := by intros; rfl)
  (bind_assoc := by intro α β γ x f g; cases x <;> rfl)

/-- The predicate transformer of an `OkFail` computation: `ok a` applies the
    success postcondition to `a`, `fail` is the exception postcondition. -/
def wpOf {α : Type} : OkFail α → PredTrans (.except PUnit .pure) α
  | .ok a => PredTrans.pure a
  | .fail => PredTrans.throw ⟨⟩

instance : WP OkFail (.except PUnit .pure) where
  wp := wpOf

instance : WPMonad OkFail (.except PUnit .pure) where
  wp_pure _ := rfl
  wp_bind x f := by cases x <;> rfl

/-- `fail` is `RCompOk`-related to every total computation. -/
theorem rcompOk_fail {N : Type → Type} [WP N .pure] {α α' : Type} {R : α → α' → Prop}
    (c' : N α') : RCompOk R (OkFail.fail : OkFail α) c' :=
  RCompOk.of_wp_false c' (fun _ => True.intro)

end OkFail

/-- The cast relation between naturals and integers. -/
def castRel (x : Nat) (y : Int) : Prop := (x : Int) = y

/-- Addition of naturals that fails when the sum is at least `256`. -/
def addChk (a b : Nat) : OkFail Nat :=
  if a + b < 256 then pure (a + b) else .fail

/-- A successful checked addition returns the integer sum of the cast operands. -/
theorem addChk_rcompOk {a b : Nat} {x y : Int} (hx : (a : Int) = x) (hy : (b : Int) = y) :
    RCompOk castRel (addChk a b) (pure (x + y) : Id Int) := by
  unfold addChk
  rcomp_ok [OkFail.rcompOk_fail]
  simp [castRel, ← hx, ← hy]

/-- Two sequenced checked additions. -/
def prog (a b c : Nat) : OkFail Nat := do
  let s ← addChk a b
  addChk s c

/-- The integer counterpart of `prog`. -/
def progId (a b c : Int) : Id Int := do
  let s ← pure (a + b)
  pure (s + c)

theorem prog_rcompOk (a b c : Nat) :
    RCompOk castRel (prog a b c) (progId a b c) := by
  unfold prog progId
  rcomp_ok [addChk_rcompOk]
  all_goals first | rfl | assumption

/-- A checked sum of `0, …, n - 1`. -/
def sumChk (n : Nat) : OkFail Nat := do
  let mut acc := 0
  for i in [0:n] do
    acc ← addChk acc i
  return acc

/-- The integer counterpart of `sumChk`. -/
def sumId (n : Nat) : Id Int := do
  let mut acc : Int := 0
  for i in [0:n] do
    acc ← pure (acc + i)
  return acc

theorem sum_rcompOk (n : Nat) : RCompOk castRel (sumChk n) (sumId n) := by
  unfold sumChk sumId
  rcomp_ok [addChk_rcompOk]
  all_goals first | exact rfl | assumption

/-- Increments values of at least `10`, with a checked addition. -/
def clampChk (a : Nat) : OkFail Nat :=
  if a < 10 then pure a else addChk a 1

/-- The integer counterpart of `clampChk`. -/
def clampId (x : Int) : Id Int :=
  if x < 10 then pure x else pure (x + 1)

theorem clamp_rcompOk (a : Nat) : RCompOk castRel (clampChk a) (clampId a) := by
  unfold clampChk clampId
  rcomp_ok [addChk_rcompOk]
  all_goals first | exact rfl | omega

theorem progId_spec (a b c : Int) : ⊢ₛ wp⟦progId a b c⟧ (⇓ r => ⌜r = a + b + c⌝) :=
  SPred.pure_intro rfl

/-- Every successful execution of `prog a b c` returns `a + b + c`, transferred
    from `progId_spec`. -/
theorem prog_spec (a b c : Nat) :
    ⊢ₛ wp⟦prog a b c⟧ (⇓? r => ⌜(r : Int) = a + b + c⌝) :=
  (prog_rcompOk a b c).transfer (fun _ _ hr hq => hr.trans hq) (progId_spec a b c)

/-- `RCompOk.transfer` has no converse: `fail` is related to `pure 0` and satisfies
    every partial-correctness postcondition, while `pure 0` does not return a
    value satisfying `False`. -/
theorem transfer_reverse_false :
    ¬ ∀ (c : OkFail Nat) (c' : Id Nat) (Q : Nat → Prop), RCompOk (· = ·) c c' →
      (⊢ₛ wp⟦c⟧ (⇓? a => ⌜Q a⌝)) → ⊢ₛ wp⟦c'⟧ (⇓ a => ⌜Q a⌝) := fun h =>
  h .fail (pure 0) (fun _ => False) (OkFail.rcompOk_fail _) (fun _ => True.intro) True.intro

theorem ofFn_arrayRel {n : Nat} (f : Fin n → Nat) :
    ArrayRel castRel (Array.ofFn f) (Array.ofFn fun k => (f k : Int)) :=
  (ArrayRel.ofFn_iff f _).mpr ⟨by simp, fun k _ => by simp [castRel]⟩

/-- `param_transfer` dispatches an `RCompOk` goal to `rcomp_ok`. -/
example (a : Nat) : RCompOk castRel (pure a : OkFail Nat) (pure (a : Int) : Id Int) := by
  param_transfer
  exact rfl

end Transfer.Param.RCompOkDemo
