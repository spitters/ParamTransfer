/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import ReprTransfer
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# `decide_zmod`: deciding ground ring identities over `ZMod m` by bounded residue computation

`HexDecide` transfers a *single* `ZMod m` multiplication to an integer
multiply-then-`%m` (`residueMulReal`). A ground ring identity — one built from
`+`, `*`, `-`, `neg`, `^` over concrete `ZMod m` numerals — is a whole expression
tree. This module lifts that single-op transfer to the tree (the
`ReprTransferExpr.OpExpr.denote_commutes` idea, for the full ring signature), and
reduces mod `m` after **every** node so intermediates stay in `[0, m)`. That
bounded-residue discipline keeps the final check on the GMP `Int` fast path, so
`decide_zmod` closes by **kernel `decide`** — axiom-free (`[propext,
Classical.choice, Quot.sound]`, no `Lean.ofReduceBool`) — where computing inside
`ZMod`/`Fin`, or over unreduced `ℤ`, either stalls the kernel or blows the
coefficients up.

## Main results

* `RingExpr` — the ground ring-expression algebra.
* `RingExpr.denoteA` / `denoteR` — its meaning in `ZMod m`, and the bounded
  integer-residue computation (`% m` after every operation).
* `RingExpr.denoteR_cast` — the abstraction theorem (the homomorphism square
  lifted over the tree by induction).
* `RingExpr.decide_transfer` — the backward transfer a `decide` on the residues
  proves the abstract identity.
* `decide_zmod` — the tactic front: reifies a `ZMod m` equality goal into
  `RingExpr` and closes it via `decide_transfer` + kernel `decide`.

## Scope and extensions

* **Ground** identities only: every leaf must be a `ZMod m` numeral. A goal with a
  free `ZMod m` variable is not decidable and is out of scope (use `ring`/
  `reduce_mod_char` there).
* Exponents are literal `ℕ`. `denoteR` computes `base ^ n` before reducing, so a
  *huge* exponent can build a large intermediate; a binary `powMod` in `denoteR`
  removes that (future).
* A **polynomial** identity `∀ x, p x = q x` reduces to coefficient equality (the
  `seqpoly` refinement, `HexSeqPoly`) — a separate `decide_zmod_poly` on top of
  this core.
-/

set_option autoImplicit false

namespace Transfer.ZModDecide

/-- Ground ring expressions over integer-numeral leaves. -/
inductive RingExpr where
  | lit : ℤ → RingExpr
  | add : RingExpr → RingExpr → RingExpr
  | sub : RingExpr → RingExpr → RingExpr
  | mul : RingExpr → RingExpr → RingExpr
  | neg : RingExpr → RingExpr
  | pow : RingExpr → ℕ → RingExpr
  deriving Repr

namespace RingExpr

/-- The abstract meaning of a `RingExpr` in `ZMod m`. -/
def denoteA (m : ℕ) : RingExpr → ZMod m
  | lit z => (z : ZMod m)
  | add a b => denoteA m a + denoteA m b
  | sub a b => denoteA m a - denoteA m b
  | mul a b => denoteA m a * denoteA m b
  | neg a => - denoteA m a
  | pow a n => (denoteA m a) ^ n

/-- The bounded integer-residue computation: `% m` after every operation, so every
    intermediate stays in `[0, m)` (bar a single `pow`, reduced immediately). This
    is what `decide` evaluates — `Int` arithmetic on the GMP fast path. -/
def denoteR (m : ℤ) : RingExpr → ℤ
  | lit z => z % m
  | add a b => (denoteR m a + denoteR m b) % m
  | sub a b => (denoteR m a - denoteR m b) % m
  | mul a b => (denoteR m a * denoteR m b) % m
  | neg a => (- denoteR m a) % m
  | pow a n => (denoteR m a ^ n) % m

/-- **The abstraction theorem.** The residue computation, cast back into `ZMod m`,
    equals the abstract value: the single-op commuting square (`% m` invisible under
    `Int.cast`, `ZMod.intCast_mod`) lifted over the tree by induction. -/
theorem denoteR_cast (m : ℕ) [NeZero m] (e : RingExpr) :
    ((denoteR (m : ℤ) e : ℤ) : ZMod m) = denoteA m e := by
  induction e with
  | lit z =>
      show (((z % (m:ℤ)) : ℤ) : ZMod m) = _
      rw [ZMod.intCast_mod]; rfl
  | add a b iha ihb =>
      show ((((denoteR (m:ℤ) a + denoteR (m:ℤ) b) % (m:ℤ)) : ℤ) : ZMod m) = _
      rw [ZMod.intCast_mod]; push_cast [iha, ihb]; rfl
  | sub a b iha ihb =>
      show ((((denoteR (m:ℤ) a - denoteR (m:ℤ) b) % (m:ℤ)) : ℤ) : ZMod m) = _
      rw [ZMod.intCast_mod]; push_cast [iha, ihb]; rfl
  | mul a b iha ihb =>
      show ((((denoteR (m:ℤ) a * denoteR (m:ℤ) b) % (m:ℤ)) : ℤ) : ZMod m) = _
      rw [ZMod.intCast_mod]; push_cast [iha, ihb]; rfl
  | neg a iha =>
      show ((((- denoteR (m:ℤ) a) % (m:ℤ)) : ℤ) : ZMod m) = _
      rw [ZMod.intCast_mod]; push_cast [iha]; rfl
  | pow a n iha =>
      show ((((denoteR (m:ℤ) a ^ n) % (m:ℤ)) : ℤ) : ZMod m) = _
      rw [ZMod.intCast_mod]; push_cast [iha]; rfl

/-- **The backward transfer.** A decidable equality of the two bounded residue
    computations proves the abstract `ZMod m` identity — `decide` on the residues,
    underwritten by `denoteR_cast` rather than trusted. -/
theorem decide_transfer (m : ℕ) [NeZero m] (e₁ e₂ : RingExpr)
    (h : denoteR (m : ℤ) e₁ = denoteR (m : ℤ) e₂) :
    denoteA m e₁ = denoteA m e₂ := by
  rw [← denoteR_cast m e₁, ← denoteR_cast m e₂, h]

end RingExpr

/-! ## The `decide_zmod` tactic -/

open Lean Elab Tactic Meta RingExpr in
/-- Reify a ground `ZMod m` expression into a `RingExpr` term. Fails on any leaf
    that is not a numeral (e.g. a free variable), keeping the tactic total on the
    ground fragment it is sound for. -/
partial def reifyZMod (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``RingExpr.add) (← reifyZMod a) (← reifyZMod b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``RingExpr.sub) (← reifyZMod a) (← reifyZMod b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``RingExpr.mul) (← reifyZMod a) (← reifyZMod b)
  | (``Neg.neg, #[_, _, a]) =>
      return mkApp (mkConst ``RingExpr.neg) (← reifyZMod a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
      let some nv ← getNatValue? n | throwError "decide_zmod: non-literal exponent {n}"
      return mkApp2 (mkConst ``RingExpr.pow) (← reifyZMod a) (mkNatLit nv)
  | (``OfNat.ofNat, #[_, k, _]) =>
      let some kv ← getNatValue? k | throwError "decide_zmod: non-literal numeral {e}"
      return mkApp (mkConst ``RingExpr.lit) (mkApp (mkConst ``Int.ofNat) (mkNatLit kv))
  | _ => throwError "decide_zmod: cannot reify leaf {e} (not a ground ZMod numeral)"

open Lean Elab Tactic Meta in
/-- Close a ground ring identity over `ZMod m` by bounded residue computation:
    reify both sides, then discharge via `RingExpr.decide_transfer` and a kernel
    `decide` on the reduced integer residues. Axiom-free (no `Lean.ofReduceBool`).
    Every leaf must be a numeral; a free `ZMod m` variable is rejected. -/
elab "decide_zmod" : tactic => do
  let goal ← getMainTarget
  let some (ty, lhs, rhs) := goal.eq? | throwError "decide_zmod: goal is not an equality"
  let (``ZMod, #[m]) := ty.getAppFnArgs | throwError "decide_zmod: goal type is not `ZMod _`"
  let e₁ ← reifyZMod lhs
  let e₂ ← reifyZMod rhs
  let mZ := mkApp (mkConst ``Int.ofNat) m
  let r₁ := mkApp2 (mkConst ``RingExpr.denoteR) mZ e₁
  let r₂ := mkApp2 (mkConst ``RingExpr.denoteR) mZ e₂
  let hProof ← mkDecideProof (← mkEq r₁ r₂)
  let pf ← mkAppM ``RingExpr.decide_transfer #[m, e₁, e₂, hProof]
  (← getMainGoal).assign pf

/-! ## Examples -/

/-- `HexDecide`'s example, now fully automated. -/
example : (2 * 3 : ZMod 5) = (1 * 1 : ZMod 5) := by decide_zmod

/-- A deeper tree — `+`, `-`, `^`, and a large modulus — still one kernel `decide`. -/
example : (((2 : ZMod 7) ^ 3 + 3 * 4) - 5 : ZMod 7) = (1 : ZMod 7) := by decide_zmod

example : ((7 : ZMod 13) ^ 4 + 2 * 9 - 3) = (7 ^ 4 + 2 * 9 - 3 : ZMod 13) := by decide_zmod

example : ((123456789 : ZMod 1000003) * 987654321 + 42)
    = (123456789 * 987654321 + 42 : ZMod 1000003) := by decide_zmod

/-! ## Axiom audit -/

section AxiomAudit

theorem zmod_example_audit : ((7 : ZMod 13) ^ 4 + 2 * 9 - 3) = (7 ^ 4 + 2 * 9 - 3 : ZMod 13) := by
  decide_zmod

/-- info: 'Transfer.ZModDecide.zmod_example_audit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms zmod_example_audit

end AxiomAudit

end Transfer.ZModDecide
