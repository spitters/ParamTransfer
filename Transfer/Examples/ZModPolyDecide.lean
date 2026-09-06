/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import ReprTransfer
public import Transfer.Examples.HexSeqPoly
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# `decide_zmod_poly`: deciding univariate polynomial identities over `ZMod m`

`ZModDecide.decide_zmod` decides a *ground* `ZMod m` equation — every leaf a
numeral — by bounded integer-residue computation. This module lifts that to a
`∀ x : ZMod m` **polynomial** identity `p x = q x`, where `p`/`q` are built from
the variable `x`, `+`, `-`, `*`, `^`, `neg`, and `ZMod m` numerals.

The mathematics is the `seqpoly` change of representation (`HexSeqPoly`): a
polynomial is a dense coefficient list (`HexPoly = List ℤ`), evaluation is Horner
form (`evalC`), and two Horner polynomials agree at every point of `ZMod m` once
their coefficient lists are congruent mod `m` (`evalC_congr_of_dvd`). The variable
is carried symbolically through the whole expression tree by the coefficient
homomorphism lemmas `evalC_cAdd / cScale / cMul / cPow`, proved once over a generic
commutative ring.

## Boundedness

`denoteC` reduces `% m` after **every** coefficient operation (`cAddMod`,
`cMulMod`, `cPowMod`, …), so a coefficient is at most `m²` transiently and `< m`
between steps. A degree-`d` identity produces two lists of about `d + 1`
coefficients, each below `m`; the closing divisibility check runs on those small
integers. Unreduced convolution — repeated `cMul` inside `cPow` — would grow a
coefficient's bit width additively per multiply, the blow-up that makes `ring`
and `native_decide` over `ZMod m` diverge on a high-degree identity.

## Main results

* `PolyExpr` — univariate polynomial expressions with a `var` leaf.
* `PolyExpr.denoteA` — the abstract meaning `ZMod m → ZMod m`.
* `PolyExpr.denoteC` — the bounded coefficient-list normalizer (`% m` after every
  operation), landing in `HexPoly`.
* `PolyExpr.denoteC_correct` — the refinement `denoteA m e x = evalC (denoteC e) x`.
* `PolyExpr.decide_transfer_poly` — the backward transfer: a coefficient-list
  divisibility check proves the abstract identity at every point.
* `decide_zmod_poly` — the tactic front: reifies a `∀ x : ZMod m, _ = _` goal and
  closes it by `decide_transfer_poly` plus a kernel `decide` on the reduced
  coefficient lists. Axiom-free (`[propext, Classical.choice, Quot.sound]`, no
  `Lean.ofReduceBool`).

## Scope

* One variable. Every numeral is a `ZMod m` constant; a second free variable is out
  of scope.
* Exponents are literal `ℕ`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.ZModPolyDecide

open Transfer.Param (HexPoly)

/-! ## The integer-coefficient Horner evaluator (the `seqpoly` read-out) -/

variable {R : Type*} [CommRing R]

/-- Horner evaluation of an integer-coefficient list (low degree first) at `x : R`,
    coefficients cast in through `Int.cast`. This is the `List ℤ` (`HexPoly`)
    representation of a polynomial read out over `R`. -/
def evalC : List ℤ → R → R
  | [], _ => 0
  | c :: cs, x => (c : R) + x * evalC cs x

/-- Coefficient-wise addition. -/
def cAdd : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: cAdd p q

/-- Scalar multiplication of a coefficient list. -/
def cScale (a : ℤ) : List ℤ → List ℤ
  | [] => []
  | b :: q => (a * b) :: cScale a q

/-- Coefficient-wise (convolution) product. -/
def cMul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: p, q => cAdd (cScale a q) (0 :: cMul p q)

/-- Coefficient-wise subtraction. -/
def cSub (p q : List ℤ) : List ℤ := cAdd p (cScale (-1) q)

/-- Reduce every coefficient mod `m`, keeping each entry in `[0, m)`. -/
def cReduce (m : ℤ) (l : List ℤ) : List ℤ := l.map (fun c => c % m)

@[simp] theorem evalC_nil (x : R) : evalC ([] : List ℤ) x = 0 := rfl

@[simp] theorem evalC_cons (c : ℤ) (cs : List ℤ) (x : R) :
    evalC (c :: cs) x = (c : R) + x * evalC cs x := rfl

/-! ### Coefficient homomorphism lemmas — proved once, generically over `R` -/

theorem evalC_cAdd (p q : List ℤ) (x : R) :
    evalC (cAdd p q) x = evalC p x + evalC q x := by
  induction p generalizing q with
  | nil => simp [cAdd]
  | cons a p ih =>
    cases q with
    | nil => simp [cAdd]
    | cons b q => simp only [cAdd, evalC_cons, ih]; push_cast; ring

theorem evalC_cScale (a : ℤ) (q : List ℤ) (x : R) :
    evalC (cScale a q) x = (a : R) * evalC q x := by
  induction q with
  | nil => simp [cScale]
  | cons b q ih => simp only [cScale, evalC_cons, ih]; push_cast; ring

theorem evalC_cMul (p q : List ℤ) (x : R) :
    evalC (cMul p q) x = evalC p x * evalC q x := by
  induction p generalizing q with
  | nil => simp [cMul]
  | cons a p ih =>
    simp only [cMul, evalC_cAdd, evalC_cScale, evalC_cons, ih]; ring

theorem evalC_cSub (p q : List ℤ) (x : R) :
    evalC (cSub p q) x = evalC p x - evalC q x := by
  simp only [cSub, evalC_cAdd, evalC_cScale]; push_cast; ring

/-- Reducing coefficients mod `m` leaves the value over `ZMod m` unchanged
    (`ZMod.intCast_mod`), lifted over the list. -/
theorem evalC_cReduce (m : ℕ) (l : List ℤ) (x : ZMod m) :
    evalC (cReduce (m : ℤ) l) x = evalC l x := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [cReduce, List.map_cons, evalC_cons] at ih ⊢
    rw [ih, ZMod.intCast_mod]

/-! ### The decision step over `ZMod m` -/

/-- A coefficient list all of whose entries reduce to `0` in `ZMod m` evaluates to
    `0` at every point. -/
theorem evalC_eq_zero_of_all {m : ℕ} (ds : List ℤ)
    (h : ∀ c ∈ ds, ((c : ZMod m) = 0)) (x : ZMod m) : evalC ds x = 0 := by
  induction ds with
  | nil => simp
  | cons c cs ih =>
    simp only [evalC_cons]
    rw [h c (by simp), ih (fun c hc => h c (by simp [hc]))]
    ring

/-- Two Horner polynomials are equal at every point of `ZMod m` once every
    coefficient of their difference `cSub p q` is divisible by `m` — a decidable
    integer predicate. This is `HexDecide.residueMulReal`'s
    `eq_transfer_backward` step lifted from a single binop to a whole polynomial. -/
theorem evalC_congr_of_dvd {m : ℕ} (p q : List ℤ)
    (h : ∀ c ∈ cSub p q, (m : ℤ) ∣ c) (x : ZMod m) :
    evalC p x = evalC q x := by
  have hz : evalC (cSub p q) x = 0 := by
    apply evalC_eq_zero_of_all
    intro c hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd c m).mpr (h c hc)
  rw [evalC_cSub] at hz
  exact sub_eq_zero.mp hz

/-! ## The bounded coefficient operations (`% m` after every step) -/

/-- Coefficient-wise addition, reduced mod `m`. -/
def cAddMod (m : ℤ) (p q : List ℤ) : List ℤ := cReduce m (cAdd p q)

/-- Coefficient-wise subtraction, reduced mod `m`. -/
def cSubMod (m : ℤ) (p q : List ℤ) : List ℤ := cReduce m (cSub p q)

/-- Convolution product, reduced mod `m`. -/
def cMulMod (m : ℤ) (p q : List ℤ) : List ℤ := cReduce m (cMul p q)

/-- Coefficient-wise negation, reduced mod `m`. -/
def cNegMod (m : ℤ) (p : List ℤ) : List ℤ := cReduce m (cScale (-1) p)

/-- Power by repeated reduced multiplication, so coefficients stay `< m`. -/
def cPowMod (m : ℤ) (p : List ℤ) : ℕ → List ℤ
  | 0 => cReduce m [1]
  | n + 1 => cMulMod m p (cPowMod m p n)

theorem evalC_cAddMod (m : ℕ) (p q : List ℤ) (x : ZMod m) :
    evalC (cAddMod (m : ℤ) p q) x = evalC p x + evalC q x := by
  simp only [cAddMod, evalC_cReduce, evalC_cAdd]

theorem evalC_cSubMod (m : ℕ) (p q : List ℤ) (x : ZMod m) :
    evalC (cSubMod (m : ℤ) p q) x = evalC p x - evalC q x := by
  simp only [cSubMod, evalC_cReduce, evalC_cSub]

theorem evalC_cMulMod (m : ℕ) (p q : List ℤ) (x : ZMod m) :
    evalC (cMulMod (m : ℤ) p q) x = evalC p x * evalC q x := by
  simp only [cMulMod, evalC_cReduce, evalC_cMul]

theorem evalC_cNegMod (m : ℕ) (p : List ℤ) (x : ZMod m) :
    evalC (cNegMod (m : ℤ) p) x = - evalC p x := by
  simp only [cNegMod, evalC_cReduce, evalC_cScale]; push_cast; ring

theorem evalC_cPowMod (m : ℕ) (p : List ℤ) (n : ℕ) (x : ZMod m) :
    evalC (cPowMod (m : ℤ) p n) x = (evalC p x) ^ n := by
  induction n with
  | zero => rw [cPowMod, evalC_cReduce]; simp [evalC]
  | succ n ih => rw [cPowMod, evalC_cMulMod, ih, pow_succ]; ring

/-! ## The polynomial-expression front -/

/-- Univariate polynomial expressions over `ZMod m`: a variable leaf, integer-
    numeral constants, and the ring operations. -/
inductive PolyExpr where
  | var : PolyExpr
  | lit : ℤ → PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | sub : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | neg : PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving Repr

namespace PolyExpr

/-- The abstract meaning of a `PolyExpr` as a function `ZMod m → ZMod m`. -/
def denoteA (m : ℕ) : PolyExpr → ZMod m → ZMod m
  | .var => fun x => x
  | .lit z => fun _ => (z : ZMod m)
  | .add a b => fun x => denoteA m a x + denoteA m b x
  | .sub a b => fun x => denoteA m a x - denoteA m b x
  | .mul a b => fun x => denoteA m a x * denoteA m b x
  | .neg a => fun x => - denoteA m a x
  | .pow a n => fun x => (denoteA m a x) ^ n

/-- The bounded coefficient-list normalizer: the polynomial's dense coefficient
    list (`HexPoly`), reduced mod `m` after every operation. -/
def denoteC (m : ℤ) : PolyExpr → HexPoly
  | .var => cReduce m [0, 1]
  | .lit z => cReduce m [z]
  | .add a b => cAddMod m (denoteC m a) (denoteC m b)
  | .sub a b => cSubMod m (denoteC m a) (denoteC m b)
  | .mul a b => cMulMod m (denoteC m a) (denoteC m b)
  | .neg a => cNegMod m (denoteC m a)
  | .pow a n => cPowMod m (denoteC m a) n

/-- **The refinement.** The abstract value at `x` equals the Horner evaluation of
    the bounded coefficient list at `x`: the coefficient homomorphism lifted over
    the expression tree, with every reduction step invisible over `ZMod m`. -/
theorem denoteC_correct (m : ℕ) (e : PolyExpr) (x : ZMod m) :
    denoteA m e x = evalC (denoteC (m : ℤ) e) x := by
  induction e with
  | var => simp only [denoteA, denoteC, evalC_cReduce]; simp [evalC]
  | lit z => simp only [denoteA, denoteC, evalC_cReduce]; simp [evalC]
  | add a b iha ihb => simp only [denoteA, denoteC, evalC_cAddMod, iha, ihb]
  | sub a b iha ihb => simp only [denoteA, denoteC, evalC_cSubMod, iha, ihb]
  | mul a b iha ihb => simp only [denoteA, denoteC, evalC_cMulMod, iha, ihb]
  | neg a iha => simp only [denoteA, denoteC, evalC_cNegMod, iha]
  | pow a n iha => simp only [denoteA, denoteC, evalC_cPowMod, iha]

/-- The decidable coefficient-list divisibility check on the difference of the two
    normalized polynomials. -/
def allDvdB (m : ℤ) (l : List ℤ) : Bool := l.all (fun c => decide (m ∣ c))

theorem allDvdB_true {m : ℤ} {l : List ℤ} (h : allDvdB m l = true) :
    ∀ c ∈ l, m ∣ c := by
  intro c hc
  exact of_decide_eq_true ((List.all_eq_true.mp h) c hc)

/-- The reflective coefficient check: every coefficient of the normalized
    difference is divisible by `m`. -/
def polyCheck (m : ℤ) (e₁ e₂ : PolyExpr) : Bool :=
  allDvdB m (cSub (denoteC m e₁) (denoteC m e₂))

/-- **The backward transfer.** When the coefficient check passes, the two abstract
    polynomials agree at every point of `ZMod m`. Underwritten by `denoteC_correct`
    and `evalC_congr_of_dvd`, so the `decide` on the reduced coefficients is proof,
    not trust. -/
theorem decide_transfer_poly (m : ℕ) (e₁ e₂ : PolyExpr)
    (h : polyCheck (m : ℤ) e₁ e₂ = true) (x : ZMod m) :
    denoteA m e₁ x = denoteA m e₂ x := by
  rw [denoteC_correct m e₁ x, denoteC_correct m e₂ x]
  exact evalC_congr_of_dvd (denoteC (m : ℤ) e₁) (denoteC (m : ℤ) e₂) (allDvdB_true h) x

end PolyExpr

/-! ## The `decide_zmod_poly` tactic -/

open Lean Elab Tactic Meta PolyExpr in
/-- Reify a `ZMod m` expression into a `PolyExpr`, mapping the free variable
    `xvar` to `PolyExpr.var`. Fails on any leaf that is neither the variable nor a
    numeral. -/
meta partial def reifyPoly (xvar : FVarId) (e : Expr) : MetaM Expr := do
  if let .fvar fid := e then
    if fid == xvar then return mkConst ``PolyExpr.var
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``PolyExpr.add) (← reifyPoly xvar a) (← reifyPoly xvar b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``PolyExpr.sub) (← reifyPoly xvar a) (← reifyPoly xvar b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
      return mkApp2 (mkConst ``PolyExpr.mul) (← reifyPoly xvar a) (← reifyPoly xvar b)
  | (``Neg.neg, #[_, _, a]) =>
      return mkApp (mkConst ``PolyExpr.neg) (← reifyPoly xvar a)
  | (``HPow.hPow, #[_, _, _, _, a, n]) =>
      let some nv ← getNatValue? n | throwError "decide_zmod_poly: non-literal exponent {n}"
      return mkApp2 (mkConst ``PolyExpr.pow) (← reifyPoly xvar a) (mkNatLit nv)
  | (``OfNat.ofNat, #[_, k, _]) =>
      let some kv ← getNatValue? k | throwError "decide_zmod_poly: non-literal numeral {e}"
      return mkApp (mkConst ``PolyExpr.lit) (mkApp (mkConst ``Int.ofNat) (mkNatLit kv))
  | _ => throwError "decide_zmod_poly: cannot reify leaf {e} (not the variable or a numeral)"

open Lean Elab Tactic Meta in
/-- Close a univariate polynomial identity `∀ x : ZMod m, p x = q x` by bounded
    coefficient-list computation: introduce `x`, reify both sides into `PolyExpr`,
    then discharge via `PolyExpr.decide_transfer_poly` and a kernel `decide` on the
    reduced coefficient lists. Axiom-free (no `Lean.ofReduceBool`). Every leaf must
    be the variable or a numeral. -/
elab "decide_zmod_poly" : tactic => do
  let (fvarId, mvarId) ← (← getMainGoal).intro `x
  mvarId.withContext do
    let goal ← mvarId.getType
    let some (ty, lhs, rhs) := goal.eq? | throwError "decide_zmod_poly: goal body is not an equality"
    let (``ZMod, #[m]) := ty.getAppFnArgs | throwError "decide_zmod_poly: goal type is not `ZMod _`"
    let e₁ ← reifyPoly fvarId lhs
    let e₂ ← reifyPoly fvarId rhs
    let mZ := mkApp (mkConst ``Int.ofNat) m
    let chk := mkApp3 (mkConst ``PolyExpr.polyCheck) mZ e₁ e₂
    let hProof ← mkDecideProof (← mkEq chk (mkConst ``Bool.true))
    let pf ← mkAppM ``PolyExpr.decide_transfer_poly #[m, e₁, e₂, hProof]
    mvarId.assign (mkApp pf (mkFVar fvarId))

/-! ## Examples -/

/-- The square of a linear factor, expanded. -/
example : ∀ x : ZMod 7, (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by decide_zmod_poly

/-- A difference of squares over a larger modulus, with a reduced constant term. -/
example : ∀ x : ZMod 13, (x - 3) * (x + 3) = x ^ 2 - 9 := by decide_zmod_poly

/-- A cube of a linear factor. -/
example : ∀ x : ZMod 5, (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by decide_zmod_poly

/-- A degree-2 identity over a six-digit modulus, whose constant term only agrees
    after reduction mod `m`. -/
example : ∀ x : ZMod 1000003,
    (x + 123456) * (x - 654321) = x ^ 2 - 530865 * x - 123456 * 654321 := by
  decide_zmod_poly

/-! ## Axiom audit -/

section AxiomAudit

theorem poly_example_audit : ∀ x : ZMod 7, (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  decide_zmod_poly

/-- info: 'Transfer.ZModPolyDecide.poly_example_audit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms poly_example_audit

end AxiomAudit

end Transfer.ZModPolyDecide
