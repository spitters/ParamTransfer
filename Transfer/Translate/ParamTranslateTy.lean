/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Lean
import Transfer.Translate.ParamTranslate

/-!
# The binder **type-translation** rule (change-of-representation)

`ParamTranslate.lean` builds the term-level parametricity translation `⟦·⟧` with
the four core rules `var`/`const`/`app`/`lam`, but its `lam` rule fixes the
binder's domain relation to the diagonal `Eq`: a bound `x : A` is transferred to
`x' : A` *at the same type*, with relatedness hypothesis `x = x'`. That is the
same-representation fragment.

This module lifts that restriction. It adds the type-translation component of
`⟦·⟧` — the `sort`/binder-domain rule — so a binder may change representation:
`x : A` ↦ `x' : A'` with a relatedness hypothesis `xr : PA x x'` at a *non-`Eq`*
relation `PA : A → A' → Prop`. Concretely it provides:

* `translateTy` — `⟦·⟧` on a *type* expr `A`, returning `(A', PA)` where
  `A'` is the transferred type and `PA : A → A' → Prop` is the chosen relation:
  - a registered base type name → its `(A', PA)` from the type database;
  - an arrow `A → B` → `(A' → B', RArrow PA_A PA_B)` (recurse on domain and
    codomain, then assemble both the arrow type and the function relation
    `RArrow` as `Expr`s);
  - any unregistered/other type → the diagonal `(A, @Eq A)` (same-representation
    default, so `translateFull` degenerates to `translate` on `Eq`-only inputs).
* `translateFull` — a copy of `translate` whose `lam` rule consults
  `translateTy` to pick the binder's domain type and relation. `var`/`const`/
  `app` are unchanged.

The type database is the type-level analogue of `translate`'s constant database:
a `NameMap (Expr × Expr)` mapping a base type's name to `(A', PA)` (the type's
`Param.R`). As there, it is passed explicitly rather than held in a persistent
attribute.

Combined with the `app`/`const`/`var` rules, this covers cross-representation
transfer: under a change-of-representation binder, a registered constant
`g : A → B` (whose database witness `gR : RArrow PA PB g g'` relates it to its
transferred `g'`) is transported, and the synthesized proof relates `g x` to
`g' x'` across the *non-`Eq*` binder relation.

## Scope

`translateTy`'s arrow case is first-order: it handles a non-dependent arrow
`A → B`. A dependent `Π (x : A), B x` — where the binder type `B` depends on an
earlier binder — is not handled (the recursion would have to thread the
parametricity context into `translateTy`); such forall-exprs fall to the `Eq`
default. `Type`-valued motives (relating types-as-data, the `peano_bin_nat`
case) likewise remain the univalence-capped boundary, exactly as for
`ParamTranslate`. This module adds the change-of-representation binder rule
for the first-order fragment.
-/

set_option autoImplicit false

open Lean Meta

namespace Transfer.Param

/-! ## The type-translation rule `⟦·⟧` on types -/

/-- `⟦·⟧` on a **type** expr. Given a *type database* `tdb` mapping a base type's
    name to `(A', PA)` (its `Param.R`), returns `(A', PA)` for the input type:
    `A'` is the transferred type, `PA : A → A' → Prop` the chosen relation.

    * a registered base type name → its `(A', PA)` from `tdb`;
    * a non-dependent arrow `A → B` → `(A' → B', RArrow PA_A PA_B)`, recursing on
      domain and codomain and assembling the arrow type and the function relation
      `RArrow` (see `ParamTranslate.RArrow`) as `Expr`s;
    * anything else (unregistered base, dependent `Π`, sorts) → the diagonal
      `(A, @Eq A)`, i.e. treat as the same representation.

    The diagonal default makes `translateFull` agree with `translate` on inputs
    whose binders all sit at `Eq`. -/
partial def translateTy (tdb : NameMap (Expr × Expr)) : Expr → MetaM (Expr × Expr)
  | .const n us => match tdb.find? n with
      | some p => return p
      | none   => do
          let A := Expr.const n us
          return (A, ← mkAppOptM ``Eq #[some A])
  | e@(.forallE _ A B _) =>
      -- only the non-dependent (first-order) arrow case; dependent `Π` falls back
      if B.hasLooseBVars then
        return (e, ← mkAppOptM ``Eq #[some e])
      else do
        let (A', PA_A) ← translateTy tdb A
        let (B', PA_B) ← translateTy tdb B
        let arrTy ← mkArrow A' B'
        let rel   ← mkAppM ``RArrow #[PA_A, PA_B]
        return (arrTy, rel)
  | e => return (e, ← mkAppOptM ``Eq #[some e])

/-! ## The full translation with the change-of-representation `lam` rule -/

/-- The term-level parametricity translation `⟦·⟧` with a **type-directed** `lam`
    rule. Like `ParamTranslate.translate` (same `var`/`const`/`app` rules), but
    the `lam` rule consults `translateTy tdb` on the binder's type to obtain the
    transferred domain `A'` and the binder relation `PA : A → A' → Prop`, then
    introduces `x : A`, `x' : A'`, and `xr : PA x x'` (the relatedness hypothesis
    at the *chosen* relation, not necessarily `Eq`). This is the change-of-
    representation binder rule.

    Returns `(t', tR)` with `t'` the transferred term and `tR` a proof of
    relatedness. With `tdb = ∅` it reduces to `translate` (every binder defaults
    to `Eq`). -/
partial def translateFull (tdb : NameMap (Expr × Expr))
    (ctx : Std.HashMap FVarId (Expr × Expr)) (db : NameMap (Expr × Expr)) :
    Expr → MetaM (Expr × Expr)
  | .fvar fid => match ctx[fid]? with
      | some p => return p
      | none   => throwError "translateFull: unbound variable"
  | .const n _ => match db.find? n with
      | some p => return p
      | none   => throwError "translateFull: unregistered constant `{n}`"
  | .app f a => do
      let (f', fR) ← translateFull tdb ctx db f
      let (a', aR) ← translateFull tdb ctx db a
      -- parametricity application: fR a a' aR : PB (f a) (f' a')
      return (.app f' a', ← mkAppM' fR #[a, a', aR])
  | .lam nm ty b bi => do
      -- type-directed binder: pick the transferred domain `ty'` and relation `PA`
      let (ty', PA) ← translateTy tdb ty
      withLocalDecl nm bi ty fun x =>
      withLocalDecl (nm.appendAfter "'") bi ty' fun x' => do
        -- relatedness hypothesis at the chosen relation: `PA x x'`
        let relTy ← mkAppM' PA #[x, x']
        withLocalDeclD (nm.appendAfter "R") relTy fun xr => do
          let ctx' := ctx.insert x.fvarId! (x', xr)
          let (b', bR) ← translateFull tdb ctx' db (b.instantiate1 x)
          let term  ← mkLambdaFVars #[x'] b'
          let proof ← mkLambdaFVars #[x, x', xr] bR
          return (term, proof)
  | e => throwError "translateFull: unsupported term {e}"

/-! ## A registered change-of-representation pair

A cross-type relation `Nat ~ Int` and a constant witness that survives
it, used by the demo below. `NatIntR n i := (↑n = i)` relates a `Nat` to the
`Int` it injects to; `succR` witnesses that `Nat.succ` and `(· + 1)` send
`NatIntR`-related arguments to `NatIntR`-related results — i.e. `Nat.succ` and
`(· + 1)` are related at `RArrow NatIntR NatIntR`. -/

/-- The relation registering `Nat ↦ Int`: a `Nat` is related to the `Int` it
    injects to. (Non-`Eq` — the two sides have different types.) -/
def NatIntR (n : Nat) (i : Int) : Prop := (n : Int) = i

/-- `Nat.succ` and `(· + 1)` are related at `RArrow NatIntR NatIntR`: they send
    `NatIntR`-related arguments to `NatIntR`-related results. This is the
    database witness for the change-of-representation demo. -/
theorem succR : RArrow NatIntR NatIntR Nat.succ (fun i => i + 1) := by
  intro n i h
  simp only [NatIntR] at *
  omega

/-! ## Demonstrations

`run_meta` blocks build the transferred term + relatedness proof; `inferType`
(which errors on an ill-typed term) kernel-checks each, so these are checked
validations. The demos exercise, in order: (a) `translateTy` on an arrow type;
(b) `translateFull` reproducing the `Eq`-lam regression; (c)
`translateFull` on a binder whose domain *changes representation* (`Nat ↦ Int`)
with a relatedness hypothesis that is not `Eq`. -/

-- (a) `translateTy (Nat → Nat)` returns `(Nat → Nat, RArrow (@Eq Nat) (@Eq Nat))`.
-- Confirms the arrow case assembles the `RArrow` relation as an `Expr`.
run_meta do
  let nat := Expr.const ``Nat []
  let arrTy ← mkArrow nat nat
  let (A', PA) ← translateTy {} arrTy
  logInfo m!"translateTy (Nat → Nat)  A'  = {A'}"
  logInfo m!"                          PA  = {PA}"
  logInfo m!"                          PA : {← inferType PA}"

-- (b) Regression: with an empty type database every binder defaults to `Eq`, so
-- `translateFull` reproduces the `Eq`-lam behaviour of `translate`.
-- `⟦fun (x : Nat) => Nat.succ x⟧` ↦ `fun x' => x'.succ`, proof `∀ x x', x = x' → …`.
run_meta do
  let nat := Expr.const ``Nat []
  let succR ← Lean.Elab.Term.TermElabM.run'
    (Lean.Elab.Term.elabTerm (← `(fun (a a' : Nat) (h : a = a') => congrArg Nat.succ h)) none)
  let db : NameMap (Expr × Expr) := (∅ : NameMap _).insert ``Nat.succ (.const ``Nat.succ [], succR)
  let t := Expr.lam `x nat (.app (.const ``Nat.succ []) (.bvar 0)) .default
  let (t', pf) ← translateFull {} {} db t
  logInfo m!"[regression, Eq] ⟦fun (x:Nat) => succ x⟧ term  = {t'}"
  logInfo m!"                                          proof : {← inferType pf}"

-- (c) Change of representation. Register `Nat ↦ (Int, NatIntR)` in the
-- type database and `Nat.succ ↦ (fun i => i + 1, succR)` in the constant database.
-- Translating `fun (x : Nat) => Nat.succ x` produces a term of type `Int → Int`
-- and a proof relating `succ x` to `x' + 1` across the *non-`Eq*` binder relation
-- `NatIntR x x'` — the binder changed representation `Nat ↦ Int`.
run_meta do
  let int  := Expr.const ``Int []
  let relC := Expr.const ``NatIntR []
  let tdb : NameMap (Expr × Expr) := (∅ : NameMap _).insert ``Nat (int, relC)
  let gPrime ← Lean.Elab.Term.TermElabM.run'
    (Lean.Elab.Term.elabTerm (← `(fun (i : Int) => i + 1)) (some (← mkArrow int int)))
  let db : NameMap (Expr × Expr) :=
    (∅ : NameMap _).insert ``Nat.succ (gPrime, .const ``succR [])
  let nat := Expr.const ``Nat []
  let t := Expr.lam `x nat (.app (.const ``Nat.succ []) (.bvar 0)) .default
  let (t', pf) ← translateFull tdb {} db t
  logInfo m!"[change-of-rep, Nat ↦ Int] ⟦fun (x:Nat) => succ x⟧ term  = {t'}"
  logInfo m!"                                                      term  : {← inferType t'}"
  logInfo m!"                                                      proof : {← inferType pf}"

end Transfer.Param
