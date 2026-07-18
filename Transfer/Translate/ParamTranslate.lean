/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Lean
import Transfer.Combinators.ParamArrow

/-!
# The term-level `⟦·⟧` synthesizer (the parametricity translation)

The type-directed engine synthesizes a `Param` witness for a type and transfers
a goal. This module adds the term-level parametricity translation `⟦·⟧` of
Trocq/paramcoq: a `MetaM` recursion over a *term* `t` producing both its
transferred term `t'` and a proof of relatedness `R t t'`, by the four core
rules:

* **`var x`** — look up the relatedness hypothesis pushed for `x` (the `lam` rule);
* **`const c`** — look up `c`'s registered witness `(c', wᶜ : R_c c c')` in the
  database (unregistered ⇒ error / would be a side-goal);
* **`app f a`** — `⟦f⟧ = (f', fR)`, `⟦a⟧ = (a', aR)`; result
  `(f' a', fR a a' aR)` — the parametricity application rule: `fR`, a proof of
  the *function relation* `∀ a a', PA a a' → PB (f a) (f' a')`, applied at the
  related arguments `a, a', aR`, yields `PB (f a) (f' a')`;
* **`lam x, b`** — introduce `x`, a transferred `x'`, and a relatedness hypothesis
  `xr : PA x x'`; recurse on `b`; abstract to `(fun x' => b', fun x x' xr => bR)`,
  a proof of the function relation. (Here the binder's domain relation is the
  diagonal `Eq` — the same-representation case; change-of-representation binders
  need the type-translation rule, see *Scope* below.)

The `⟦·⟧` produces relatedness *proof terms* (validated: the demos below
construct the proof and the kernel type-checks it). The `app` rule's
`fR a a' aR` and the `lam` rule's abstraction are the parametricity
combinators; the function relation `RArrow` here is `ParamArrow.R_arrow` specialized
to bare `Prop`-relations.

## Scope

The translation is complete for the first-order, same-domain fragment:
`const`/`var`/`app`/`lam` over registered constants, producing checked relatedness
proofs. What it does not cover — the remaining metaprogramming, distinct
from this core:

* a type-translation rule (`sort`/binder-domain) so a binder may change
  representation (`x : A` ↦ `x' : A'` at a non-`Eq` relation) — needs `⟦·⟧` on the
  binder type to produce `(A', PA)`;
* dependent `Π`/elimination and recursors (the `peano_bin_nat` case) —
  the `Type`-valued-motive case, which (per `UnivalenceStatus`) is also where
  univalence would be required and is therefore capped;
* a persistent `@[param]` database (here the database is passed explicitly);
* operator-class arity handling (`HMul.hMul` ↦ a plain `mul`), which needs a
  per-constant arity-aware rule, not a bare const-rename.

For the goals proof transfer exercises (∀-statements, function/value
relations over registered domains), the type-directed engine (`param_transfer`,
`forallTransfer`, `param_resolve`) already closes them; this module is the
term-level companion that exhibits the proof *terms*.
-/

set_option autoImplicit false

open Lean Meta

namespace Transfer.Param

/-- The function relation (Trocq `R_arrow`, bare-`Prop` form): `f`, `f'` send
    `PA`-related arguments to `PB`-related results. -/
def RArrow {A A' B B' : Type} (PA : A → A' → Prop) (PB : B → B' → Prop)
    (f : A → B) (f' : A' → B') : Prop :=
  ∀ a a', PA a a' → PB (f a) (f' a')

/-- The term-level parametricity translation `⟦·⟧`. Given a context mapping bound
    variables to their `(transferred var, relatedness proof)` and a database
    mapping constants to `(transferred const, relatedness witness)`, returns the
    transferred term together with its relatedness proof. See the module docstring
    for the four rules. -/
partial def translate (ctx : Std.HashMap FVarId (Expr × Expr)) (db : NameMap (Expr × Expr)) :
    Expr → MetaM (Expr × Expr)
  | .fvar fid => match ctx[fid]? with
      | some p => return p
      | none   => throwError "translate: unbound variable"
  | .const n _ => match db.find? n with
      | some p => return p
      | none   => throwError "translate: unregistered constant `{n}`"
  | .app f a => do
      let (f', fR) ← translate ctx db f
      let (a', aR) ← translate ctx db a
      -- parametricity application: fR a a' aR : PB (f a) (f' a')
      return (.app f' a', ← mkAppM' fR #[a, a', aR])
  | .lam nm ty b bi =>
      -- same-domain (Eq) binder rule
      withLocalDecl nm bi ty fun x =>
      withLocalDecl (nm.appendAfter "'") bi ty fun x' => do
        let eqTy ← mkAppM ``Eq #[x, x']
        withLocalDeclD (nm.appendAfter "R") eqTy fun xr => do
          let ctx' := ctx.insert x.fvarId! (x', xr)
          let (b', bR) ← translate ctx' db (b.instantiate1 x)
          let term  ← mkLambdaFVars #[x'] b'
          let proof ← mkLambdaFVars #[x, x', xr] bR
          return (term, proof)
  | e => throwError "translate: unsupported term {e}"

/-! ## Demonstrations (the synthesizer in action)

Each `run_meta` block builds the transferred term + relatedness proof and the
kernel type-checks the proof (`inferType` would error on an ill-typed term), so
each is a checked validation. -/

-- `⟦fun x => Nat.succ x⟧` — produces the transferred function and a proof of
-- `∀ x x', x = x' → x.succ = x'.succ` (the `RArrow Eq Eq` relatedness). The output
-- is pinned with `#guard_msgs`, so this is a *checked* example.
run_meta do
  let nat := Expr.const ``Nat []
  let succR ← Lean.Elab.Term.TermElabM.run'
    (Lean.Elab.Term.elabTerm (← `(fun (a a' : Nat) (h : a = a') => congrArg Nat.succ h)) none)
  let db : NameMap (Expr × Expr) := (∅ : NameMap _).insert ``Nat.succ (.const ``Nat.succ [], succR)
  let t := Expr.lam `x nat (.app (.const ``Nat.succ []) (.bvar 0)) .default
  let (t', pf) ← translate {} db t
  logInfo m!"⟦fun x => succ x⟧ = {t'}  ⊢  {← inferType pf}"

-- `⟦fun x => Nat.succ (Nat.succ x)⟧` — nested application; the `app` rule
-- composes, producing `∀ x x', x = x' → x.succ.succ = x'.succ.succ`. Checked.
run_meta do
  let nat := Expr.const ``Nat []
  let succR ← Lean.Elab.Term.TermElabM.run'
    (Lean.Elab.Term.elabTerm (← `(fun (a a' : Nat) (h : a = a') => congrArg Nat.succ h)) none)
  let db : NameMap (Expr × Expr) := (∅ : NameMap _).insert ``Nat.succ (.const ``Nat.succ [], succR)
  let body := Expr.app (.const ``Nat.succ []) (.app (.const ``Nat.succ []) (.bvar 0))
  let t := Expr.lam `x nat body .default
  let (t', pf) ← translate {} db t
  logInfo m!"⟦fun x => succ (succ x)⟧ = {t'}  ⊢  {← inferType pf}"

end Transfer.Param
