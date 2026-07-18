/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Translate.ParamDB
import Transfer.Translate.ParamTranslateTy
import Transfer.Translate.ParamTranslateOp

/-!
# The integrated term-level translator `⟦·⟧` (capstone)

Combines the three extensions into one parametricity translation:

* `var` — relatedness hypothesis from the local context;
* `const` — resolved from the ambient `@[param]` registry (`ParamDB`), no
  explicit database;
* operator spine (`a * b` = `@HMul.hMul … a b`) — the operator/arity rule
  (`ParamTranslateOp`): strip the leading type/instance args, apply the registered
  binary witness to the translated value args;
* app — the parametricity application `fR a a' aR`;
* `lam` — the type-translation rule (`ParamTranslateTy`): the binder may
  change representation (`x : A ↦ x' : A'`) at the relation `PA` from `translateTy`,
  with hypothesis `xr : PA x x'`.

`translateAll` is the single function with all rules; `#transfer t` runs it against
the ambient registry. This is the term-level `⟦·⟧` for the first-order fragment
(`const`/`var`/`app`/`lam`/operators, registry-driven, with change-of-representation
binders). The remaining case — dependent `Π`/recursors and the `Type`-valued
motive — is the univalence cap, which `UnivalenceStatus.univalence_inconsistent`
proves is unreachable in Lean by necessity.
-/

set_option autoImplicit false

open Lean Meta Elab

namespace Transfer.Param

/-- The integrated translation: operator-spine, registry `const`, `app`, the
    type-translating `lam`, and `var`. `opdb` is the operator database, `tdb` the
    type-relation database, `db` the (registry-materialised) constant database. -/
partial def translateAll (opdb : OpDB) (tdb : NameMap (Expr × Expr))
    (ctx : Std.HashMap FVarId (Expr × Expr)) (db : NameMap (Expr × Expr)) :
    Expr → MetaM (Expr × Expr) := fun e => do
  match e with
  | .fvar fid =>
      match ctx[fid]? with
      | some p => return p
      | none   => throwError "translateAll: unbound variable"
  | .lam nm ty b bi =>
      let (ty', PA) ← translateTy tdb ty
      withLocalDecl nm bi ty fun x =>
      withLocalDecl (nm.appendAfter "'") bi ty' fun x' => do
        let hyp ← mkAppM' PA #[x, x']
        withLocalDeclD (nm.appendAfter "R") hyp fun xr => do
          let (b', bR) ← translateAll opdb tdb (ctx.insert x.fvarId! (x', xr)) db (b.instantiate1 x)
          return (← mkLambdaFVars #[x'] b', ← mkLambdaFVars #[x, x', xr] bR)
  | _ =>
    if e.isApp then
      let (fn, args) := e.getAppFnArgs
      match opdb.find? fn with
      | some (lead, bop, w) =>
          if args.size == lead + 2 then
            -- operator/arity rule
            let a := args[lead]!; let b := args[lead + 1]!
            let (a', aR) ← translateAll opdb tdb ctx db a
            let (b', bR) ← translateAll opdb tdb ctx db b
            return (mkApp2 bop a' b', ← mkAppM' w #[a, a', aR, b, b', bR])
          else
            let f := e.appFn!; let a := e.appArg!
            let (f', fR) ← translateAll opdb tdb ctx db f
            let (a', aR) ← translateAll opdb tdb ctx db a
            return (.app f' a', ← mkAppM' fR #[a, a', aR])
      | none =>
          -- ordinary parametricity application
          let f := e.appFn!; let a := e.appArg!
          let (f', fR) ← translateAll opdb tdb ctx db f
          let (a', aR) ← translateAll opdb tdb ctx db a
          return (.app f' a', ← mkAppM' fR #[a, a', aR])
    else match e with
      | .const n _ =>
          match db.find? n with
          | some p => return p
          | none   => throwError "translateAll: unregistered constant `{n}`"
      | _ => throwError "translateAll: unsupported term {e}"

/-! ## Registered witnesses (downstream of `ParamDB`, so `@[param]` works here) -/

/-- `Nat.succ` related to itself (diagonal), registered in the `@[param]` database. -/
@[param] theorem succWitFull : RArrow Eq Eq Nat.succ Nat.succ :=
  fun _ _ h => congrArg Nat.succ h

/-- `Nat.mul` related to itself, curried through the function relation (for the
    operator rule on `*`). -/
theorem mulWitFull : RArrow Eq (RArrow Eq Eq) Nat.mul Nat.mul :=
  fun _ _ ha _ _ hb => ha ▸ hb ▸ rfl

/-- The demo operator database: `HMul.hMul` (4 leading type/instance args) ↦
    `Nat.mul` with witness `mulWitFull`. -/
def demoOpDB : OpDB :=
  (∅ : NameMap _).insert ``HMul.hMul (4, .const ``Nat.mul [], .const ``mulWitFull [])

/-- `#transfer t` — the integrated translation against the ambient `@[param]`
    registry (constants) + the demo operator database, logging the transferred
    term and the relatedness proof's type. -/
elab "#transfer " t:term : command =>
  Lean.Elab.Command.liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let db ← getParamDB
    let (t', pf) ← translateAll demoOpDB {} {} db e
    logInfo m!"⟦{e}⟧ = {t'}  ⊢  {← inferType pf}"

/-! ## Demonstrations — all rules together, registry-driven

The constant `Nat.succ` is resolved from the registry, `*` via the operator rule,
under a `lam`; no explicit database at any call site. -/

-- const (registry) under a binder — the output is asserted with `#guard_msgs`,
-- so these demos are *checked* (the synthesized term + proof type are pinned).
/-- info: ⟦fun x ↦ x.succ⟧ = fun x' ↦ x'.succ  ⊢  ∀ (x x' : Nat), x = x' → x.succ = x'.succ -/
#guard_msgs in
#transfer (fun x : Nat => Nat.succ x)

-- operator rule under a binder
/-- info: ⟦fun x ↦ x * x⟧ = fun x' ↦ x'.mul x'  ⊢  ∀ (x x' : Nat), x = x' → x.mul x = x'.mul x' -/
#guard_msgs in
#transfer (fun x : Nat => x * x)

-- Integrated: operator `*` + registry const `Nat.succ` + binder, in one term
/-- info: ⟦fun x ↦ x.succ * x⟧ = fun x' ↦ x'.succ.mul x'  ⊢  ∀ (x x' : Nat), x = x' → x.succ.mul x = x'.succ.mul x' -/
#guard_msgs in
#transfer (fun x : Nat => Nat.succ x * x)

end Transfer.Param
