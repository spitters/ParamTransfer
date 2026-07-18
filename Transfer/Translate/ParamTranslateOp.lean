/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Lean
import Transfer.Translate.ParamTranslate

/-!
# The operator/arity rule for the term-level translator

`ParamTranslate.lean`'s `translate` covers the first-order, same-domain
fragment (`var`/`const`/`app`/`lam`) where every head is a clean `.const`. But
the type-class operators that crypto terms are written with — `a * b`,
`a + b` — do not elaborate to a `.const` head: `a * b` is
`@HMul.hMul α α α inst a b`, an application spine whose head const is
``HMul.hMul`` *followed by three type arguments and one instance argument*
before the two value arguments. Feeding such a spine to the bare `app`/`const`
rules fails (the type/instance args are unregistered constants).

This module adds the operator/arity rule. It maps an operator head
const name to its *arity profile* and a transferred binary op + relatedness
witness, then has the `app` rule recognise an operator spine and strip the
leading type+instance arguments before recursing on the two value arguments.

## The rule

For a binary operator `op` the relatedness witness is **curried** through the
function relation `RArrow` (from `ParamTranslate`):

```
opR : RArrow PA (RArrow PA PC) op bop
```

so that, given related arguments `a a' aR` and `b b' bR`,

```
opR a a' aR        : RArrow PA PC (op a) (bop a')
opR a a' aR b b' bR : PC (op a b) (bop a' b')
```

is exactly the relatedness proof for the value `op a b`. The transferred term
is `bop a' b'`. This is the same combinator the `app` rule uses, applied twice;
the only new work is *spine stripping* — discarding the `numLeadingArgs`
type+instance arguments so the parametricity recursion sees only `a` and `b`.

## Operator database

`OpDB := NameMap (Nat × Expr × Expr)` maps a head const name to
`(numLeadingArgs, bop, witness)`:

* `numLeadingArgs` — the count of type+instance arguments that precede the two
  value arguments. For `@HMul.hMul α α α inst a b` this is `4` (three type
  arguments `α α α` plus one instance `inst`); the spine then has
  `numLeadingArgs + 2 = 6` arguments total.
* `bop : Expr` — the transferred binary operator.
* `witness : Expr` — `RArrow PA (RArrow PA PC) ⟨abstract binary fn⟩ bop`.

## n-ary operators

An `n`-ary operator generalises by the *same* spine-stripping: register
`numLeadingArgs` for the type+instance prefix and an `n`-fold-curried `RArrow`
witness, then strip the prefix and recurse on the `n` value arguments. The
binary case below is the worked instance. Combined with the const/var/app/lam
rules inherited from `ParamTranslate`, this covers the operator-bearing
first-order fragment.
-/

set_option autoImplicit false

open Lean Meta

namespace Transfer.Param

/-- The operator database: maps an operator **head** const name (e.g.
    ``HMul.hMul``, ``HAdd.hAdd``) to `(numLeadingArgs, bop, witness)` where
    `numLeadingArgs` is the number of type+instance arguments preceding the two
    value arguments, `bop` is the transferred binary operator, and `witness`
    proves `RArrow PA (RArrow PA PC) ⟨abstract binary fn⟩ bop`. -/
abbrev OpDB := NameMap (Nat × Expr × Expr)

/-- The term-level parametricity translation extended with the **operator/arity
    rule**. Identical to `translate` (the `var`/`const`/`app`/`lam` rules) except
    that the `app` rule first checks whether the term is an *operator spine*:
    if `e.getAppFnArgs = (opName, args)` with `opName ∈ opdb` and
    `args.size = numLeadingArgs + 2`, the leading type+instance arguments are
    stripped, the two value arguments `a := args[numLeadingArgs]`,
    `b := args[numLeadingArgs+1]` are translated, and the result is
    `(bop a' b', witness a a' aR b b' bR)`. Otherwise it falls back to the normal
    rules. All recursive calls go back through `translateOp`. -/
partial def translateOp (opdb : OpDB)
    (ctx : Std.HashMap FVarId (Expr × Expr)) (db : NameMap (Expr × Expr)) :
    Expr → MetaM (Expr × Expr)
  | .fvar fid => match ctx[fid]? with
      | some p => return p
      | none   => throwError "translateOp: unbound variable"
  | .const n _ => match db.find? n with
      | some p => return p
      | none   => throwError "translateOp: unregistered constant `{n}`"
  | e@(.app f a) => do
      -- operator/arity rule: recognise an operator spine and strip its prefix
      let (opName, args) := e.getAppFnArgs
      match opdb.find? opName with
      | some (numLeading, bop, witness) =>
          if args.size == numLeading + 2 then
            -- the two value arguments live just past the type+instance prefix
            let av := args[numLeading]!
            let bv := args[numLeading + 1]!
            let (a', aR) ← translateOp opdb ctx db av
            let (b', bR) ← translateOp opdb ctx db bv
            -- bop a' b'  with curried witness  witness a a' aR b b' bR
            return (mkApp2 bop a' b', ← mkAppM' witness #[av, a', aR, bv, b', bR])
          else
            -- not the operator's value arity: fall back to the plain `app` rule
            let (f', fR) ← translateOp opdb ctx db f
            let (a', aR) ← translateOp opdb ctx db a
            return (.app f' a', ← mkAppM' fR #[a, a', aR])
      | none =>
          -- ordinary application: the parametricity application rule
          let (f', fR) ← translateOp opdb ctx db f
          let (a', aR) ← translateOp opdb ctx db a
          return (.app f' a', ← mkAppM' fR #[a, a', aR])
  | .lam nm ty b bi =>
      -- same-domain (Eq) binder rule, recursing through `translateOp`
      withLocalDecl nm bi ty fun x =>
      withLocalDecl (nm.appendAfter "'") bi ty fun x' => do
        let eqTy ← mkAppM ``Eq #[x, x']
        withLocalDeclD (nm.appendAfter "R") eqTy fun xr => do
          let ctx' := ctx.insert x.fvarId! (x', xr)
          let (b', bR) ← translateOp opdb ctx' db (b.instantiate1 x)
          let term  ← mkLambdaFVars #[x'] b'
          let proof ← mkLambdaFVars #[x, x', xr] bR
          return (term, proof)
  | e => throwError "translateOp: unsupported term {e}"

/-! ## Demonstration — operator translation

The demo registers the `*` operator over `ℕ` (head const ``HMul.hMul``, with
`numLeadingArgs = 4`: three type arguments `ℕ ℕ ℕ` plus one `HMul ℕ ℕ ℕ`
instance, confirmed by inspecting the elaborated spine of `fun x : Nat => x * x`)
to the abstract/transferred binary op `Nat.mul` (same on both sides) with the
diagonal relatedness witness

```
mulR : RArrow (@Eq ℕ) (RArrow (@Eq ℕ) (@Eq ℕ)) Nat.mul Nat.mul
```

Then `⟦fun x => x * x⟧` produces the transferred function `fun x' => x'.mul x'`
together with the relatedness proof `∀ x x', x = x' → x.mul x = x'.mul x'`. The
`inferType` makes the kernel type-check the proof term, so this is a checked
validation. -/

run_meta do
  -- witness: RArrow Eq (RArrow Eq Eq) Nat.mul Nat.mul, by Eq-substitution
  let mulR ← Lean.Elab.Term.TermElabM.run'
    (Lean.Elab.Term.elabTerm
      (← `((fun (a a' : Nat) (ha : a = a') (b b' : Nat) (hb : b = b') =>
              ha ▸ hb ▸ rfl :
            RArrow (@Eq Nat) (RArrow (@Eq Nat) (@Eq Nat)) Nat.mul Nat.mul))) none)
  -- operator database: `*` over ℕ  ↦  (numLeadingArgs = 4, Nat.mul, mulR)
  let opdb : OpDB := (∅ : OpDB).insert ``HMul.hMul (4, Expr.const ``Nat.mul [], mulR)
  -- the term to translate: `fun x : Nat => x * x`
  let t ← Lean.Elab.Term.TermElabM.run'
    (Lean.Elab.Term.elabTerm (← `(fun x : Nat => x * x)) none)
  let (t', pf) ← translateOp opdb {} {} (← instantiateMVars t)
  logInfo m!"⟦fun x => x * x⟧  term  = {t'}"
  logInfo m!"                  proof : {← inferType pf}"

end Transfer.Param
