/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Lean
import Transfer.Translate.ParamTranslate

/-!
# The persistent `@[param]` constant database

The term-level translator `ParamTranslate.translate` consumes a `db : NameMap
(Expr × Expr)` mapping an abstract constant `c` to its transferred counterpart
`c'` together with a witness `wᶜ : RArrow PA PB c c'`. Without an ambient store
that database must be assembled and passed by hand at each call site.

This module makes the database persistent and ambient:

* a persistent environment extension (`paramExt`) whose state is a
  `NameMap (Name × Name)` — abstract const name ↦ `(transferred const, witness
  lemma)`. Built with `Lean.registerSimplePersistentEnvExtension`; the
  `addImportedFn` re-folds entries from imported modules, so registrations
  survive across files.
* an attribute `@[param]` that, given a lemma `cR : RArrow PA PB c c'`,
  peels the `RArrow` application from the lemma's *type* (the last two of its
  eight application arguments are the abstract const `c` and the transferred
  const `c'`) and stores `c.constName ↦ (c'.constName, lemmaName)`.
* `getParamDB : MetaM (NameMap (Expr × Expr))` — materialises the extension
  state into the `NameMap (Expr × Expr)` that `translate` consumes, turning each
  `(c', lemmaName)` into `(Expr.const c' [], Expr.const lemmaName [])`.
* a driver command `#param_translate t` that runs
  `translate {} (← getParamDB) t` against the *ambient* registry and logs the
  transferred term and the proof's type.

A witness is registered once with `@[param]`, and the translator resolves the
constant from the registry with no explicit `db` argument.
-/

set_option autoImplicit false

open Lean Meta Elab

namespace Transfer.Param

/-! ## The persistent `@[param]` database -/

/-- The persistent environment extension backing `@[param]`. Its state maps an
    abstract constant's name to `(transferred const name, witness lemma name)`.
    `addEntryFn` inserts a single registration; `addImportedFn` re-folds all
    entries contributed by imported modules so the database is cross-file. -/
initialize paramExt :
    SimplePersistentEnvExtension (Name × Name × Name) (NameMap (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (k, c', l) => m.insert k (c', l)
    addImportedFn := fun arrs =>
      arrs.foldl (fun m arr => arr.foldl (fun m (k, c', l) => m.insert k (c', l)) m) {}
  }

/-- Peel `RArrow PA PB c c'` from a lemma's type. `RArrow` has four implicit type
    arguments `{A A' B B'}`, two relation arguments `PA PB`, and the two function
    arguments `f f'` — eight application arguments in total. The abstract constant
    `c` and its transferred counterpart `c'` are the last two; their
    head-constant names are returned. -/
def peelRArrow (ty : Expr) : MetaM (Name × Name) := do
  -- NB: do not `whnf` — `RArrow` is a `def`, so reduction would unfold the head
  -- away from the `RArrow` constant being matched.
  let ty ← instantiateMVars ty
  let args := ty.getAppArgs
  unless ty.getAppFn.isConstOf ``RArrow do
    throwError "@[param]: lemma type is not an `RArrow PA PB c c'`, got{indentExpr ty}"
  unless args.size = 8 do
    throwError "@[param]: expected 8 `RArrow` application arguments, got {args.size}"
  let some cN := args[6]!.getAppFn.constName?
    | throwError "@[param]: abstract const is not a constant:{indentExpr args[6]!}"
  let some c'N := args[7]!.getAppFn.constName?
    | throwError "@[param]: transferred const is not a constant:{indentExpr args[7]!}"
  return (cN, c'N)

initialize registerBuiltinAttribute {
  name := `param
  descr := "register a `RArrow PA PB c c'` witness lemma in the Trocq parametricity database"
  add := fun decl _stx _kind => do
    let info ← getConstInfo decl
    let (cN, c'N) ← MetaM.run' (peelRArrow info.type)
    modifyEnv fun env => paramExt.addEntry env (cN, c'N, decl)
}

/-- Materialise the persistent `@[param]` registry into the `NameMap (Expr × Expr)`
    that `ParamTranslate.translate` consumes: each stored `(c', lemmaName)` becomes
    `(Expr.const c' [], Expr.const lemmaName [])`. -/
def getParamDB : MetaM (NameMap (Expr × Expr)) := do
  return (paramExt.getState (← getEnv)).foldl
    (fun acc k (c', l) => acc.insert k (.const c' [], .const l [])) {}

/-! ## Driver command -/

open Lean.Elab.Command in
/-- `#param_translate t` runs the term-level parametricity translation `⟦t⟧`
    against the **ambient** `@[param]` registry (no explicit database), logging
    the transferred term and the type of the relatedness proof. -/
elab "#param_translate " t:term : command =>
  liftTermElabM do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let db ← getParamDB
    let (t', pf) ← translate {} db e
    logInfo m!"⟦{e}⟧  term  = {t'}"
    logInfo m!"      proof : {← inferType pf}"

-- NOTE: the persistent extension cannot be *used* in its defining module
-- (`initialize` runs at import). Registrations via `@[param]` and uses of
-- `#param_translate`/`getParamDB` therefore live in downstream modules (see
-- `ParamTranslateFull`).

end Transfer.Param
