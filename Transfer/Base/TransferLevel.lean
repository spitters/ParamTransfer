/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.TransferTactic
import Transfer.Base.LevelRefusal

/-!
# The level-aware `transfer!` elaborator

A `MetaM` `elab` tactic
(not a backtracking macro) that infers a relation level from the goal
`Expr`, runs it through the univalence-free guard `LevelRefusal.classify`, and
then either refuses with the report (when the goal forces the `equiv` top) or
proceeds — logging the level used and delegating to the proven `transfer` macro.

This connects the three pieces — `Levels`/`RelatedAt` (the `(m,n)` levels),
`TransferTactic` (the binder tactic), and `LevelRefusal` (the refusal guard) —
into one pipeline: a goal `Expr` ↦ inferred level ↦ refuse-or-transfer, with the
level reported.

## The Expr-level inferencer (a conservative version)

`inferGoalLevel` walks the goal term:
* `∀`/`→` binders are traversed (forward transfer adds no strength);
* an `Eq` whose carrier is a `Sort` — an equation between types — needs an
  equivalence-as-equality and is inferred `equiv` (the refused univalence case);
* any other `Eq` or an `Iff` is a leaf transferred via an injective encoding:
  level `embedding`;
* everything else defaults to `map` (the weakest level).

This is an `Expr`-level version of the `GoalShape`-model `inferLevel` (which
walked a hand-rolled `GoalShape`): the level is computed from the goal. It is
conservative on leaf carriers — the per-subterm minimal-level solver (looking up
each leaf's registered `RelatedAt` level and threading the `meet` through
binders) is the larger engine; this version captures the one structural
rule that matters for the refusal discipline (type-equality ⇒ `equiv`).
-/

set_option autoImplicit false

open Lean Elab Tactic Meta Command

namespace Transfer

open Transfer.LevelRefusal

/-- Infer the minimal `RelLevel` the goal `Expr` needs. See the module docstring
    for the rules. Conservative on leaves (`embedding`); the only `equiv`-forcing
    rule is an equation between `Sort`s (a type equality, needing univalence). -/
partial def inferGoalLevel (e : Expr) : MetaM RelLevel := do
  let e ← instantiateMVars e
  match e with
  | .forallE _ _ body _ => inferGoalLevel body
  | _ =>
    match e.getAppFnArgs with
    | (``Eq, #[α, _, _]) =>
        -- An equation between types (carrier is a `Sort`) needs an
        -- equivalence-as-equality ⇒ `equiv` (the refused univalence case).
        let α ← whnf (← instantiateMVars α)
        return (if α.isSort then .equiv else .embedding)
    | (``Iff, #[_, _]) => return .embedding
    | _                => return .map

/-- `transfer!` — the level-aware transfer. Infers the goal's level from its
    `Expr`, classifies it, and either refuses (with the univalence-free report) or
    logs the level and runs the proven `transfer`. -/
elab "transfer!" : tactic => do
  let tgt ← getMainTarget
  let lvl ← inferGoalLevel tgt
  match classify lvl with
  | .refused r => throwError "transfer! refused — level inference: {r}"
  | .ok l =>
      logInfo m!"transfer! proceeding at level {repr l}"
      evalTactic (← `(tactic| transfer))

/-- A command that reports the inferred level + permission of a goal type, for
    inspection/testing without running a proof. -/
elab "#transfer_level " t:term : command =>
  Command.runTermElabM fun _ => do
    let e ← Term.elabType t
    let lvl ← inferGoalLevel e
    logInfo m!"inferred level {repr lvl}; permitted {permitted lvl}"

/-! ## Demonstrations

The success cases are self-checking: `by transfer!` builds only if the level
inferred is permitted and `transfer` closes the goal. -/

open Transfer.ExampleField

/-- Ground composite: inferred `embedding`, permitted, closed by `transfer`. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by transfer!

/-- Under a binder: the `∀` is traversed, leaf inferred `embedding`, closed. -/
example (b c : F) : ∀ a : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by transfer!

-- The inferencer reports levels for inspection: a first-order ∀-equation is
-- `embedding` (permitted); a type equality is `equiv` (refused).
#transfer_level (∀ a b : Nat, a + b = b + a)
#transfer_level ((ULift.{0} Bool) = Bool)

end Transfer
