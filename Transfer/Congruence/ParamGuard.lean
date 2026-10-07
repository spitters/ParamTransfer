/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Congruence.ParamSolve
public import Transfer.Base.RelatedOn
public import Transfer.Base.RelatedFamily

/-!
# `param_guard` — descent through guarded squares

`param_guard` closes a goal `Related enc t t'`, an equation `enc t = t'` (or an
equation bridged to `Related id`), or an equivalence `r a b ↔ br a' b'` by
descending through the registered squares, total and guarded
(`Transfer.Base.RelatedOn`). At each node it applies `rcongrBinOpOn`,
`rcongrUnOpOn` or `rcongrRelOn`; the total squares take part through the
instances `RelatedBinOp.toOn` and `RelatedUnOp.toOn` with guard `True`. A read of
an element-wise related container (`Transfer.Base.RelatedFamily`) is closed by the
leaf rules of `transfer_guard_leaf`, whose guard identifies the position read.

The guard of each node is a proposition about the abstract operands of that node,
for example `b ≤ a` at `a - b` or `(a - b) < 2 ^ 64 ∧ s < 64` at `(a - b) >>> s`.
The discharger runs on it: `transfer_guard_disch` by default, or the tactic given
as `param_guard (disch := tac)`. A guard the discharger does not close is left as a
goal, so `param_guard` returns exactly the side conditions it could not prove.

When a `Related` subgoal has no registered square and no leaf closes it,
`param_guard` fails with an error that names that subgoal, its abstract and
encoded heads, and the encoding. The error is raised at the leaf, not at the root
of the op-tree.

`param_solve` runs the same guarded descent with the default discharger and fails
over to its closure leaf when a guard is not closed.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

open Lean Elab Tactic Meta

/-- The error for a `Related` goal that no registered square and no leaf closes:
    it names the goal, the heads of its abstract and encoded sides, and the
    encoding. -/
meta def paramGuardLeafError (g : MVarId) : MetaM MessageData := do
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``Related, #[_, _, enc, lhs, rhs]) =>
      pure m!"param_guard: no registered square or leaf closes{indentExpr t}\n\
        abstract head: {lhs.getAppFn}, encoded head: {rhs.getAppFn}, encoding: {enc}"
  | _ => pure m!"param_guard: no rule closes{indentExpr t}"

/-- Run `tac` on `g`; return `true` and keep the result when it closes `g`, else
    restore the state and return `false`. -/
meta def paramGuardCloses (tac : Syntax) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    if (← Term.withoutErrToSorry (evalTacticAt tac g)).isEmpty then return true
    s.restore; return false
  catch _ =>
    s.restore; return false

/-- Apply the rule `rule` to `g`; return its new goals, or `none` (state restored)
    when the rule does not apply. -/
meta def paramGuardApply (rule : Syntax) (g : MVarId) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  try
    return some (← Term.withoutErrToSorry (evalTacticAt rule g))
  catch _ =>
    s.restore; return none

/-- Reshape an equation `enc t = t'` whose sides have a type other than that of
    `t` into the goal `Related enc t t'`, and return that goal. Metadata around
    the left-hand side is removed first. -/
meta def paramGuardReshape (g : MVarId) : MetaM MVarId := do
  let some (α, lhs, rhs) := (← instantiateMVars (← g.getType)).cleanupAnnotations.eq?
    | throwError "param_guard: not an equation"
  let lhs := lhs.cleanupAnnotations
  unless lhs.isApp do throwError "param_guard: the left-hand side is not `enc t`"
  let f := lhs.appFn!
  let a := lhs.appArg!
  if ← isDefEq (← inferType a) α then
    throwError "param_guard: same-type application, not an encoding"
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Related #[f, a, rhs])
  g.assign (Expr.proj ``Related 0 m)
  return m.mvarId!

/-- The `param_guard` recursion on one goal. Returns the goals left open: the
    guards the discharger `disch` did not close. Throws the leaf error of
    `paramGuardLeafError` on a `Related` subgoal that no rule closes. -/
meta partial def paramGuardCore (disch : Syntax) (g : MVarId) : TacticM (List MVarId) :=
  g.withContext do
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
  -- A node rule leaves the operand goals, then the guard as the last goal.
  let node (gs : List MVarId) : TacticM (List MVarId) := do
    let some guard := gs.getLast? | throwError "param_guard: rule left no guard goal"
    let mut rest : List MVarId := []
    for sub in gs.dropLast do
      rest := rest ++ (← paramGuardCore disch sub)
    guard.setType ((← instantiateMVars (← guard.getType)).headBeta)
    if ← paramGuardCloses disch guard then return rest
    return rest ++ [guard]
  match tgt.getAppFnArgs with
  | (``Related, _) =>
      if ← paramGuardCloses (← `(tactic| exact inferInstance)) g then return []
      if let some gs ← paramGuardApply (← `(tactic| refine rcongrBinOpOn _ _ _ ?_ ?_ ?_)) g then
        return ← node gs
      if let some gs ← paramGuardApply (← `(tactic| refine rcongrUnOpOn _ _ _ ?_ ?_)) g then
        return ← node gs
      if let some gs ← paramGuardApply (← `(tactic| transfer_guard_leaf)) g then
        return ← node gs
      let s ← saveState
      try
        setGoals [g]
        paramCCCore
        if (← getUnsolvedGoals).isEmpty then return []
        s.restore
      catch _ => s.restore
      throwError (← paramGuardLeafError g)
  | (``Iff, _) =>
      if let some gs ← paramGuardApply (← `(tactic| refine rcongrRelOn _ _ _ ?_ ?_ ?_)) g then
        return ← node gs
      if ← paramGuardCloses (← `(tactic| exact Iff.rfl)) g then return []
      throwError (← paramGuardLeafError g)
  | (``Eq, _) =>
      let s ← saveState
      let reshaped ← try
          pure (some (← paramGuardReshape g))
        catch _ => s.restore; pure none
      if let some g' := reshaped then
        return ← paramGuardCore disch g'
      if let some [g'] ← paramGuardApply (← `(tactic| refine transferGround (h := ?_))) g then
        return ← paramGuardCore disch g'
      if ← paramGuardCloses (← `(tactic| rfl)) g then return []
      throwError (← paramGuardLeafError g)
  | _ => throwError (← paramGuardLeafError g)

/-- Run `paramGuardCore` on the main goal and replace it by the open guards. -/
meta def paramGuardMain (disch : Syntax) : TacticM Unit := do
  let g ← getMainGoal
  let rest ← paramGuardCore disch g
  replaceMainGoal rest

/-- `param_guard` descends through the registered total and guarded squares
    (`RelatedBinOpOn`, `RelatedUnOpOn`, `RelatedRelOn`), discharges each guard by
    `transfer_guard_disch`, and leaves the guards it does not close as goals. -/
elab "param_guard" : tactic => do
  paramGuardMain (← `(tactic| transfer_guard_disch))

/-- `param_guard (disch := tac)` is `param_guard` with the guard discharger `tac`. -/
elab "param_guard" " (" &"disch" " := " d:tacticSeq ")" : tactic => do
  paramGuardMain d

end Transfer
