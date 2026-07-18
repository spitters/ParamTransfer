/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Congruence.ParamSolve
import Transfer.Base.Related
import Mathlib.Tactic

/-!
# `param_auto` — one coordinator over every congruence surface

Every native Lean relational tactic is congruence for one fixed relation, and the
engine tactics generalize that rule to a registered relation (see
`Congruence/RCongr.lean`, `Examples/StrongExamples.lean`). `param_auto` is the
single entry point that *dispatches* to all of them: the engine tactics
(`param_solve` = descent + closure, itself calling `grind` on the `Eq` leaves;
`rcongr` for cross-head descent) and the native relational tactics (`norm_cast`
for the cast graph, `gcongr` for ordered congruence, `grind` for `Eq` closure).

The point is a **stable call site**: a proof writes `param_auto`, and the *dispatch
strategy* underneath — the order of alternatives, goal-shape-directed routing,
per-relation specialization — can be optimized later without changing any call
site. It is currently a `first`-cascade; that is the coordinator in its simplest
form. A goal-directed router (inspect the relation head, jump straight to its
optimal solver) is a drop-in replacement behind the same name.

This realizes, as a tactic, the "one engine" picture: the coordinator descends the
one graded congruence rule and hands each leaf to the fastest available
decision procedure for that leaf's relation.
-/

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField

/-- The coordinator: try each surface in turn. `first` moves past any alternative
    that does not apply to the current goal, so one name closes goals from many
    different relations. Optimize the dispatch (order / goal-directed routing)
    behind this name without touching call sites. -/
macro "param_auto" : tactic => `(tactic|
  first
    | rfl
    | param_solve
    | rcongr
    | norm_cast
    | gcongr
    | grind
    | assumption)

/-! ## One tactic, four relations

Each goal below is congruence for a *different* fixed relation; `param_auto`
routes each to a surface that closes it. -/

/-- `Eq` — closed by `rfl`/`grind`. -/
example (a : Nat) : a + 0 = a := by param_auto

/-- `≤` — routed to `gcongr` (ordered congruence). -/
example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by param_auto

/-- The cast graph — routed to `norm_cast`. -/
example (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + b := by param_auto

/-- A registered representation change — routed to `rcongr` (cross-head descent
    over the `RelatedBinOp` squares), which `gcongr` structurally cannot do. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_auto

end Transfer
