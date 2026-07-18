/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Congruence.ParamAuto
import Transfer.Congruence.RCongr
import Mathlib.Data.Nat.Cast.Basic

/-!
# `param_compose` — descend-and-dispatch congruence

`param_auto` (`ParamAuto.lean`) is a `first`-cascade: it selects *one* surface to
close the *whole* goal. That cannot handle a goal that needs **two** extensions at
once — descend a representation change with the engine, then close each residual
*leaf* with a *different* (native) tactic. `param_compose` is that composer: it
descends a `Related` op-tree with the cross-head rule `rcongrBinOp`, and closes
each leaf with the full native cascade (`param_leaf`).

The distinctive niche is a **cross-representation congruence over an opaque
registered operation whose leaves need arithmetic** — where neither a native
tactic nor the engine alone suffices:

* `grind`/`norm_cast`/`gcongr` cannot descend the op-tree — the realized operation
  (`bbFieldMul`, an emitted kernel, …) is opaque to them;
* `rcongr` descends but can only close leaves from the `Related` registry — an
  arithmetic leaf (`c + 0`, a cast, a commutation) is not registry-seatable.

`param_compose` descends with `rcongrBinOp` and hands each leaf to `param_leaf`,
so the two capabilities compose. It is the tactic form of the "coordinator"
architecture: descend the one graded congruence rule, route each leaf to its
fastest solver.

## `param_leaf` and the `done`-gate

`param_leaf` is the per-leaf discharger. Each alternative must **fully close** the
goal: the progress-only tactics (`simp`, `gcongr`, `norm_cast`) are gated with
`done`, because `first` otherwise commits to a tactic that merely *made progress*
and pre-empts a later closer. This gate is what makes the cascade robust.

Visible residual: on a leaf no surface closes, `param_compose` leaves it as an
open goal (it does not fail), so a missing witness stays visible — the engine's
standing invariant.
-/

set_option autoImplicit false

namespace Transfer

open Lean Elab Tactic Meta

/-- The per-leaf discharger: a native cascade in which every alternative must
    **close** the goal. The progress-only tactics are `done`-gated so `first`
    cannot commit to partial progress. -/
macro "param_leaf" : tactic => `(tactic|
  first | rfl | assumption | (simp; done) | grind | ring | (gcongr <;> done) | (norm_cast; done))

/-- Preprocessing: reshape a bare equation `enc t = t'` into `Related enc t t'`,
    reading the encoding off the LHS head. Fires **only** when `enc : A → α` is a
    genuine cross-representation encoding (`A ≠ α`) — a same-type application (an
    *operation* like `a + b : F`) is left for the `id`-bridge. Without this a bare
    `enc t = t'` bridges to `Related id (enc t) t'`, hiding the encoding, and the
    descent cannot use the registered `enc`-squares. -/
def reshapeEq : TacticM Unit := do
  let g ← getMainGoal
  match (← instantiateMVars (← g.getType)).eq? with
  | some (α, .app f a, rhs) =>
      if ← isDefEq (← inferType a) α then
        throwError "reshapeEq: same-type application, not a cross-type encoding"
      let m ← mkFreshExprMVar (← mkAppM ``Related #[f, a, rhs])
      g.assign (Expr.proj ``Related 0 m)
      replaceMainGoal [m.mvarId!]
  | _ => throwError "reshapeEq: LHS is not `enc t`"

/-- Descend a `Related` op-tree with `rcongrBinOp`, closing each leaf with
    `param_leaf`. On a `Related` goal: try the cross-head descent (unification finds
    the operation and operands); on failure treat it as a leaf — the registry
    (`inferInstance`) first, else bridge `Related enc a b` to the equation
    `enc a = b` and run the native cascade. On an `Eq` goal: first try the
    encoding-aware `reshapeEq` (a cross-type `enc t = t'` becomes `Related enc t t'`
    so the descent sees the real encoding), else bridge to `Related id` via
    `transferGround`. Leaves nothing that closes as a residual. -/
partial def paramComposeCore : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let relLeaf : TacticM Unit := do
    let closed ← (do evalTactic (← `(tactic| exact inferInstance)); pure true) <|> pure false
    if closed then return
    try
      evalTactic (← `(tactic| refine ⟨?_⟩))
      evalTactic (← `(tactic| param_leaf))
    catch _ => pure ()
  match tgt.getAppFnArgs with
  | (``Related, _) =>
      try
        evalTactic (← `(tactic| refine rcongrBinOp _ _ _ ?_ ?_))
        allGoals paramComposeCore
      catch _ => relLeaf
  | (``Eq, _) =>
      try
        reshapeEq
        paramComposeCore
      catch _ =>
        try
          evalTactic (← `(tactic| refine transferGround (h := ?_)))
          paramComposeCore
        catch _ => try evalTactic (← `(tactic| param_leaf)) catch _ => pure ()
  | _ => try evalTactic (← `(tactic| param_leaf)) catch _ => pure ()

/-- `param_compose` — descend a representation change and close each leaf with the
    native cascade. Closes goals that need *both* the engine's cross-head descent
    *and* a native leaf tactic — which neither `rcongr` nor a native tactic closes
    alone. -/
elab "param_compose" : tactic => paramComposeCore

/-! ## The compositional example neither `rcongr` nor `grind` closes alone

`bbFieldMul`/`bbFieldAdd` (the `ExampleField` emitted kernels, identity encoding)
are **opaque** to `grind`; the leaf `c + 0` is **not** registry-seatable, so
`rcongr` cannot close it. `param_compose` descends the op-tree and closes the
`c + 0` leaf with `simp`. -/

section
open Transfer.ExampleField

/-- Descend the opaque `bbFieldAdd`/`bbFieldMul` op-tree, close the `c + 0` leaf
    with the native cascade. `rcongr` alone fails at the leaf; `grind` alone fails
    on the opaque operations. -/
example (a b c : F) :
    Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) (c + 0)) := by
  param_compose

/-- The same as an equation (bridged through `transferGround`). -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) (c + 0) := by
  param_compose

end

/-! ## The preprocessing: a bare cross-type equation `enc t = t'`

`Nat.cast : ℕ → ℤ` is a genuine cross-type encoding, so a bare `↑t = t'` is
reshaped to `Related Nat.cast t t'` — the descent then sees the registered cast
squares. Without the reshape it would bridge to `Related id (↑t) t'` and fail.
This is the shape of the ascent's word-value leaves (`wEnc t = t'`). -/

section
local instance : RelatedBinOp (Nat.cast : ℕ → ℤ) (· + ·) (· + ·) := ⟨fun a b => Nat.cast_add a b⟩
local instance : RelatedBinOp (Nat.cast : ℕ → ℤ) (· * ·) (· * ·) := ⟨fun a b => Nat.cast_mul a b⟩

/-- A bare cross-type equation, closed through the reshape preprocessing — `rcongr`
    alone picks `Related id` and fails. -/
example (a b c : ℕ) : ((a * b + c : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) + (c : ℤ) := by
  param_compose

end

end Transfer
