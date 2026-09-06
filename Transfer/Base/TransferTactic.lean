/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public meta import Transfer.Base.HigherOrderTransfer
public import Transfer.Base.HigherOrderTransfer
public meta import Transfer.Base.RelatedAt
public import Transfer.Base.RelatedAt

/-!
# The `transfer` tactic (automatic binder translation)

The generic transfer lemmas provide the binder / higher-order / ∀ transfer capability as proven
lemmas (`funMap_transfer`, `foldl_transfer`, `forall_transfer`); `ForallFoldTactic`
wraps them as thin `refine`-macros whose own docstring flags the gap: they are
"not the full `MetaM` `⟦·⟧` elaborator that would find the registered
square automatically" — the user still names the commuting square / pointwise
transfer at the call site.

This module closes that gap for the tractable fragment: a recursive `transfer`
tactic that traverses binders automatically (the `∀`/`λ`/`Iff`-of-`∀` rules)
and dispatches each leaf to the registry — the `Related`/`RelatedBinOp`
typeclass instances (the `@[transfer]` set / the `RelatedAt` kernel) —
with no square named by the caller.

## What `transfer` does (the `⟦·⟧` rules, as a backtracking tactic)

At each goal it tries, in order:
* leaf closers — `rfl`, `Iff.rfl`, `assumption`, and the registry closer
  `exact Related.rel inferInstance` (synthesizes a `Related id lhs rhs` and
  extracts its equation — this is the ground composite, found by
  instance resolution);
* the `∀`-prop rule — on `(∀ x, P x) ↔ (∀ x, Q x)`, `apply forall_congr'`,
  reducing to the pointwise `∀ x, P x ↔ Q x` (then the Pi rule);
* the Pi/`λ` rule — on `∀ x, body` introduce `x` and recurse; on a function
  equality `f = g`, `funext x` and recurse;
* the registry sweep — `simp only [transfer]` (the realization set,
  which itself rewrites under binders), then a bounded `solve_by_elim` over the
  generic transfer lemmas plus the local context (so a square bundled in a local
  realization structure `R` is found via `R`'s projections).

Termination: every structural rule strips one binder; the leaf closers make no
goal; `solve_by_elim` is depth-bounded. So the recursion is well-founded on goal
size.

## Scope (the non-fabrication invariant)

`transfer` never invents a commuting square: the registry closer only succeeds
when instance resolution finds a registered `RelatedBinOp`/`Related` (or the
`@[transfer]` set / a local realization hypothesis) witnessing it. When no
registered witness exists it leaves the leaf as a goal — the residual the
underlying lemmas carry. The search is automatic; the non-fabrication guarantee
is unchanged. This module handles binder translation; the dependent
motive / recursor transfer (`peano_bin_nat`) and the full `(m,n)` level-inference
engine are not implemented here.
-/

public section

meta section

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField
open Lean Elab Tactic Meta

universe u

/-- Ground leaf closer. Discharges `a = b` when the registry synthesizes a
    `Related id a b` (the identity-encoding composite of registered
    `RelatedBinOp`s). The encoding is pinned to `id` so instance resolution sees
    the concrete `a`, `b` of the goal — no higher-order unification on the
    encoding metavariable. -/
theorem transferGround {α : Type u} {a b : α} [h : Related (id : α → α) a b] :
    a = b := h.rel

/-- Leaf discharge. The registry cascade: cheap closers (`rfl`/`Iff.rfl`/
    `assumption`), the identity-encoding registry closer (`transferGround`), the
    `@[transfer]` rewrite set, `solve_by_elim` over the generic transfer lemmas plus
    the local context (so a square bundled in a local realization `R` is found
    once surfaced with a `have`), and finally `grind`. On failure it leaves the
    goal — the non-fabrication residual — rather than erroring. -/
partial def transferLeaf : TacticM Unit := do
  try
    evalTactic (← `(tactic|
      first
        | rfl
        | exact Iff.rfl
        | assumption
        | exact transferGround
        | (simp only [transfer] ; done)
        | solve_by_elim [foldl_transfer, funMap_transfer, forall_transfer]
        | grind))
  catch _ => pure ()

/-- Fast registry leaf. The cheap leaf closer shared by the descent
    tactics `rcongr` (`RCongr.lean`) and `param_solve` (`ParamSolve.lean`): a
    bottomed-out `Related` leaf is discharged by the registry (`inferInstance` —
    the `leaf`/`leafId` instances, plus any class-typed `Related` hypothesis
    treated as a local instance) or `rfl`. Unlike `transferLeaf` it propagates
    failure (no `try`/`catch`), so a caller can chain a heavier discharger
    (`param_solve` delegates to `paramCCCore`) and `rcongr` surfaces the leaf's
    `rfl` error when no registry witness matches. -/
def transferRegistryLeaf : TacticM Unit := do
  evalTactic (← `(tactic| first | exact inferInstance | rfl))

/-- Goal-shape-directed transfer core. Dispatches on the goal's head —
    `∀`-`Iff` (`forall_congr'`), `∀`/`→` (`intro`), function equality (`funext`) —
    recursing structurally, and discharges the leaf otherwise. An `elab`
    (not a backtracking macro): it gates on the goal shape and leaves residual
    side-goals cleanly. -/
partial def transferCore : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  match tgt.getAppFnArgs with
  | (``Iff, #[a, b]) =>
      if a.isForall && b.isForall then
        evalTactic (← `(tactic| apply forall_congr'))
        evalTactic (← `(tactic| intro _))
        transferCore
      else
        transferLeaf
  | (``Eq, #[α, _, _]) =>
      if α.isForall then
        evalTactic (← `(tactic| funext _))
        transferCore
      else
        transferLeaf
  | _ =>
      if tgt.isForall then
        evalTactic (← `(tactic| intro _))
        transferCore
      else
        transferLeaf

/-- The `transfer` tactic — automatic binder traversal + registry leaf
    dispatch, as a goal-shape-directed `elab`. Binder structure is handled
    automatically; only an unregistered commuting square is named
    (surface a locally-bundled one with a `have`). See the module docstring. -/
elab "transfer" : tactic => transferCore

/-! ## Demonstrations — `by transfer`, no square named

These exercise the tactic on the registered Baby Bear field squares
(`bbMulRelated`/`bbAddRelated`, the `RelatedBinOp` instances from `Related.lean`).
The caller names nothing: instance resolution finds the squares. -/

/-- Ground composite (by the tactic). -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by transfer

/-- Under a binder (the Pi rule): the same composite, universally
    quantified — `transfer` introduces `a` and dispatches the leaf to the
    registry automatically. -/
example (b c : F) : ∀ a : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by transfer

/-- Two binders. Both `a` and `b` are introduced; the registry closes the
    leaf. -/
example (c : F) : ∀ a b : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by transfer

/-- Function equality (the λ rule): the byte realization of a pointwise
    product-with-constant, as functions. `transfer` applies `funext` then the
    registry. -/
example (b c : F) :
    (fun a : F => a * b + c) = (fun a : F => bbFieldAdd (bbFieldMul a b) c) := by
  transfer

end Transfer
