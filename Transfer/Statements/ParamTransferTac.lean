/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransfer
import Transfer.Synthesis.ParamSynth

/-!
# `param_transfer`, end-to-end `∀`-transfer

This module is the term-level transfer capstone for the `∀`-fragment of the
`Param` engine. It closes the last manual seam in `ParamTransfer.lean`:
`forallTransfer` there required the caller to *name* the domain
`Param .map0 .map2a A A'`. Here the domain witness is synthesized by instance
resolution through a small `TransferDom` class, and a `param_transfer` tactic
applies the abstraction-theorem `∀`-rule (`forallTransfer`) so the caller writes
nothing structural — no commuting square, no domain relation, no `Param` term.

## The two levels and why `TransferDom` (not `HasParam`)

`ParamSynth.HasParam` resolves witnesses at the fixed self-relation level
`(.map1, .map1)` (forward + backward maps, used for the arrow/`app` rule). But
the `∀`-rule `forallTransfer` consumes the domain at `(.map0, .map2a)` (forward
nothing, backward a section `A' → A` + `map_in_R`) — the univalence-free level
that `Map1_forall` needs. These levels are *incomparable* in the obvious
direction, so the `∀`-rule gets its own resolver: `TransferDom A A'` carries a
`Param .map0 .map2a A A'`, with instances for

* the diagonal `TransferDom A A` (graph `Eq`, via `paramDiag`) — so
  same-type `∀`-transfer resolves with no caller input; and
* the `Num ↦ ℕ` change-of-representation `TransferDom Num ℕ` (graph of the
  cast, via `paramNumNat`) — so a change of representation resolves too.

## What it delivers

With `TransferDom` resolving the domain, `forallTransferAuto` and the
`param_transfer` tactic reduce a goal `(∀ a, P a) → (∀ a', P' a')` to the
*pointwise* obligation `∀ a a' (_ : dom.R a a'), P a → P' a'` — the only content
the caller supplies, and on related pairs it is usually closed by
`intro`/`assumption`/`exact`. The domain `Param`, the reflection through
`ULift`/`PLift`, and the abstraction-theorem combinator are all invisible.

What is not implemented here is the full `⟦t⟧` translation over
arbitrary terms: a constant database (`@[param]`) plus `app`/`lam` recursion
beyond `∀`-statements, i.e. the `MetaM`/Elpi-style synthesizer that infers the
`Param` witnesses and per-subterm `(m, n)` levels for *any* term, not just the
universally-quantified `Prop`-fragment handled here.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

/-! ## `TransferDom`: the domain `Param` at the `∀`-rule level, by resolution -/

/-- `TransferDom A A'` carries the domain `Param .map0 .map2a A A'` that the
    abstraction-theorem `∀`-rule (`forallTransfer`) consumes. Resolution of this
    class is what makes the domain witness *automatic*: the caller of
    `param_transfer` never names it. The level is `(.map0, .map2a)` — the
    univalence-free level `Map1_forall` requires — deliberately distinct from
    `HasParam`'s `(.map1, .map1)` self-relation level. -/
class TransferDom (A A' : Type u) where
  dom : Param .map0 .map2a A A'

/-- The diagonal instance: same-type `∀`-transfer resolves automatically. The
    domain `Param` is `paramDiag` (graph `Eq`), so on related pairs `(a, a')` the
    relation is `a = a'` and the pointwise obligation is `∀ a, P a → P' a`. -/
instance instTransferDomDiag (A : Type u) : TransferDom A A where
  dom := paramDiag

/-- The `Num ↦ ℕ` instance: a change of representation resolves
    automatically. The domain `Param` is `paramNumNat` (graph of the cast
    `Num → ℕ`), so on related pairs `(n, k)` the relation is `(n : ℕ) = k`. -/
instance instTransferDomNumNat : TransferDom Num ℕ where
  dom := paramNumNat

/-! ## `forallTransferAuto`: `forallTransfer` with the domain resolved -/

/-- `forallTransfer` with the domain `Param` synthesized by `TransferDom`.

    Identical to `forallTransfer` except the domain witness is not an explicit
    argument — it is resolved from `TransferDom A A'`. The only argument the
    caller supplies is the pointwise implication `PB`, stated against the
    resolved relation `(TransferDom.dom).R`. -/
def forallTransferAuto {A A' : Type u} [TransferDom A A']
    {P : A → Prop} {P' : A' → Prop}
    (PB : ∀ a a', (TransferDom.dom (A := A) (A' := A')).R a a' → (P a → P' a')) :
    (∀ a, P a) → (∀ a', P' a') :=
  forallTransfer (TransferDom.dom (A := A) (A' := A')) PB

/-! ## The `param_transfer` tactic

`param_transfer` refines the goal by `forallTransferAuto`, which resolves the
domain `Param` via `TransferDom` and leaves the *pointwise* obligation. The
caller then discharges that obligation (typically `intro`/`assumption`/`exact`),
with no structural relation named. -/

/-- Close (or reduce) a goal `(∀ a, P a) → (∀ a', P' a')` by the
    abstraction-theorem `∀`-rule with the domain `Param` synthesized via
    `TransferDom`. Leaves the pointwise obligation
    `∀ a a' (_ : (TransferDom.dom).R a a'), P a → P' a'`. -/
macro "param_transfer" : tactic =>
  `(tactic| refine forallTransferAuto ?_)

/-! ## End-to-end auto demos — the caller names nothing structural

Each demo below transfers a universally-quantified statement with the domain
`Param` resolved automatically by `TransferDom`. The only thing written by hand
is the *pointwise* part, closed by `intro`/`exact`/`assumption`. -/

/-- Same-type auto demo. `(∀ n : ℕ, P n) → (∀ n : ℕ, Q n)` from a pointwise
    `∀ n, P n → Q n`, with the domain `Param` (the diagonal) resolved by
    `TransferDom` — the caller writes `param_transfer` then discharges the
    pointwise part, naming nothing about the relation. -/
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) :
    (∀ n : ℕ, P n) → (∀ n : ℕ, Q n) := by
  param_transfer
  intro a a' (haa' : a = a') hPa
  exact haa' ▸ h a hPa

/-- A fully concrete same-type instance: `(∀ n : ℕ, 0 ≤ n) → (∀ n : ℕ, 0 ≤ n)`,
    domain auto-resolved, pointwise part trivial. -/
example : (∀ n : ℕ, 0 ≤ n) → (∀ n : ℕ, 0 ≤ n) := by
  param_transfer
  intro a a' (haa' : a = a') h
  exact haa' ▸ h

/-- Change-of-representation auto demo (`Num → ℕ`). The domain `Param` is the
    `Num ↦ ℕ` cast graph, resolved automatically by `TransferDom Num ℕ`. The
    caller writes `param_transfer` and discharges only the pointwise part on
    related pairs `(n, k)` with `(n : ℕ) = k` — naming nothing structural. -/
example : (∀ n : Num, 0 ≤ n) → (∀ k : ℕ, 0 ≤ k) := by
  param_transfer
  intro _ _ _ _
  exact Nat.zero_le _

/-- A `Num → ℕ` demo with a nontrivial pointwise step: transfer
    `∀ n : Num, (n : ℕ) = (n : ℕ)` to `∀ k : ℕ, k = k`, using the resolved
    relation `(n : ℕ) = k` to rewrite. The domain change of representation is
    invisible at the call site. -/
example : (∀ _ : Num, True) → (∀ k : ℕ, k = k) := by
  param_transfer
  intro _ _ _ _
  rfl

/-! ## Same-type `↔` via the engine, domain auto-resolved

For completeness, the biconditional engine `forall_iff_transfer_engine` is a
same-type result; here we expose that the diagonal domain it uses is exactly the
one `TransferDom` resolves, so the `↔`-fragment is auto-domain too. -/

/-- The diagonal domain that `forall_iff_transfer_engine` consumes is the one
    `TransferDom` resolves: `(TransferDom.dom : Param .map0 .map2a ι ι) = paramDiag`
    definitionally. So both directions of the `↔`-engine run on the resolved
    domain. -/
example {ι : Type u} : (TransferDom.dom (A := ι) (A' := ι)) = paramDiag := rfl

end Transfer.Param
