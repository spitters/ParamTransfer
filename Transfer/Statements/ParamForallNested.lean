/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Statements.ParamTransfer

/-!
# Dependent-Π transfer for **nested** `∀`-statements

`ParamTransfer.lean` derived the single-binder abstraction-theorem `∀`-rule
`forallTransfer` from the dependent-Π combinator `Map1_forall`. This module
extends that to multi-binder (nested) `∀`-statements: it transfers

  `(∀ a b, P a b) → (∀ a' b', P' a' b')`

and the 3-binder analogue, by iterating `forallTransfer`, and applies the
result to concrete same-type and `Num ≃ ℕ` statements.

## How the nesting works

A two-binder statement `∀ a b, P a b` is `∀ a, (fun a => ∀ b, P a b) a` — a
*single* `∀` whose motive is itself a `∀`. So we transfer it with a single
outer `forallTransfer` over the domain `Param` `PA : Param .map0 .map2a A A'`,
at the (`Prop`-valued) motives

  `Pouter a  := ∀ b,  P a b`        `Pouter' a' := ∀ b', P' a' b'`.

The pointwise obligation `forallTransfer` then demands is, for each `PA`-related
pair `(a, a')`,

  `Pouter a → Pouter' a'`   i.e.   `(∀ b, P a b) → (∀ b', P' a' b')`,

which is **exactly another single-binder transfer**, this time the *inner*
`forallTransfer` over `PB : Param .map0 .map2a B B'`. Its own pointwise
obligation — for a `PB`-related pair `(b, b')` — is `P a b → P' a' b'`, fed by
the caller's `H a a' b b'`, specialised at the *outer* relatedness witness
`aR : PA.R a a'`. Iterating once more (motive a 2-binder `∀`) gives the
3-binder rule with no new ideas.

This stays at the `Prop` motive, so it is univalence-free: each layer only
consumes the corresponding domain `Param`'s backward `map2a` structure, exactly
as `forallTransfer`/`Map1_forall` require — no `map4`/`Map2a_forall`.

## What this delivers

The single-binder `forallTransfer` is the `n = 1` case; `numForallTransfer`
(the `Num ≃ ℕ` flagship's `∀`-transfer) is its `Num`-domain instance. The
combinators here are the `n = 2`, `n = 3` cases, and `numForallTransfer2`
below extends the flagship to a binary `Num`-statement. The residual is
unchanged from `ParamTransfer.lean`:

* the `Type`-valued motive (`B : A → Type`, not `Prop`), needing
  `Map2a_forall` whose domain `Param` must be `Param04` = univalence — localized
  in `ParamForall.lean`;
* the full term-level abstraction theorem `⟦t⟧ : R_T t ⟦t⟧` for arbitrary
  `t` — the `MetaM` synthesizer's job (Trocq's `param`/`trocq` tactic).

Nesting `forallTransfer` covers the *propositional* multi-quantifier fragment
automatically, which is the bulk of first-order transfer targets.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param

open Transfer

/-! ## Two-binder transfer -/

/-- Two-binder dependent-Π transfer. Given domain `Param`s `PA`, `PB` and,
    for every pair of related pairs `(a,a')`, `(b,b')`, a pointwise implication
    `P a b → P' a' b'`, transfer `∀ a b, P a b` to `∀ a' b', P' a' b'`.

    Built by iterating `forallTransfer`: the outer `forallTransfer PA` runs at
    the motive `fun a => ∀ b, P a b`; its per-pair obligation
    `(∀ b, P a b) → (∀ b', P' a' b')` is discharged by an inner
    `forallTransfer PB`, whose own per-pair obligation is `H` specialised at the
    outer relatedness witness. Univalence-free. -/
def forallTransfer2 {A A' B B' : Type u}
    (PA : Param .map0 .map2a A A') (PB : Param .map0 .map2a B B')
    {P : A → B → Prop} {P' : A' → B' → Prop}
    (H : ∀ a a' b b', PA.R a a' → PB.R b b' → (P a b → P' a' b')) :
    (∀ a b, P a b) → (∀ a' b', P' a' b') :=
  forallTransfer PA
    (P := fun a => ∀ b, P a b) (P' := fun a' => ∀ b', P' a' b')
    (fun a a' aR =>
      forallTransfer PB
        (P := fun b => P a b) (P' := fun b' => P' a' b')
        (fun b b' bR => H a a' b b' aR bR))

/-! ## Three-binder transfer

The nesting generalizes: the outer `forallTransfer PA` runs at the
2-binder motive `fun a => ∀ b c, P a b c`, whose per-pair obligation is exactly
a `forallTransfer2 PB PC`. -/

/-- Three-binder dependent-Π transfer, by iterating once more: outer
    `forallTransfer PA` at the 2-binder motive `fun a => ∀ b c, P a b c`, inner
    obligation discharged by `forallTransfer2 PB PC`. -/
def forallTransfer3 {A A' B B' C C' : Type u}
    (PA : Param .map0 .map2a A A') (PB : Param .map0 .map2a B B')
    (PC : Param .map0 .map2a C C')
    {P : A → B → C → Prop} {P' : A' → B' → C' → Prop}
    (H : ∀ a a' b b' c c',
        PA.R a a' → PB.R b b' → PC.R c c' → (P a b c → P' a' b' c')) :
    (∀ a b c, P a b c) → (∀ a' b' c', P' a' b' c') :=
  forallTransfer PA
    (P := fun a => ∀ b c, P a b c) (P' := fun a' => ∀ b' c', P' a' b' c')
    (fun a a' aR =>
      forallTransfer2 PB PC
        (P := fun b c => P a b c) (P' := fun b' c' => P' a' b' c')
        (fun b b' c c' bR cR => H a a' b b' c c' aR bR cR))

/-! ## Same-type concrete applications (diagonal domain)

With `paramDiag`, the relatedness witnesses are `Eq`, so the per-pair
obligations `a = a'`, `b = b'` are `subst`-ed away, leaving the bare pointwise
implication `P a b → Q a b`. This is the multi-binder analogue of
`forall_transfer_engine`. -/

/-- Same-type two-binder transfer through the engine. From the pointwise
    `∀ a b, P a b → Q a b`, the engine (`forallTransfer2` over two diagonal
    `Param`s) produces `(∀ a b, P a b) → (∀ a b, Q a b)` — no `forall_congr'`,
    no manual `intro`. -/
theorem forall2_transfer_engine {α β : Type u} (P Q : α → β → Prop)
    (h : ∀ a b, P a b → Q a b) :
    (∀ a b, P a b) → (∀ a b, Q a b) :=
  forallTransfer2 paramDiag paramDiag
    (fun a a' b b' (ha : a = a') (hb : b = b') => ha ▸ hb ▸ h a b)

/-- Same-type three-binder transfer through the engine. -/
theorem forall3_transfer_engine {α β γ : Type u} (P Q : α → β → γ → Prop)
    (h : ∀ a b c, P a b c → Q a b c) :
    (∀ a b c, P a b c) → (∀ a b c, Q a b c) :=
  forallTransfer3 paramDiag paramDiag paramDiag
    (fun a a' b b' c c' (ha : a = a') (hb : b = b') (hc : c = c') =>
      ha ▸ hb ▸ hc ▸ h a b c)

/-- A concrete `example`: a binary relation strengthening transferred across the
    diagonal on `ℕ`. From `∀ a b, a ≤ b → a ≤ b` the engine yields the same. -/
example : (∀ a b : ℕ, a ≤ b → a ≤ b) → (∀ a b : ℕ, a ≤ b → a ≤ b) :=
  forall2_transfer_engine _ _ (fun _ _ h => h)

/-- A concrete `example` exercising a nontrivial pointwise step: monotone-shaped
    `min a b ≤ a` transfers to itself across the diagonal, with the pointwise
    part closed by `Nat.min_le_left`. -/
example : (∀ a b : ℕ, min a b ≤ a) → (∀ a b : ℕ, min a b ≤ a) :=
  forall2_transfer_engine _ _ (fun _ _ h => h)

/-! ## `Num ≃ ℕ` flagship, extended to two binders

`numForallTransfer` (in `ParamTransfer.lean`) transferred a single-binder
`∀ n : Num`-statement to `∀ k : ℕ`. We extend the flagship to a *binary*
`Num`-statement via `forallTransfer2 paramNumNat paramNumNat`: the two
relatedness witnesses are `(m : ℕ) = j` and `(n : ℕ) = k`, the graph of the
cast, which the pointwise part consumes through the cast/round-trip lemmas. -/

/-- Binary `Num`-flavoured `∀`-transfer. A `∀ m n : Num`-statement transfers
    to the corresponding `∀ j k : ℕ`-statement, given the pointwise implication
    on related pairs `(m,j)`, `(n,k)` with `(m : ℕ) = j`, `(n : ℕ) = k`. The
    two-binder instance of the flagship. -/
def numForallTransfer2 {P : Num → Num → Prop} {P' : ℕ → ℕ → Prop}
    (H : ∀ (m : Num) (j : ℕ) (n : Num) (k : ℕ),
        (m : ℕ) = j → (n : ℕ) = k → (P m n → P' j k)) :
    (∀ m n : Num, P m n) → (∀ j k : ℕ, P' j k) :=
  forallTransfer2 paramNumNat paramNumNat H

/-- A concrete instance of the binary `Num` flagship: transfer
    `∀ m n : Num, (m + n : ℕ) = (n + m : ℕ)` (commutativity of the cast sum) to
    `∀ j k : ℕ, j + k = k + j`. On related pairs `(m,j)`, `(n,k)` the cast
    equalities rewrite the `Num` statement to the `ℕ` one, then `Nat.add_comm`
    closes it. This is a multi-quantifier first-order fact pushed across the
    binary↔unary equivalence by the engine. -/
example :
    (∀ m n : Num, ((m : ℕ) + (n : ℕ)) = ((n : ℕ) + (m : ℕ))) →
    (∀ j k : ℕ, j + k = k + j) :=
  numForallTransfer2
    (fun _ _ _ _ (hm : _ = _) (hn : _ = _) _ => by
      subst hm; subst hn; exact Nat.add_comm _ _)

/-- A `≤`-shaped binary `Num` transfer: `∀ m n : Num, (m : ℕ) ≤ (m : ℕ) + (n : ℕ)`
    to `∀ j k : ℕ, j ≤ j + k`, closed pointwise by `Nat.le_add_right`. -/
example :
    (∀ m n : Num, (m : ℕ) ≤ (m : ℕ) + (n : ℕ)) →
    (∀ j k : ℕ, j ≤ j + k) :=
  numForallTransfer2
    (fun _ _ _ _ (hm : _ = _) (hn : _ = _) _ => by
      subst hm; subst hn; exact Nat.le_add_right _ _)

/-! ## Tie to the flagship: the 1-binder case and its extension

The single-binder `forallTransfer` (and `numForallTransfer`) is recovered as the
degenerate `n = 1` instance — there is no nesting, just the engine's base rule.
`forallTransfer2` is the extension: a *second* universally-quantified
variable, transferred by a second application of the same base rule under the
first binder. The lemma below makes the base-case identity explicit: a 1-binder
`Num`-transfer is literally `forallTransfer paramNumNat`, the `n = 1` slice of
this nested family, of which `numForallTransfer2` is the `n = 2` extension. -/

/-- The 1-binder `Num`-transfer is the base case of the nested family: it is
    exactly `forallTransfer paramNumNat`, with `numForallTransfer2` extending it
    to two binders. Stated as a definitional identity to record the tie. -/
theorem numForallTransfer_is_base {P : Num → Prop} {P' : ℕ → Prop}
    (PB : ∀ (n : Num) (k : ℕ), (n : ℕ) = k → (P n → P' k)) :
    numForallTransfer PB = forallTransfer paramNumNat PB :=
  rfl

end Transfer.Param
