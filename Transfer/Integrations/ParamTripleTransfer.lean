/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransfer
import Std.Do.Triple

/-!
# Transferring a Hoare/`wp` triple through a `Param` relation

This module lifts the abstraction-theorem `∀`-rule (`ParamTransfer.forallTransfer`)
from *propositions* to *monadic computations*: it builds a **triple-transfer
principle**. Given a value-level `Param`-style relation between two computations
and a Hoare triple for the source, it derives the triple for the transferred
computation, using only the `wp_pure`/`wp_bind` algebra of `Std.Do.WPMonad`.

## The Kleisli-level logical relation `RComp`

`ParamForall`/`ParamTransfer` give the abstraction theorem at `R_arrow`/`R_forall`
— the *pure* function level. Talking about *effectful* programs requires the same
logical relation lifted to the Kleisli category of a monad `M`. `RComp Rα c c'`
is exactly that lift, phrased as **`wp`-refinement modulo the value relation**:

  `RComp Rα c c' := ∀ Q Q' E, (∀ a a', Rα a a' → Q a ⊢ₛ Q' a') →`
  `                  wp⟦c⟧ (Q, E) ⊢ₛ wp⟦c'⟧ (Q', E)`

i.e. any success-postcondition pair related pointwise by `Rα` (sharing the
failure barrel `E`) is refined from `c` to `c'` at the level of weakest
preconditions. This is the canonical Reynolds/Kleisli lift: the relation on
computations induced by the relation on values, read through the `wp`
observation.

The two `pure`/`bind` rules below are the compositional core — the
content of the abstraction theorem at the monad level:

* `RComp.pure` — `Rα a a'` gives `RComp Rα (pure a) (pure a')` (via `wp_pure`);
* `RComp.bind` — `RComp Rα c c'` and a pointwise `RComp Rβ (f a) (f' a')` give
  `RComp Rβ (c >>= f) (c' >>= f')` (via `wp_bind`).

`RComp.refl` records the diagonal instance (`Rα = Eq`, `c = c'`): every
computation is `wp`-refinement-related to itself, the `paramDiag` analogue.

## The triple-transfer lemma

`triple_transfer` follows: since `Triple x P Q` is *defined* as
`P ⊢ₛ wp⟦x⟧ Q`, an `RComp`-witness composes on the left with the source triple
to yield the transferred triple. The pure/bind closure means an `RComp`-witness
for a whole do-block can be assembled structurally from witnesses for its
leaves — exactly the abstraction-theorem discipline `ParamTransfer` runs for
`∀`-statements, here for stateful/partial `SPComp` programs.

## Concrete `SPComp` instance

`SPComp.RComp_pure` / `SPComp.triple_transfer` instantiate the principle on the
project's probabilistic monad through the `StdDoBridge` `WPMonad SPComp
spPostShape` instance, and `SPComp.transfer_pure_example` applies it end-to-end on
a `Bool`-valued `SPComp.pure` triple.

## Scope

Proved (univalence-free, `Prop`-predicate triples only):

* the Kleisli logical-relation lift `RComp` and its `pure`/`bind`/`refl` closure
  — the compositional core of the abstraction theorem at the monad level;
* `triple_transfer`, transferring `Triple c P (Q, E)` to `Triple c' P (Q', E)`
  along any `RComp`-witness;
* a concrete `SPComp` instantiation via `StdDoBridge`.

Not implemented here:

* `MetaM`-level synthesis of the `RComp`-witness for an arbitrary do-block (the
  `param`/`trocq`-tactic analogue): here the witness is assembled by hand from
  `RComp.pure`/`RComp.bind`;
* full `mvcgen` integration (generating `RComp`-witnesses from `@[spec]`
  lemmas);
* the quantitative / advantage route is explicitly out of scope: expectation
  transformers are monotone but not conjunctive, so they do not inhabit
  `PredTrans.conjunctiveRaw` (see `StdDoBridge`); quantitative transfer belongs
  to the `Advantage`/`sdist` layer, not to this `Prop`-predicate `wp` principle.
-/

set_option autoImplicit false

universe u v

namespace Transfer.Param

open Std.Do

/-! ## The Kleisli-level logical relation `RComp`

The relation on computations induced by a value relation `Rα`, read through the
`wp` observation: a `wp`-refinement that holds for every `Rα`-related
postcondition pair (sharing the failure barrel). This is the monad-level analogue
of `R_arrow`/`R_forall` from `ParamForall`/`ParamTransfer`. -/

/-- **The Kleisli lift of a value relation.** `RComp Rα c c'` holds when, for
    every pair of success-postconditions related pointwise by `Rα` (sharing one
    failure barrel `E`), the weakest precondition of `c` entails that of `c'`.
    This is the canonical logical-relation lift of `Rα` to `M`-computations,
    observed via `wp`. -/
def RComp {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {α α' : Type u} (Rα : α → α' → Prop) (c : M α) (c' : M α') : Prop :=
  ∀ (Q : α → Assertion ps) (Q' : α' → Assertion ps) (E : ExceptConds ps),
    (∀ a a', Rα a a' → Q a ⊢ₛ Q' a') →
    wp⟦c⟧ (Q, E) ⊢ₛ wp⟦c'⟧ (Q', E)

/-- **`pure` rule of the abstraction theorem at the monad level.** A value
    relatedness `Rα a a'` lifts to computation relatedness of the point
    distributions `pure a`, `pure a'`. Proved through `WPMonad.wp_pure`. -/
theorem RComp.pure {M : Type u → Type v} {ps : PostShape.{u}} [Monad M] [WPMonad M ps]
    {α α' : Type u} (Rα : α → α' → Prop) {a : α} {a' : α'} (h : Rα a a') :
    RComp (M := M) (ps := ps) Rα (Pure.pure a) (Pure.pure a') := by
  intro Q Q' E hQ
  simp only [WPMonad.wp_pure, PredTrans.apply_Pure_pure]
  exact hQ a a' h

/-- **`bind` rule of the abstraction theorem at the monad level.** Sequencing
    two related computations with two pointwise-related continuations yields
    related computations. Proved through `WPMonad.wp_bind`: the bound `wp`
    factors as `wp⟦c⟧ (fun a => wp⟦f a⟧ ·)`, so the head refinement `RComp Rα c
    c'` applies with the per-result continuation refinements as its
    postcondition relatedness. -/
theorem RComp.bind {M : Type u → Type v} {ps : PostShape.{u}} [Monad M] [WPMonad M ps]
    {α α' β β' : Type u} {Rα : α → α' → Prop} {Rβ : β → β' → Prop}
    {c : M α} {c' : M α'} {f : α → M β} {f' : α' → M β'}
    (hc : RComp (ps := ps) Rα c c')
    (hf : ∀ a a', Rα a a' → RComp (ps := ps) Rβ (f a) (f' a')) :
    RComp (ps := ps) Rβ (c >>= f) (c' >>= f') := by
  intro Q Q' E hQ
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  exact hc (fun a => wp⟦f a⟧ (Q, E)) (fun a' => wp⟦f' a'⟧ (Q', E)) E
    (fun a a' h => hf a a' h Q Q' E hQ)

/-- **The diagonal instance** (`paramDiag` analogue): every computation is
    `wp`-refinement-related to itself under the equality value relation. The
    monad-level counterpart of `ParamTransfer.paramDiag`. -/
theorem RComp.refl {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {α : Type u} (c : M α) :
    RComp (ps := ps) (fun a a' => a = a') c c := by
  intro Q Q' E hQ
  have hQQ' : (Q, E) ⊢ₚ (Q', E) :=
    ⟨fun a => hQ a a rfl, ExceptConds.entails.refl E⟩
  exact (wp c).mono _ _ hQQ'

/-! ## The triple-transfer principle

`Triple x P Q` is *defined* as `P ⊢ₛ wp⟦x⟧ Q` (`Std.Do.Triple`), so an
`RComp`-witness — a `wp`-refinement — composes on the left of a source triple to
give the transferred triple. -/

/-- **Triple transfer along an `RComp`-witness.** Given relatedness `RComp Rα c
    c'`, a postcondition relatedness `∀ a a', Rα a a' → Q a ⊢ₛ Q' a'`, and a
    source triple `⦃P⦄ c ⦃Q, E⦄`, derive the transferred triple `⦃P⦄ c' ⦃Q',
    E⦄` (same precondition, same failure barrel). This is the monad-level
    abstraction theorem: the conclusion is read off `Triple = (· ⊢ₛ wp⟦·⟧ ·)`
    by transitivity through the refinement. -/
theorem triple_transfer {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {α α' : Type u} {Rα : α → α' → Prop} {c : M α} {c' : M α'}
    (hcc : RComp (ps := ps) Rα c c')
    {P : Assertion ps} {Q : α → Assertion ps} {Q' : α' → Assertion ps} {E : ExceptConds ps}
    (hQ : ∀ a a', Rα a a' → Q a ⊢ₛ Q' a')
    (ht : Triple c P (Q, E)) :
    Triple c' P (Q', E) :=
  Triple.iff.mpr ((Triple.iff.mp ht).trans (hcc Q Q' E hQ))

/-! ## A worked `pure ≫= pure` assembly

A two-leaf do-block witness assembled from `RComp.pure` and `RComp.bind`,
showing the compositional core composes (the `param`-tactic would synthesize
this automatically). -/

/-- `RComp` for `do let x ← pure a; pure (g x)` vs its primed twin, assembled
    structurally from the `pure`/`bind` rules. The continuation relatedness
    `Rβ (g a) (g' a')` is supplied pointwise. -/
theorem RComp.pure_bind_pure {M : Type u → Type v} {ps : PostShape.{u}} [Monad M] [WPMonad M ps]
    {α α' β β' : Type u} {Rα : α → α' → Prop} {Rβ : β → β' → Prop}
    {a : α} {a' : α'} {g : α → β} {g' : α' → β'}
    (ha : Rα a a') (hg : ∀ x x', Rα x x' → Rβ (g x) (g' x')) :
    RComp (M := M) (ps := ps) Rβ
      (do let x ← Pure.pure a; Pure.pure (g x))
      (do let x ← Pure.pure a'; Pure.pure (g' x)) :=
  RComp.bind (RComp.pure Rα ha)
    (fun x x' hx => RComp.pure Rβ (hg x x' hx))

end Transfer.Param
