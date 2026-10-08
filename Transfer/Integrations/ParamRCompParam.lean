/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Integrations.ParamRCompOk
public import Transfer.Hierarchy.ParamHierarchy

/-!
# `RComp`/`RCompOk` as instances of `Param`, and their composition

This module connects the Kleisli-level logical relations `RComp`/`RCompOk`
(`Integrations/ParamTripleTransfer.lean`, `Integrations/ParamRCompOk.lean`) to the
`Param` annotated-relation hierarchy (`Hierarchy/ParamHierarchy.lean`).

## `RComp` is a `Param` at `(map2a, map2a)`

Given `p : Param .map2a .map2a A A'` and a `WPMonad M ps`, `Param.rcomp p` packages
`RComp p.R` with forward/backward `Map2aHas` records whose maps are `Functor.map`
of `p`'s forward/backward maps. The content is each record's `map_in_R` field: a
value relatedness `∀ a, p.R a (f a)` (`p.fwd.map_in_R`, resp. `p.bwd.map_in_R`)
lifts through `WPMonad.wp_map` and `(wp c).mono` to `RComp p.R c (f <$> c)`
(resp. the backward `RComp p.R (g <$> c') c'`).

`(map2a, map2a)` is the largest class this construction reaches, for both
directions, and the ceiling is real:

* `Map1Has (RComp p.R)` is available from `p.fwd : Map1Has p.R` alone (no proof
  obligation), but carries no relational content — `Map1Has` requires nothing
  beyond a function.
* `Map2bHas`/`Map3Has` forward would additionally require
  `RComp p.R c c' → f <$> c = c'`: that `RComp`-relatedness (a one-directional
  `wp`-refinement order, reflexive by `RComp.refl` but not an equivalence)
  determines `c'` as *literally* `f <$> c`. This needs `wp` to be injective on
  `M`'s carrier (so that `wp`-refinement in both directions forces term
  equality) — a property `WPMonad` does not assume and no instance in
  `WP/Monad.lean` (`Id`, `StateT`, `ExceptT`, `Except`, `Option`, `EStateM`, …)
  needs. This module does not construct a formal counterexample instance; the
  obstruction is the missing law `wp`-injectivity, stated here as the
  boundary of what `Map2aHas.map_in_R`'s one-directional argument reaches.

## `RCompOk` is not generically a `Param`

`RCompOk Rα : M A → N A' → Prop` relates computations in *two* monads, one
possibly failing (`WP M ps`), one total (`WP N .pure`). A `Param m n (M A) (N A')`
instance needs a forward map `M A → N A'` (`Map1Has`, free) and, for any
relational content (`Map2aHas`), a proof that `RCompOk Rα c (map c)` holds for
*every* `c : M A` — including a `c` that never succeeds, where `RCompOk`'s
partial-correctness `⇓?` on the `M` side imposes no constraint, so any map value
there is fine, but including also a `c` for whose success value `map` must
recover the `p.fwd.map`-related partner. Recovering a value from an arbitrary
`c : M A` (to feed `p.fwd.map`) is exactly a monad morphism `M ⟶ N` compatible
with `wp` (an "extraction"): `Id`, `Option`, `Except ε`, `EStateM ε σ` admit one
concretely (`Option.getD`, `Except.getD`-style, run-and-default), but a fully
abstract `M` with only `[Monad M] [WPMonad M ps]` does not — `WPMonad` gives no
way to turn a computation into a value. So the only level `Param` reaches for
*generic* `M`, `N` is the content-free `Map1Has`; `Map2aHas` (in either direction)
needs the extraction morphism as extra data, which is a hypothesis outside
`RCompOk`'s own signature. `Param.rcompOkTrivial` below records the free `map0`
instance; no `map2a` instance is stated, since it would need that extra
hypothesis and is out of the scope of `RCompOk`'s two-monad signature.

## Composition and identity

`RComp.trans` composes two `RComp`s in the same monad along relation composition
(`∃ b, Rα a b ∧ Rβ b c`), using only `WP` (no `Monad`/`WPMonad` needed — it is
pure `wp`-entailment chaining through `SPred.exists`/`SPred.and`).

`RCompOk.trans` composes `RCompOk Rα : M → N` with `RCompOk Rβ : N → P` when both
`N` and `P` are total (`WP N .pure`, `WP P .pure`): at a `.pure` shape the
partial-correctness postcondition `⇓?` and the total-correctness postcondition
`⇓` coincide (`ExceptConds .pure = PUnit` has one element, so
`ExceptConds.false = ExceptConds.true` by `rfl`), so the total-side result of the
first step feeds directly as the total-side hypothesis of the second.

`RCompOk.reflEq` is the identity-at-`Eq` fact for `RCompOk`, available exactly
when the "failing" side is itself total (`WP M .pure`) — the degenerate case
where `RCompOk` and `RComp` coincide up to the same `⇓?`/`⇓` collapse.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

universe u v w x

namespace Transfer.Param

open Std.Do

/-! ## `RComp` as a `Param` -/

/-- **`RComp` is a `Param` at `(map2a, map2a)`.** Given an element relation at
    forward/backward `map2a`, the Kleisli lift `RComp p.R` is again forward/backward
    `map2a`, with maps `Functor.map` of `p`'s forward/backward maps. This is the
    largest class the construction reaches (see the module docstring for why
    `map2b`/`map3` is out of reach in general). -/
def Param.rcomp {M : Type u → Type u} {ps : PostShape.{u}} [Monad M] [WPMonad M ps]
    {A A' : Type u} (p : Param .map2a .map2a A A') :
    Param .map2a .map2a (M A) (M A') where
  R := RComp (ps := ps) p.R
  fwd :=
    { map := fun c => p.fwd.map <$> c
      map_in_R := by
        rintro c _ rfl
        intro Q Q' E hQ
        rw [WPMonad.wp_map]
        exact (wp c).mono _ _
          ⟨fun a => hQ a (p.fwd.map a) (p.fwd.map_in_R a (p.fwd.map a) rfl),
            ExceptConds.entails.refl E⟩ }
  bwd :=
    { map := fun c' => p.bwd.map <$> c'
      map_in_R := by
        rintro c' _ rfl
        intro Q Q' E hQ
        rw [WPMonad.wp_map]
        exact (wp c').mono _ _
          ⟨fun a' => hQ (p.bwd.map a') a' (p.bwd.map_in_R a' (p.bwd.map a') rfl),
            ExceptConds.entails.refl E⟩ }

/-! ## `RCompOk`: the free `map0` instance -/

/-- The content-free `Param` instance `RCompOk` always admits: `Map0Has` needs no
    data. No `Map2aHas` instance is stated (see the module docstring): it would
    need a `wp`-respecting extraction `M A → A`, data outside `RCompOk`'s own
    two-monad signature. -/
def Param.rcompOkTrivial {M : Type u → Type u} {ps : PostShape.{u}} [WP M ps]
    {N : Type u → Type u} [WP N .pure] {A A' : Type u} (Rα : A → A' → Prop) :
    Param .map0 .map0 (M A) (N A') where
  R := RCompOk (N := N) Rα
  fwd := ⟨⟩
  bwd := ⟨⟩

/-! ## Composition -/

/-- **`RComp` composes along relation composition.** Sequencing two
    `RComp`-witnesses in the same monad gives a witness for the composed value
    relation `∃ b, Rα a b ∧ Rβ b c`. Needs only `WP M ps` — no `Monad`/`WPMonad`,
    since it chains `wp`-entailment through `SPred.exists`/`SPred.and` alone. -/
theorem RComp.trans {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {A B C : Type u} {Rα : A → B → Prop} {Rβ : B → C → Prop}
    {c : M A} {c' : M B} {c'' : M C}
    (h1 : RComp (ps := ps) Rα c c') (h2 : RComp (ps := ps) Rβ c' c'') :
    RComp (ps := ps) (fun a x => ∃ b, Rα a b ∧ Rβ b x) c c'' := by
  intro Q Q'' E hQ
  refine (h1 Q (fun b => spred(∃ a, ⌜Rα a b⌝ ∧ Q a)) E
    (fun a b hab => SPred.exists_intro' a (SPred.and_intro (SPred.pure_intro hab) .rfl))).trans
    (h2 _ Q'' E (fun b x hbx =>
      SPred.exists_elim (fun a => SPred.pure_elim_l (fun hab => hQ a x ⟨b, hab, hbx⟩))))

/-- **`RCompOk` composes across two total codomains.** `RCompOk Rα : M → N` and
    `RCompOk Rβ : N → P` compose to `RCompOk (∃ b, Rα a b ∧ Rβ b c) : M → P`
    whenever both `N` and `P` are total (`WP N .pure`, `WP P .pure`): at a `.pure`
    shape `⇓?` and `⇓` coincide by `rfl` (`ExceptConds .pure = PUnit`), so the
    total-correctness conclusion about `c'` from the second witness feeds directly
    as the total-correctness hypothesis the first witness expects. -/
theorem RCompOk.trans {M : Type u → Type v} {ps : PostShape.{u}}
    {N : Type u → Type w} {P : Type u → Type x}
    [WP M ps] [WP N .pure] [WP P .pure]
    {A B C : Type u} {Rα : A → B → Prop} {Rβ : B → C → Prop}
    {c : M A} {c' : N B} {c'' : P C}
    (h1 : RCompOk Rα c c') (h2 : RCompOk Rβ c' c'') :
    RCompOk (fun a x => ∃ b, Rα a b ∧ Rβ b x) c c'' := by
  intro Q'' hQ''
  have hmid : ⊢ₛ wp⟦c'⟧ (⇓ b => ⌜∃ x, Rβ b x ∧ Q'' x⌝) := h2 Q'' hQ''
  refine (h1 _ hmid).trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
  exact SPred.pure_elim' fun ⟨b, hab, x, hbx, hqx⟩ => SPred.pure_intro ⟨x, ⟨b, hab, hbx⟩, hqx⟩

/-! ## Identity -/

/-- **`RCompOk` at `Eq` is reflexive when the `M`-side is itself total.** The
    degenerate case `N := M`, `ps := .pure`, where `RCompOk`'s partial- and
    total-correctness postconditions coincide (`⇓? = ⇓` by `rfl` at `.pure`), so
    `RCompOk` reduces to the same `wp`-monotonicity argument as `RComp.refl`. -/
theorem RCompOk.reflEq {M : Type u → Type v} [WP M .pure] {A : Type u} (c : M A) :
    RCompOk (N := M) (Eq (α := A)) c c := by
  intro Q' hQ'
  exact hQ'.trans ((wp c).mono _ _
    ⟨fun a => SPred.exists_intro' a (SPred.and_intro (SPred.pure_intro rfl) .rfl),
      ExceptConds.entails.pure⟩)

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.Param.rcomp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Param.rcomp

/-- info: 'Transfer.Param.RComp.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RComp.trans

/-- info: 'Transfer.Param.RCompOk.trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RCompOk.trans

/-- info: 'Transfer.Param.RCompOk.reflEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RCompOk.reflEq

end AxiomAudit

end Transfer.Param
