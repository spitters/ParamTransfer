/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Integrations.ParamPredTrans
public import Transfer.Hierarchy.ParamHierarchy

/-!
# Relational refinement of abstract predicate transformers

`RRelPT γ RE R wa wc` is the relation `RRel` of `Integrations/ParamPredTrans.lean`
stated for two predicate transformers `wa` and `wc` given as functions, with no
`WP` instance behind them. A deep-embedded language with its own weakest
precondition (an inductive syntax and a `wp` defined by recursion on it) is related
to a monadic computation, or to another such language, through `RRelPT`. The
second argument of each transformer has an arbitrary type: `ExceptConds ps` for a
`WP` instance, a second postcondition (for example a control-flow postcondition)
for a deep embedding. `RRel` is `RRelPT` at the two `wp` transformers
(`rrel_iff_rrelPT`).

`Param.rrel` packages `RRel γ RE p.R` between two monads as a `Param` at
`(map2a, map2a)`, given functions `M A → N A` and `N A' → M A'` that are
`RRel`-related to the identity at equality.

## Main definitions

* `RRelPT γ RE R wa wc`: the relational refinement of two predicate transformers.
* `Param.rrel`: `RRel` as a `Param .map2a .map2a (M A) (N A')`.

## Main results

* `rrel_iff_rrelPT`, `RRelPT.of_rrel`: `RRel` is `RRelPT` at the `wp` transformers.
* `RRelPT.transport`: an entailment into `wa` transports to one into `wc`.
* `RRelPT.trans`: composition along relational composition.
* `RRelPT.closed_form`: `RRelPT` at the strongest related postcondition, for a
  target transformer monotone in its postcondition.
* `RRel.map_left`, `RRel.map_right`: `Functor.map` on either side.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

universe u v w x y z u₁ u₂

namespace Transfer.Param

open Std.Do

/-- The relational refinement of two predicate transformers `wa` and `wc`. For all
    postconditions `Q`, `Q'` with `γ (Q a) ⊢ₛ Q' a'` whenever `R a a'`, and all
    second arguments `E`, `E'` with `RE E E'`, the image under `γ` of `wa Q E`
    entails `wc Q' E'`. -/
def RRelPT {ps ps' : PostShape.{u}} {ε : Type x} {ε' : Type y} (γ : AssnRel ps ps')
    (RE : ε → ε' → Prop) {α : Type u₁} {α' : Type u₂} (R : α → α' → Prop)
    (wa : (α → Assertion ps) → ε → Assertion ps)
    (wc : (α' → Assertion ps') → ε' → Assertion ps') : Prop :=
  ∀ (Q : α → Assertion ps) (Q' : α' → Assertion ps') (E : ε) (E' : ε'),
    (∀ a a', R a a' → γ.γ (Q a) ⊢ₛ Q' a') → RE E E' → γ.γ (wa Q E) ⊢ₛ wc Q' E'

section RRelPT

variable {ps ps' ps'' : PostShape.{u}} {ε : Type x} {ε' : Type y} {ε'' : Type z}
  {α α' α'' : Type u}

/-- `RRel` is `RRelPT` at the two `wp` transformers. -/
theorem rrel_iff_rrelPT {M : Type u → Type v} {N : Type u → Type w} [WP M ps] [WP N ps']
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    {β β' : Type u} {R : β → β' → Prop} {c : M β} {c' : N β'} :
    RRel γ RE R c c' ↔
      RRelPT γ RE R (fun Q E => wp⟦c⟧ (Q, E)) (fun Q' E' => wp⟦c'⟧ (Q', E')) :=
  Iff.rfl

/-- An `RRel` witness is an `RRelPT` witness at the two `wp` transformers. -/
theorem RRelPT.of_rrel {M : Type u → Type v} {N : Type u → Type w} [WP M ps] [WP N ps']
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    {β β' : Type u} {R : β → β' → Prop} {c : M β} {c' : N β'} (h : RRel γ RE R c c') :
    RRelPT γ RE R (fun Q E => wp⟦c⟧ (Q, E)) (fun Q' E' => wp⟦c'⟧ (Q', E')) :=
  rrel_iff_rrelPT.mp h

/-- An entailment `P ⊢ₛ wa Q E` transports along `RRelPT γ RE R wa wc` to the
    entailment `γ P ⊢ₛ wc Q' E'`, for postconditions related by `R` up to `γ` and
    second arguments related by `RE`. -/
theorem RRelPT.transport {γ : AssnRel ps ps'} {RE : ε → ε' → Prop} {R : α → α' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wc : (α' → Assertion ps') → ε' → Assertion ps'} (h : RRelPT γ RE R wa wc)
    {P : Assertion ps} {Q : α → Assertion ps} {E : ε} {Q' : α' → Assertion ps'} {E' : ε'}
    (hQ : ∀ a a', R a a' → γ.γ (Q a) ⊢ₛ Q' a') (hE : RE E E') (ht : P ⊢ₛ wa Q E) :
    γ.γ P ⊢ₛ wc Q' E' :=
  (γ.mono ht).trans (h Q Q' E E' hQ hE)

/-- `RRelPT` composes: from `RRelPT γ₁ RE₁ R₁ wa wb` and `RRelPT γ₂ RE₂ R₂ wb wc`
    follows `RRelPT (γ₂ ∘ γ₁) (RE₁ ; RE₂) (R₁ ; R₂) wa wc`, where `;` is relational
    composition through an intermediate value or second argument. -/
theorem RRelPT.trans {γ₁ : AssnRel ps ps'} {γ₂ : AssnRel ps' ps''}
    {RE₁ : ε → ε' → Prop} {RE₂ : ε' → ε'' → Prop}
    {R₁ : α → α' → Prop} {R₂ : α' → α'' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wb : (α' → Assertion ps') → ε' → Assertion ps'}
    {wc : (α'' → Assertion ps'') → ε'' → Assertion ps''}
    (h₁ : RRelPT γ₁ RE₁ R₁ wa wb) (h₂ : RRelPT γ₂ RE₂ R₂ wb wc) :
    RRelPT (γ₂.comp γ₁) (fun E E'' => ∃ E', RE₁ E E' ∧ RE₂ E' E'')
      (fun a a'' => ∃ a', R₁ a a' ∧ R₂ a' a'') wa wc := by
  rintro Q Q'' E E'' hQ ⟨E', hE₁, hE₂⟩
  refine (γ₂.mono (h₁ Q (fun b => spred(∃ p : {a // R₁ a b}, γ₁.γ (Q p.1))) E E'
    (fun a b hab => SPred.exists_intro' ⟨a, hab⟩ .rfl) hE₁)).trans
    (h₂ _ Q'' E' E'' (fun b a'' hb => ?_) hE₂)
  exact (γ₂.exists_le _).trans (SPred.exists_elim fun p => hQ p.1 a'' ⟨b, p.2, hb⟩)

/-- For a target transformer `wc` monotone in its postcondition, `RRelPT` holds
    exactly when it holds at the strongest postcondition related to `Q`, namely
    `fun a' => ∃ a, ⌜R a a'⌝ ∧ γ (Q a)`. -/
theorem RRelPT.closed_form {γ : AssnRel ps ps'} {RE : ε → ε' → Prop} {R : α → α' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wc : (α' → Assertion ps') → ε' → Assertion ps'}
    (hmono : ∀ (Q₁ Q₂ : α' → Assertion ps') (E' : ε'),
      (∀ a', Q₁ a' ⊢ₛ Q₂ a') → wc Q₁ E' ⊢ₛ wc Q₂ E') :
    RRelPT γ RE R wa wc ↔
      ∀ (Q : α → Assertion ps) (E : ε) (E' : ε'), RE E E' →
        γ.γ (wa Q E) ⊢ₛ wc (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (Q a))) E' := by
  constructor
  · intro h Q E E' hE
    exact h Q _ E E'
      (fun a a' hr => SPred.exists_intro' a (SPred.and_intro (SPred.pure_intro hr) .rfl)) hE
  · intro h Q Q' E E' hQ hE
    exact (h Q E E' hE).trans (hmono _ _ E'
      fun a' => SPred.exists_elim fun a => SPred.pure_elim_l fun hr => hQ a a' hr)

end RRelPT

/-! ## `Functor.map` on either side of `RRel` -/

section Map

variable {M : Type u → Type v} {N : Type u → Type w} {ps ps' : PostShape.{u}}
  {α α' β β' : Type u}

/-- `RRel` is preserved by `Functor.map` on the target side, along a map of the
    value relation. -/
theorem RRel.map_right [WP M ps] [Monad N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {S : α → β' → Prop} {c : M α} {c' : N α'} (h : RRel γ RE R c c') (f : α' → β')
    (hf : ∀ a a', R a a' → S a (f a')) : RRel γ RE S c (f <$> c') := by
  intro Q Q' E E' hQ hE
  rw [WPMonad.wp_map]
  exact h Q (fun a' => Q' (f a')) E E' (fun a a' hr => hQ a (f a') (hf a a' hr)) hE

/-- `RRel` is preserved by `Functor.map` on the source side, along a map of the
    value relation. -/
theorem RRel.map_left [Monad M] [WPMonad M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {S : β → α' → Prop} {c : M α} {c' : N α'} (h : RRel γ RE R c c') (g : α → β)
    (hg : ∀ a a', R a a' → S (g a) a') : RRel γ RE S (g <$> c) c' := by
  intro Q Q' E E' hQ hE
  rw [WPMonad.wp_map]
  exact h (fun a => Q (g a)) Q' E E' (fun a a' hr => hQ (g a) a' (hg a a' hr)) hE

end Map

/-! ## `RRel` as a `Param` -/

/-- `RRel γ RE p.R` between the monads `M` and `N` is a `Param` at
    `(map2a, map2a)`, given `φ : M A → N A` with `RRel γ RE Eq c (φ c)` and
    `ψ : N A' → M A'` with `RRel γ RE Eq (ψ c') c'`. The forward map is
    `p.fwd.map <$> φ c`, the backward map `p.bwd.map <$> ψ c'`. At `M = N`,
    `γ = AssnRel.id ps`, `RE = Eq` and `φ = ψ = id` this is `Param.rcomp`.

    `(map2a, map2a)` is the largest class reached. `Map2bHas` forward would need
    `RRel γ RE p.R c c' → p.fwd.map <$> φ c = c'`: `RRel` is a refinement order on
    the images under `wp`, so it determines `c'` up to its weakest precondition and
    not as a term, and neither `WPMonad` nor `AssnRel` makes `wp` injective. The
    backward direction fails in the same way. -/
def Param.rrel {M N : Type u → Type u} {ps ps' : PostShape.{u}} [Monad M] [WPMonad M ps]
    [Monad N] [WPMonad N ps'] (γ : AssnRel ps ps')
    (RE : ExceptConds ps → ExceptConds ps' → Prop) {A A' : Type u}
    (p : Param .map2a .map2a A A')
    (φ : M A → N A) (hφ : ∀ c, RRel γ RE (· = ·) c (φ c))
    (ψ : N A' → M A') (hψ : ∀ c', RRel γ RE (· = ·) (ψ c') c') :
    Param .map2a .map2a (M A) (N A') where
  R := RRel γ RE p.R
  fwd :=
    { map := fun c => p.fwd.map <$> φ c
      map_in_R := by
        rintro c _ rfl
        exact (hφ c).map_right p.fwd.map fun a _ h => by subst h; exact p.fwd.map_in_R a _ rfl }
  bwd :=
    { map := fun c' => p.bwd.map <$> ψ c'
      map_in_R := by
        rintro c' _ rfl
        exact (hψ c').map_left p.bwd.map fun a _ h => by subst h; exact p.bwd.map_in_R a _ rfl }

end Transfer.Param

end
