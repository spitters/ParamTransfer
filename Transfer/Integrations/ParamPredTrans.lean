/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Integrations.ParamRCompOk

/-!
# Relational refinement of predicate transformers

`RRel γ RE R c c'` relates a computation `c : M α` to a computation `c' : N α'` in
a possibly different monad and postcondition shape. The relation is read through
the two weakest-precondition transformers: for every pair of postconditions
related by `R` up to the assertion map `γ`, and every pair of exception
postconditions related by `RE`, the image under `γ` of the weakest precondition of
`c` entails the weakest precondition of `c'`. This is the refinement weakest
precondition `rwp` of S. Graf's `sgraf812/ascent`, at the top element; the closed
form `RRel.closed_form` states it with upstream's postcondition
`fun a' => ∃ a, ⌜R a a'⌝ ∧ γ (Q a)`.

The two Kleisli relations of ParamTransfer are instances: `RComp`
(`Integrations/ParamTripleTransfer.lean`) is `RRel` at the identity assertion map
and equal exception postconditions (`rcomp_iff_rrel`); `RCompOk`
(`Integrations/ParamRCompOk.lean`) is `RRel` from the total side to the failing
side, at the embedding `⌜·⌝` of `.pure` assertions, with the flipped value
relation and the trivial exception postcondition on the failing side
(`rcompOk_iff_rrel`).

## Main definitions

* `AssnRel ps ps'`: a monotone map of assertions that preserves existentials.
* `AssnRel.id`, `AssnRel.comp`, `AssnRel.purify`: the identity, composition, and
  the embedding of `.pure` assertions by `⌜·⌝`.
* `RRel γ RE R c c'`: the relational refinement of the two `wp` transformers.

## Main results

* `rcomp_iff_rrel`, `rcompOk_iff_rrel`: the two Kleisli relations as instances.
* `RRel.transport`: a triple for `c` gives a triple for `c'`.
* `RRel.trans`: composition along relational composition of value relations and of
  exception relations, with the composite assertion map.
* `RRel.pure`, `RRel.bind`, `RRel.ite`, `RRel.forIn_list`: the rules for the monad
  operations.
* `RRel.closed_form`: `RRel` at the strongest related postcondition.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z

namespace Transfer.Param

open Std.Do

/-- A map of assertions from shape `ps` to shape `ps'` that is monotone for
    entailment and maps an existential over a `Type u` index into the existential
    of the images. -/
structure AssnRel (ps ps' : PostShape.{u}) where
  /-- The map of assertions. -/
  γ : Assertion ps → Assertion ps'
  /-- `γ` is monotone for entailment. -/
  mono : ∀ {P Q : Assertion ps}, (P ⊢ₛ Q) → γ P ⊢ₛ γ Q
  /-- `γ` maps an existential into the existential of the images. -/
  exists_le : ∀ {ι : Type u} (P : ι → Assertion ps),
    γ spred(∃ i, P i) ⊢ₛ spred(∃ i, γ (P i))

namespace AssnRel

/-- The identity map of assertions. -/
def id (ps : PostShape.{u}) : AssnRel ps ps where
  γ P := P
  mono h := h
  exists_le _ := .rfl

/-- The composite `γ₂ ∘ γ₁` of two assertion maps. -/
def comp {ps ps' ps'' : PostShape.{u}} (γ₂ : AssnRel ps' ps'') (γ₁ : AssnRel ps ps') :
    AssnRel ps ps'' where
  γ P := γ₂.γ (γ₁.γ P)
  mono h := γ₂.mono (γ₁.mono h)
  exists_le P := (γ₂.mono (γ₁.exists_le P)).trans (γ₂.exists_le _)

/-- The embedding of an assertion of shape `.pure` (a proposition) into shape `ps`
    as the pure assertion `⌜·⌝`. -/
def purify (ps : PostShape.{u}) : AssnRel .pure ps where
  γ P := ⌜P.down⌝
  mono h := SPred.pure_mono h
  exists_le _ := SPred.pure_elim' fun ⟨i, hi⟩ =>
    SPred.exists_intro' i (SPred.pure_intro hi)

end AssnRel

/-- The relational refinement of the weakest preconditions of `c : M α` and
    `c' : N α'`. For all postconditions `Q`, `Q'` with `γ (Q a) ⊢ₛ Q' a'` whenever
    `R a a'`, and all exception postconditions `E`, `E'` with `RE E E'`, the image
    under `γ` of `wp⟦c⟧ (Q, E)` entails `wp⟦c'⟧ (Q', E')`. -/
def RRel {M : Type u → Type v} {N : Type u → Type w} {ps ps' : PostShape.{u}}
    [WP M ps] [WP N ps'] (γ : AssnRel ps ps')
    (RE : ExceptConds ps → ExceptConds ps' → Prop)
    {α α' : Type u} (R : α → α' → Prop) (c : M α) (c' : N α') : Prop :=
  ∀ (Q : α → Assertion ps) (Q' : α' → Assertion ps') (E : ExceptConds ps)
    (E' : ExceptConds ps'),
    (∀ a a', R a a' → γ.γ (Q a) ⊢ₛ Q' a') → RE E E' →
    γ.γ (wp⟦c⟧ (Q, E)) ⊢ₛ wp⟦c'⟧ (Q', E')

section RRel

variable {M : Type u → Type v} {N : Type u → Type w} {K : Type u → Type x}
  {ps ps' ps'' : PostShape.{u}} {α α' α'' β β' : Type u}

/-! ## The Kleisli relations as instances -/

/-- `RComp` is `RRel` at the identity assertion map and equal exception
    postconditions. -/
theorem rcomp_iff_rrel [WP M ps] {R : α → α' → Prop} {c : M α} {c' : M α'} :
    RComp (ps := ps) R c c' ↔ RRel (AssnRel.id ps) (· = ·) R c c' := by
  constructor
  · rintro h Q Q' E _ hQ rfl
    exact h Q Q' E hQ
  · intro h Q Q' E hQ
    exact h Q Q' E E hQ rfl

/-- `RCompOk R c c'` is `RRel` from the total computation `c'` to the failing
    computation `c`, at the embedding `⌜·⌝` of `.pure` assertions, with the
    flipped value relation and the exception postcondition of `c` equal to
    `ExceptConds.true` (partial correctness). -/
theorem rcompOk_iff_rrel [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {c : M α} {c' : N α'} :
    RCompOk R c c' ↔
      RRel (AssnRel.purify ps) (fun _ E => E = ExceptConds.true) (fun a' a => R a a') c' c := by
  constructor
  · rintro h Q' Q E' E hQ rfl
    refine SPred.pure_elim' fun hwp => ?_
    refine (h (fun a' => (Q' a').down) (fun _ => hwp)).trans
      ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
    exact SPred.pure_elim' fun ⟨a', hr, hq⟩ => (SPred.pure_intro hq).trans (hQ a' a hr)
  · intro h Q' hQ'
    exact (SPred.pure_intro (hQ' True.intro)).trans
      (h (fun a' => ⌜Q' a'⌝) (fun a => ⌜∃ a', R a a' ∧ Q' a'⌝) ExceptConds.false
        ExceptConds.true
        (fun a' a hr => SPred.pure_mono fun hq => ⟨a', hr, hq⟩) rfl)

/-! ## Transport and composition -/

/-- A triple `⦃P⦄ c ⦃(Q, E)⦄` transports along `RRel γ RE R c c'` to the triple
    `⦃γ P⦄ c' ⦃(Q', E')⦄`, for postconditions related by `R` up to `γ` and
    exception postconditions related by `RE`. -/
theorem RRel.transport [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {c : M α} {c' : N α'} (h : RRel γ RE R c c')
    {P : Assertion ps} {Q : α → Assertion ps} {E : ExceptConds ps}
    {Q' : α' → Assertion ps'} {E' : ExceptConds ps'}
    (hQ : ∀ a a', R a a' → γ.γ (Q a) ⊢ₛ Q' a') (hE : RE E E')
    (ht : ⦃P⦄ c ⦃(Q, E)⦄) : ⦃γ.γ P⦄ c' ⦃(Q', E')⦄ :=
  Triple.iff.mpr ((γ.mono (Triple.iff.mp ht)).trans (h Q Q' E E' hQ hE))

/-- `RRel` composes: from `RRel γ₁ RE₁ R₁ c c'` and `RRel γ₂ RE₂ R₂ c' c''` follows
    `RRel (γ₂ ∘ γ₁) (RE₁ ; RE₂) (R₁ ; R₂) c c''`, where `;` is relational
    composition through an intermediate value or exception postcondition. The
    value relations are arbitrary relations. -/
theorem RRel.trans [WP M ps] [WP N ps'] [WP K ps''] {γ₁ : AssnRel ps ps'}
    {γ₂ : AssnRel ps' ps''}
    {RE₁ : ExceptConds ps → ExceptConds ps' → Prop}
    {RE₂ : ExceptConds ps' → ExceptConds ps'' → Prop}
    {R₁ : α → α' → Prop} {R₂ : α' → α'' → Prop}
    {c : M α} {c' : N α'} {c'' : K α''}
    (h₁ : RRel γ₁ RE₁ R₁ c c') (h₂ : RRel γ₂ RE₂ R₂ c' c'') :
    RRel (γ₂.comp γ₁) (fun E E'' => ∃ E', RE₁ E E' ∧ RE₂ E' E'')
      (fun a a'' => ∃ a', R₁ a a' ∧ R₂ a' a'') c c'' := by
  rintro Q Q'' E E'' hQ ⟨E', hE₁, hE₂⟩
  refine (γ₂.mono (h₁ Q (fun b => spred(∃ p : {a // R₁ a b}, γ₁.γ (Q p.1))) E E'
    (fun a b hab => SPred.exists_intro' ⟨a, hab⟩ .rfl) hE₁)).trans
    (h₂ _ Q'' E' E'' (fun b a'' hb => ?_) hE₂)
  exact (γ₂.exists_le _).trans (SPred.exists_elim fun p => hQ p.1 a'' ⟨b, p.2, hb⟩)

/-! ## Rules for the monad operations -/

/-- Related values give `RRel`-related `pure` computations. -/
theorem RRel.pure [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    (RE : ExceptConds ps → ExceptConds ps' → Prop) (R : α → α' → Prop)
    {a : α} {a' : α'} (h : R a a') :
    RRel (M := M) (N := N) γ RE R (Pure.pure a) (Pure.pure a') := by
  intro Q Q' E E' hQ _
  simp only [WPMonad.wp_pure, PredTrans.apply_Pure_pure]
  exact hQ a a' h

/-- Related heads and pointwise related continuations give related sequential
    compositions. -/
theorem RRel.bind [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {Rα : α → α' → Prop}
    {Rβ : β → β' → Prop}
    {c : M α} {c' : N α'} {f : α → M β} {f' : α' → N β'}
    (hc : RRel γ RE Rα c c') (hf : ∀ a a', Rα a a' → RRel γ RE Rβ (f a) (f' a')) :
    RRel γ RE Rβ (c >>= f) (c' >>= f') := by
  intro Q Q' E E' hQ hE
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  exact hc (fun a => wp⟦f a⟧ (Q, E)) (fun a' => wp⟦f' a'⟧ (Q', E')) E E'
    (fun a a' h => hf a a' h Q Q' E E' hQ hE) hE

/-- Conditionals with equivalent conditions and branchwise related arms are
    related. -/
theorem RRel.ite [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {b b' : Prop} [Decidable b] [Decidable b'] (hb : b ↔ b')
    {t e : M α} {t' e' : N α'} (ht : RRel γ RE R t t') (he : RRel γ RE R e e') :
    RRel γ RE R (if b then t else e) (if b' then t' else e') := by
  by_cases h : b
  · rw [if_pos h, if_pos (hb.mp h)]; exact ht
  · rw [if_neg h, if_neg (mt hb.mpr h)]; exact he

/-- `forIn` over `List.Forall₂`-related lists, with a body that maps related
    elements and related accumulators to `RForInStep`-related steps. -/
theorem RRel.forIn_list [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps']
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    {A : Type y} {A' : Type z} (RA : A → A' → Prop) (Rβ : β → β' → Prop)
    (body : A → β → M (ForInStep β)) (body' : A' → β' → N (ForInStep β'))
    (hbody : ∀ a a' b b', RA a a' → Rβ b b' →
      RRel γ RE (RForInStep Rβ) (body a b) (body' a' b'))
    {l : List A} {l' : List A'} (hl : List.Forall₂ RA l l')
    {init : β} {init' : β'} (hinit : Rβ init init') :
    RRel γ RE Rβ (forIn l init body) (forIn l' init' body') := by
  induction hl generalizing init init' with
  | nil => simpa only [List.forIn_nil] using RRel.pure (M := M) (N := N) (γ := γ) RE Rβ hinit
  | cons hx _ ih =>
    simp only [List.forIn_cons]
    refine RRel.bind (hbody _ _ _ _ hx hinit) (fun s s' hs => ?_)
    match s, s', hs with
    | .yield b, .yield b', hb => exact ih hb
    | .done b,  .done b',  hb => exact RRel.pure RE Rβ hb

/-! ## Closed form -/

/-- `RRel` holds exactly when it holds at the strongest postcondition of `c'`
    related to `Q`, namely `fun a' => ∃ a, ⌜R a a'⌝ ∧ γ (Q a)`. This is the
    refinement weakest precondition `rwp` of S. Graf's `sgraf812/ascent`, at the
    top element. -/
theorem RRel.closed_form [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {c : M α} {c' : N α'} :
    RRel γ RE R c c' ↔
      ∀ (Q : α → Assertion ps) (E : ExceptConds ps) (E' : ExceptConds ps'),
        RE E E' → γ.γ (wp⟦c⟧ (Q, E)) ⊢ₛ
          wp⟦c'⟧ (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (Q a)), E') := by
  constructor
  · intro h Q E E' hE
    exact h Q _ E E'
      (fun a a' hr => SPred.exists_intro' a (SPred.and_intro (SPred.pure_intro hr) .rfl)) hE
  · intro h Q Q' E E' hQ hE
    exact (h Q E E' hE).trans ((wp c').mono _ _
      ⟨fun a' => SPred.exists_elim fun a => SPred.pure_elim_l fun hr => hQ a a' hr,
        ExceptConds.entails.refl E'⟩)

end RRel

end Transfer.Param

end
