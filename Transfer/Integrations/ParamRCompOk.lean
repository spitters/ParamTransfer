/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: ParamTransfer Contributors
-/
module

public import Transfer.Integrations.ParamRComp

/-!
# `RCompOk`: the success-restricted Kleisli relation

`RComp` (`Integrations/ParamTripleTransfer.lean`) relates two computations in one
monad by `wp`-refinement with a shared failure barrel. This module relates a
computation `c : M α` in a monad whose `Std.Do` postcondition shape may carry
exception components (a model that fails, for example on arithmetic overflow or an
out-of-range index) to a computation `c' : N α'` in a monad of shape `.pure`
(a total model, for example `Id`):

  `RCompOk Rα c c' := ∀ Q', (⊢ₛ wp⟦c'⟧ (⇓ a' => ⌜Q' a'⌝)) →`
  `                    ⊢ₛ wp⟦c⟧ (⇓? a => ⌜∃ a', Rα a a' ∧ Q' a'⌝)`

Every postcondition that `c'` establishes is established, up to `Rα`, by every
successful execution of `c`; a failing execution of `c` is unconstrained. At
`N = Id` this is the statement "if `c` returns `a`, then `Rα a c'.run`"
(`RCompOk.id_iff`). The relation is stated through `wp` for `M` only, so it
applies to any `M` with a `WPMonad` instance.

## Rules

* `RCompOk.pure`, `RCompOk.bind` — the Kleisli rules; `bind` composes;
* `RCompOk.mono` — weakening of the value relation;
* `RCompOk.ite`, `RCompOk.dite` — conditionals on both sides, with equivalent
  conditions; `RCompOk.ite_left`, `RCompOk.dite_left` — a conditional on the
  `M` side only (a runtime check with no counterpart in `N`);
* `RCompOk.bind_left` — a computation on the `M` side only, described by a
  partial-correctness postcondition;
* `RCompOk.of_wp_false` — a computation that never succeeds relates to anything;
* `RCompOk.forIn_list`, `RCompOk.forIn_range`, `RCompOk.forIn_rco` — `for`
  loops over `List.Forall₂`-related lists, over `[a:b]` and over `a...b`, with
  early exit through `RForInStep`.

## Transfer

`RCompOk.transfer` moves a total-correctness fact about `c'` to a
partial-correctness fact about `c`: if every result of `c'` satisfies `Q'`, and
`Rα a a' → Q' a' → Q a`, then every successful result of `c` satisfies `Q`.
`RCompOk.triple_transfer` is the same statement in `Std.Do` triple notation. The
converse direction does not hold: a computation that always fails is
`RCompOk`-related to every `c'` and satisfies every partial-correctness
postcondition (`Examples/RCompOkExamples.lean`, `transfer_reverse_false`).

## Containers

`ArrayRel R` is the pointwise relation on arrays, `List.Forall₂ R` on the
underlying lists (the relation `R_array` of `Combinators/ParamArray.lean` is
`ArrayRel` at a `Param` relation, `R_array_eq_arrayRel`). `ArrayRel.iff_getElem`
states it by size and index; `ArrayRel.ofFn_iff` states agreement of an array with
an indexed family `Fin n → α`.

## The `rcomp_ok` tactic

`rcomp_ok` walks both programs of an `RCompOk` goal and applies the rule matching
the head of the `M` side, leaving the value-relation leaves as goals. See
`rcompOkCore`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

namespace Transfer.Param

open Std.Do

/-- The success-restricted Kleisli lift of a value relation. `RCompOk Rα c c'`
    holds when every postcondition `Q'` that the total computation `c'`
    establishes is established, up to `Rα`, by every successful execution of
    `c`: each value `a` that `c` returns without an exception has a partner
    `a'` with `Rα a a'` and `Q' a'`. The monad `N` has postcondition shape
    `.pure`, so `wp⟦c'⟧ (⇓ a' => ⌜Q' a'⌝)` states that every result of `c'`
    satisfies `Q'`. -/
def RCompOk {M : Type u → Type v} {ps : PostShape.{u}} [WP M ps]
    {N : Type u → Type w} [WP N .pure]
    {α α' : Type u} (Rα : α → α' → Prop) (c : M α) (c' : N α') : Prop :=
  ∀ Q' : α' → Prop, (⊢ₛ wp⟦c'⟧ (⇓ a' => ⌜Q' a'⌝)) →
    ⊢ₛ wp⟦c⟧ (⇓? a => ⌜∃ a', Rα a a' ∧ Q' a'⌝)

/-- `pure` rule: related values give related `pure` computations. -/
theorem RCompOk.pure {M : Type u → Type v} {ps : PostShape.{u}} [Monad M] [WPMonad M ps]
    {N : Type u → Type w} [Monad N] [WPMonad N .pure]
    {α α' : Type u} (Rα : α → α' → Prop) {a : α} {a' : α'} (h : Rα a a') :
    RCompOk (M := M) (N := N) Rα (Pure.pure a) (Pure.pure a') := by
  intro Q' hQ
  simp only [WPMonad.wp_pure, PredTrans.apply_Pure_pure] at hQ ⊢
  exact SPred.pure_intro ⟨a', h, by simpa using hQ⟩

/-- `bind` rule: related heads and pointwise related continuations give related
    sequential compositions. The intermediate relation `Rα` is arbitrary. -/
theorem RCompOk.bind {M : Type u → Type v} {ps : PostShape.{u}} [Monad M] [WPMonad M ps]
    {N : Type u → Type w} [Monad N] [WPMonad N .pure]
    {α α' β β' : Type u} {Rα : α → α' → Prop} {Rβ : β → β' → Prop}
    {c : M α} {c' : N α'} {f : α → M β} {f' : α' → N β'}
    (hc : RCompOk Rα c c') (hf : ∀ a a', Rα a a' → RCompOk Rβ (f a) (f' a')) :
    RCompOk Rβ (c >>= f) (c' >>= f') := by
  intro Q' hQ
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind] at hQ ⊢
  have h1 := hc (fun a' => ⊢ₛ wp⟦f' a'⟧ (⇓ b' => ⌜Q' b'⌝)) (by
    refine hQ.trans ((wp c').mono _ _ ⟨fun a' => ?_, ExceptConds.entails.refl _⟩)
    exact fun h _ => h)
  refine h1.trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
  exact SPred.pure_elim' fun ⟨a', hr, hp⟩ => hf a a' hr Q' hp

section Rules

variable {M : Type u → Type v} {ps : PostShape.{u}} {N : Type u → Type w}
  {α α' β β' : Type u}

/-- Weakening: `RCompOk` is monotone in the value relation. -/
theorem RCompOk.mono [WP M ps] [WP N .pure] {R S : α → α' → Prop}
    (hRS : ∀ a a', R a a' → S a a') {c : M α} {c' : N α'} (h : RCompOk R c c') :
    RCompOk S c c' := by
  intro Q' hQ
  refine (h Q' hQ).trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
  exact SPred.pure_elim' fun ⟨a', hr, hq⟩ => SPred.pure_intro ⟨a', hRS a a' hr, hq⟩

/-- A computation with no successful execution (its partial-correctness `wp` at
    the postcondition `False` holds) is `RCompOk`-related to every `c'`. -/
theorem RCompOk.of_wp_false [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {c : M α} (c' : N α') (h : ⊢ₛ wp⟦c⟧ (⇓? _ => ⌜False⌝)) : RCompOk R c c' := by
  intro Q' _
  refine h.trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
  exact SPred.pure_elim' False.elim

/-- One-sided `bind`: a computation `c` on the `M` side with no counterpart on the
    `N` side, whose successful results satisfy `P`, followed by continuations each
    related to `c'`. -/
theorem RCompOk.bind_left [Monad M] [WPMonad M ps] [WP N .pure] {R : β → α' → Prop}
    {c : M α} {f : α → M β} {c' : N α'} (P : α → Prop)
    (hc : ⊢ₛ wp⟦c⟧ (⇓? a => ⌜P a⌝)) (hf : ∀ a, P a → RCompOk R (f a) c') :
    RCompOk R (c >>= f) c' := by
  intro Q' hQ
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  refine hc.trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
  exact SPred.pure_elim' fun hp => hf a hp Q' hQ

/-- `ite` rule: conditionals with equivalent conditions and branchwise related
    arms are related. -/
theorem RCompOk.ite [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {b b' : Prop} [Decidable b] [Decidable b'] (hb : b ↔ b')
    {t e : M α} {t' e' : N α'} (ht : RCompOk R t t') (he : RCompOk R e e') :
    RCompOk R (if b then t else e) (if b' then t' else e') := by
  by_cases h : b
  · simpa [h, hb.mp h] using ht
  · simpa [h, mt hb.mpr h] using he

/-- `dite` rule: dependent conditionals with equivalent conditions and branchwise
    related arms are related. -/
theorem RCompOk.dite [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {b b' : Prop} [Decidable b] [Decidable b'] (hb : b ↔ b')
    {t : b → M α} {e : ¬ b → M α} {t' : b' → N α'} {e' : ¬ b' → N α'}
    (ht : ∀ h h', RCompOk R (t h) (t' h')) (he : ∀ h h', RCompOk R (e h) (e' h')) :
    RCompOk R (if h : b then t h else e h) (if h' : b' then t' h' else e' h') := by
  by_cases h : b
  · simpa [h, hb.mp h] using ht h (hb.mp h)
  · simpa [h, mt hb.mpr h] using he h (mt hb.mpr h)

/-- One-sided `ite`: a conditional on the `M` side whose arms are each related to
    `c'` under the corresponding case hypothesis. -/
theorem RCompOk.ite_left [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {b : Prop} [Decidable b] {t e : M α} {c' : N α'}
    (ht : b → RCompOk R t c') (he : ¬ b → RCompOk R e c') :
    RCompOk R (if b then t else e) c' := by
  by_cases h : b
  · simpa [h] using ht h
  · simpa [h] using he h

/-- One-sided `dite`: a dependent conditional on the `M` side whose arms are each
    related to `c'`. -/
theorem RCompOk.dite_left [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {b : Prop} [Decidable b] {t : b → M α} {e : ¬ b → M α} {c' : N α'}
    (ht : ∀ h, RCompOk R (t h) c') (he : ∀ h, RCompOk R (e h) c') :
    RCompOk R (if h : b then t h else e h) c' := by
  by_cases h : b
  · simpa [h] using ht h
  · simpa [h] using he h

/-- `forIn` rule over lists: a loop body mapping related elements and related
    accumulators to `RForInStep`-related steps, folded over `List.Forall₂`-related
    lists from related initial accumulators, gives related loops. A `done` step
    must meet a `done` step, so early exit is matched. -/
theorem RCompOk.forIn_list [Monad M] [WPMonad M ps] [Monad N] [WPMonad N .pure]
    {A : Type x} {A' : Type y} (RA : A → A' → Prop) (Rβ : β → β' → Prop)
    (body : A → β → M (ForInStep β)) (body' : A' → β' → N (ForInStep β'))
    (hbody : ∀ a a' b b', RA a a' → Rβ b b' →
      RCompOk (RForInStep Rβ) (body a b) (body' a' b'))
    {l : List A} {l' : List A'} (hl : List.Forall₂ RA l l')
    {init : β} {init' : β'} (hinit : Rβ init init') :
    RCompOk Rβ (forIn l init body) (forIn l' init' body') := by
  induction hl generalizing init init' with
  | nil => simpa only [List.forIn_nil] using RCompOk.pure (M := M) (N := N) Rβ hinit
  | cons hx _ ih =>
    simp only [List.forIn_cons]
    refine RCompOk.bind (hbody _ _ _ _ hx hinit) (fun s s' hs => ?_)
    match s, s', hs with
    | .yield b, .yield b', hb => exact ih hb
    | .done b,  .done b',  hb => exact RCompOk.pure Rβ hb

/-- `forIn` rule over a range `[a:b]` (`Std.Legacy.Range`) iterated on both sides,
    with the same index passed to both bodies. -/
theorem RCompOk.forIn_range [Monad M] [WPMonad M ps] [Monad N] [WPMonad N .pure]
    (Rβ : β → β' → Prop) (r : Std.Legacy.Range)
    (body : Nat → β → M (ForInStep β)) (body' : Nat → β' → N (ForInStep β'))
    (hbody : ∀ i b b', Rβ b b' → RCompOk (RForInStep Rβ) (body i b) (body' i b'))
    {init : β} {init' : β'} (hinit : Rβ init init') :
    RCompOk Rβ (forIn r init body) (forIn r init' body') := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  exact RCompOk.forIn_list (· = ·) Rβ body body' (fun i _ b b' h hb => h ▸ hbody i b b' hb)
    (List.forall₂_same.mpr fun _ _ => rfl) hinit

end Rules

/-- `forIn` rule over a half-open range `a...b` (`Std.Rco Nat`) iterated on both
    sides, with the same index passed to both bodies. The range's `ForIn`
    instance places the accumulator in `Type`. -/
theorem RCompOk.forIn_rco {M N : Type → Type} {ps : PostShape.{0}}
    [Monad M] [WPMonad M ps] [Monad N] [WPMonad N .pure] {β β' : Type}
    (Rβ : β → β' → Prop) (r : Std.Rco Nat)
    (body : Nat → β → M (ForInStep β)) (body' : Nat → β' → N (ForInStep β'))
    (hbody : ∀ i b b', Rβ b b' → RCompOk (RForInStep Rβ) (body i b) (body' i b'))
    {init : β} {init' : β'} (hinit : Rβ init init') :
    RCompOk Rβ (forIn r init body) (forIn r init' body') := by
  simp only [forIn, Std.Rco.forIn'_eq_forIn'_toList]
  exact RCompOk.forIn_list (· = ·) Rβ body body' (fun i _ b b' h hb => h ▸ hbody i b b' hb)
    (List.forall₂_same.mpr fun _ _ => rfl) hinit

section Transfer

variable {M : Type u → Type v} {ps : PostShape.{u}} {N : Type u → Type w}
  {α α' : Type u}

/-- Transfer from the total side to the successful executions of the partial side.
    If every result of `c'` satisfies `Q'` and `R a a' → Q' a' → Q a`, then every
    result that `c` returns without an exception satisfies `Q`. The converse
    direction, from a partial-correctness fact about `c` to a fact about `c'`,
    does not hold, since a `c` that always fails is related to every `c'`. -/
theorem RCompOk.transfer [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {c : M α} {c' : N α'} (h : RCompOk R c c')
    {Q : α → Prop} {Q' : α' → Prop} (hQ : ∀ a a', R a a' → Q' a' → Q a)
    (ht : ⊢ₛ wp⟦c'⟧ (⇓ a' => ⌜Q' a'⌝)) :
    ⊢ₛ wp⟦c⟧ (⇓? a => ⌜Q a⌝) := by
  refine (h Q' ht).trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
  exact SPred.pure_elim' fun ⟨a', hr, hq⟩ => SPred.pure_intro (hQ a a' hr hq)

/-- `RCompOk.transfer` in triple notation: a total-correctness triple for `c'`
    gives a partial-correctness triple for `c` under any precondition. -/
theorem RCompOk.triple_transfer [WP M ps] [WP N .pure] {R : α → α' → Prop}
    {c : M α} {c' : N α'} (h : RCompOk R c c')
    {Q : α → Prop} {Q' : α' → Prop} (hQ : ∀ a a', R a a' → Q' a' → Q a)
    (P : Assertion ps) (ht : ⦃⌜True⌝⦄ c' ⦃⇓ a' => ⌜Q' a'⌝⦄) :
    ⦃P⦄ c ⦃⇓? a => ⌜Q a⌝⦄ :=
  SPred.true_intro.trans (h.transfer hQ ht)

/-- At `N = Id`, `RCompOk R c c'` states that every successful result of `c` is
    `R`-related to `c'.run`. -/
theorem RCompOk.id_iff [WP M ps] {R : α → α' → Prop} {c : M α} {c' : Id α'} :
    RCompOk R c c' ↔ ⊢ₛ wp⟦c⟧ (⇓? a => ⌜R a c'.run⌝) := by
  constructor
  · intro h
    refine (h (· = c'.run) ?_).trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
    · exact SPred.pure_intro rfl
    · exact SPred.pure_elim' fun ⟨a', hr, hq⟩ => SPred.pure_intro (hq ▸ hr)
  · intro h Q' hQ
    have hq : Q' c'.run := hQ True.intro
    refine h.trans ((wp c).mono _ _ ⟨fun a => ?_, ExceptConds.entails.refl _⟩)
    exact SPred.pure_elim' fun hr => SPred.pure_intro ⟨_, hr, hq⟩

end Transfer

section ArrayRel

variable {α : Type x} {β : Type y}

/-- The pointwise relation on arrays: `a` and `b` have the same size and
    corresponding entries are `R`-related, stated as `List.Forall₂ R` on the
    underlying lists. -/
def ArrayRel (R : α → β → Prop) (a : Array α) (b : Array β) : Prop :=
  List.Forall₂ R a.toList b.toList

/-- The `Param` array relation `R_array PA` is `ArrayRel` at the relation of `PA`. -/
theorem R_array_eq_arrayRel {mA nA : MapClass} {A A' : Type u} (PA : Param mA nA A A') :
    R_array PA = ArrayRel PA.R := rfl

/-- `ArrayRel` by size and index. -/
theorem ArrayRel.iff_getElem {R : α → β → Prop} {a : Array α} {b : Array β} :
    ArrayRel R a b ↔
      a.size = b.size ∧ ∀ (i : Nat) (h : i < a.size) (h' : i < b.size), R a[i] b[i] := by
  simp [ArrayRel, List.forall₂_iff_get]

/-- Related arrays have equal size. -/
theorem ArrayRel.size_eq {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ArrayRel R a b) : a.size = b.size :=
  (ArrayRel.iff_getElem.mp h).1

/-- Entries of related arrays at the same in-range index are related. -/
theorem ArrayRel.getElem {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ArrayRel R a b) (i : Nat) (hi : i < a.size) (hi' : i < b.size) : R a[i] b[i] :=
  (ArrayRel.iff_getElem.mp h).2 i hi hi'

/-- Pushing related entries onto related arrays gives related arrays. -/
theorem ArrayRel.push {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ArrayRel R a b) {x : α} {y : β} (hxy : R x y) :
    ArrayRel R (a.push x) (b.push y) := by
  simpa [ArrayRel] using List.rel_append h (List.Forall₂.cons hxy .nil)

/-- Writing related entries at the same in-range index of related arrays gives
    related arrays. -/
theorem ArrayRel.set {R : α → β → Prop} {a : Array α} {b : Array β}
    (h : ArrayRel R a b) (i : Nat) (hi : i < a.size) (hi' : i < b.size)
    {x : α} {y : β} (hxy : R x y) :
    ArrayRel R (a.set i x hi) (b.set i y hi') := by
  rw [ArrayRel.iff_getElem] at h ⊢
  refine ⟨by simpa using h.1, fun j hj hj' => ?_⟩
  simp only [Array.getElem_set]
  split
  · exact hxy
  · exact h.2 j (by simpa using hj) (by simpa using hj')

/-- Agreement of an array with an indexed family: `Array.ofFn f` is related to `b`
    exactly when `b` has size `n` and position `k` of `b` is related to `f k`. -/
theorem ArrayRel.ofFn_iff {R : α → β → Prop} {n : Nat} (f : Fin n → α) (b : Array β) :
    ArrayRel R (Array.ofFn f) b ↔
      b.size = n ∧ ∀ (k : Fin n) (hk : k.val < b.size), R (f k) b[k.val] := by
  rw [ArrayRel.iff_getElem]
  simp only [Array.size_ofFn, Array.getElem_ofFn]
  constructor
  · rintro ⟨hs, h⟩
    exact ⟨hs.symm, fun k hk => h k.val k.isLt hk⟩
  · rintro ⟨hs, h⟩
    exact ⟨hs.symm, fun i hi hi' => h ⟨i, hi⟩ hi'⟩

end ArrayRel

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.RCompOk.forIn_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RCompOk.forIn_list

/-- info: 'Transfer.Param.RCompOk.transfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RCompOk.transfer

end AxiomAudit

end Transfer.Param

end

public meta section

set_option autoImplicit false

namespace Transfer.Param

open Lean Elab Tactic Meta

/-- Introduce every leading binder of the main goal with a fresh name. -/
partial def rcompOkIntros : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.isForall then
    let n := mkIdent (← mkFreshUserName `a)
    evalTactic (← `(tactic| intro $n:ident))
    rcompOkIntros

/-- Structural `RCompOk` descent. On a goal `RCompOk R c c'` (after introducing
    leading binders and `dsimp only`, which removes `have` and β-redexes left by
    `do`-elaboration) it tries, in order:

    1. each supplied lemma, by `exact` and then by `apply`;
    2. by the head of `c`: `Bind.bind` ↦ `RCompOk.bind`, with the intermediate
       relation taken from `userRels`, then from the relations of the enclosing
       goals (innermost first, including `R` of an `RForInStep R` goal), then
       equality; `ite` / `dite` ↦ `RCompOk.ite` / `RCompOk.dite` when `c'` has
       the same head and `RCompOk.ite_left` / `RCompOk.dite_left` otherwise;
       `ForIn.forIn` ↦ `RCompOk.forIn_range`, `RCompOk.forIn_rco`,
       `RCompOk.forIn_list` at equality (same list) or at a relation from
       `userRels`;
    3. otherwise `RCompOk.pure`.

    It recurses into every resulting `RCompOk` goal. Condition equivalences
    `b ↔ b'` are closed by `Iff.rfl` when possible; an `RForInStep R` leaf on two
    `yield` (or two `done`) steps is reduced to `R`. Value-relation leaves and
    goals that match no rule are left to the caller. -/
partial def rcompOkCore (userRels rels : Array Term) (lemmas : Array Term) : TacticM Unit :=
  withMainContext do
  rcompOkIntros
  withMainContext do
  unless (← instantiateMVars (← getMainTarget)).isAppOf ``Transfer.Param.RCompOk do return
  try evalTactic (← `(tactic| dsimp only)) catch _ => pure ()
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let (``Transfer.Param.RCompOk, args) := tgt.getAppFnArgs | return
  let relE := args[7]!
  let goalRel ← Lean.Elab.Term.exprToSyntax relE
  let rels' ← if relE.isAppOfArity ``Transfer.Param.RForInStep 3 then
      pure ((rels.push goalRel).push (← Lean.Elab.Term.exprToSyntax relE.appArg!))
    else pure (rels.push goalRel)
  let c ← instantiateMVars args[8]!
  let c' ← instantiateMVars args[9]!
  let recurse : TacticM Unit := do
    allGoals (withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      if g.isAppOf ``Transfer.Param.RCompOk || g.isForall then rcompOkCore userRels rels' lemmas
      else if g.isAppOf ``Iff then
        try evalTactic (← `(tactic| exact Iff.rfl)) catch _ => pure ()
      else if g.isAppOf ``Transfer.Param.RForInStep then
        try evalTactic (← `(tactic| dsimp only [RForInStep])) catch _ => pure ()
      else pure ())
  for l in lemmas do
    try
      evalTactic (← `(tactic| exact $l))
      return
    catch _ => pure ()
  for l in lemmas do
    try
      evalTactic (← `(tactic| apply $l))
      recurse
      return
    catch _ => pure ()
  let c'Head := c'.getAppFn.constName?
  let steps : Array (TSyntax `tactic) ← match c.getAppFn.constName? with
    | some ``Bind.bind =>
      ((userRels ++ rels'.reverse).push (← `(fun a a' => a = a'))).mapM fun r =>
        `(tactic| refine RCompOk.bind (Rα := $r) ?_ ?_)
    | some ``ite =>
      if c'Head == some ``ite then
        pure #[← `(tactic| refine RCompOk.ite ?_ ?_ ?_),
          ← `(tactic| refine RCompOk.ite_left ?_ ?_)]
      else pure #[← `(tactic| refine RCompOk.ite_left ?_ ?_)]
    | some ``dite =>
      if c'Head == some ``dite then
        pure #[← `(tactic| refine RCompOk.dite ?_ ?_ ?_),
          ← `(tactic| refine RCompOk.dite_left ?_ ?_)]
      else pure #[← `(tactic| refine RCompOk.dite_left ?_ ?_)]
    | some ``ForIn.forIn => do
      let fixed : Array (TSyntax `tactic) := #[
        ← `(tactic| refine RCompOk.forIn_range _ _ _ _ ?_ ?_),
        ← `(tactic| refine RCompOk.forIn_rco _ _ _ _ ?_ ?_),
        ← `(tactic| refine RCompOk.forIn_list (fun a a' => a = a') _ _ _ ?_
            (List.forall₂_same.mpr fun _ _ => rfl) ?_)]
      let viaRel ← userRels.mapM fun r =>
        `(tactic| refine RCompOk.forIn_list $r _ _ _ ?_ ?_ ?_)
      pure (fixed ++ viaRel)
    | _ => pure #[← `(tactic| refine RCompOk.pure _ ?_)]
  for t in steps do
    try
      evalTactic t
      recurse
      return
    catch _ => pure ()

/-- `rcomp_ok` assembles an `RCompOk` witness by structural descent over both
    programs (see `rcompOkCore`) and leaves the value-relation leaves as goals.
    `rcomp_ok using R₁, …, Rₙ` supplies intermediate relations for `bind` and
    `forIn`, tried before the relations of the enclosing goals;
    `rcomp_ok [h₁, …, hₘ]` supplies `RCompOk` lemmas for sub-programs (a called
    function, a failing primitive), tried at each node before the structural
    rules. It fails on a goal that is not `RCompOk _ _ _`. -/
syntax (name := rcompOkTac) "rcomp_ok" (" using " term,+)? (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| rcomp_ok $[using $rels,*]? $[[$lemmas,*]]?) => withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    unless tgt.isAppOf ``Transfer.Param.RCompOk do
      throwError "rcomp_ok: goal is not `RCompOk _ _ _`"
    let rels := (rels.map (·.getElems)).getD #[]
    let lemmas := (lemmas.map (·.getElems)).getD #[]
    rcompOkCore rels #[] lemmas

/-- `param_transfer` runs `rcomp_ok` on an `RCompOk` goal. -/
macro_rules
  | `(tactic| param_transfer) => `(tactic| rcomp_ok)

end Transfer.Param

end
