/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Integrations.ParamTripleTransfer
import Transfer.Combinators.ParamArray

/-!
# `forIn` / `do`-loop transfer: `foldlR` meets `RComp`

`ParamArray.foldlR` transfers a *pure* fold across related containers. Real hex
loops (`HexBareiss`, `HexLLL`) are `do`/`for` loops — effectful, with early exit.
Lean desugars `for x in xs do …` to `forIn`, so this module lifts the fold
transfer to `forIn`, combining `ParamArray`'s container relation with
`Integrations/ParamTripleTransfer`'s Kleisli relation `RComp`.

The result `RComp.forIn_list` is exactly `foldlR` extended along two axes:

* **effects** — the body runs in an arbitrary `WPMonad`, so the transfer is at
  the `wp`-refinement level (`RComp`), not plain equality;
* **early exit** — the body returns a `ForInStep`, and `RForInStep` relates
  `yield`/`done` constructor-wise (a `done` on one side must meet a `done` on the
  other), so the loop transfers even when it breaks early.

A pure, yield-only `forIn` is a `foldl`, so `foldlR` is the special case of this
lemma at `M = Id` with no `done`. Together with `ParamArray.foldlR` (structural
folds) and `RComp.pure`/`RComp.bind` (straight-line effects), this closes the
combinator set a fold-or-loop-shaped hex algorithm needs to transfer without any
recursor translation.
-/

set_option autoImplicit false

open Std.Do

universe u v w

namespace Transfer.Param

/-! ## The relation on `ForInStep` -/

/-- The constructor-wise lift of a value relation to `ForInStep`: `yield`/`done`
    are related only to the same constructor, carrying the value relation
    (the `ForInStep` analogue of `R_option`). A `done` on one side cannot be
    related to a `yield` on the other, so an early exit must be matched. -/
def RForInStep {β : Type u} {β' : Type u} (Rβ : β → β' → Prop) :
    ForInStep β → ForInStep β' → Prop
  | .yield b, .yield b' => Rβ b b'
  | .done b,  .done b'  => Rβ b b'
  | _,        _         => False

/-! ## `forIn` transfer over a `List` -/

/-- **`forIn` transfer.** For a loop body that maps related elements and related
    accumulators to `RForInStep`-related steps (in the `wp`-refinement sense),
    folding it with `forIn` over `List.Forall₂`-related lists from related
    initial accumulators yields `RComp`-related computations. Proved by induction
    on the `Forall₂` derivation, `RComp.bind`-ing the body step against the
    continuation, which the `RForInStep` relation splits into the `yield`
    (recurse) and `done` (`pure`) cases. -/
theorem RComp.forIn_list {M : Type u → Type v} {ps : PostShape.{u}}
    [Monad M] [WPMonad M ps] {A : Type u} {A' : Type u} {β : Type u} {β' : Type u}
    (RA : A → A' → Prop) (Rβ : β → β' → Prop)
    (body : A → β → M (ForInStep β)) (body' : A' → β' → M (ForInStep β'))
    (hbody : ∀ a a' b b', RA a a' → Rβ b b' →
      RComp (ps := ps) (RForInStep Rβ) (body a b) (body' a' b'))
    {l : List A} {l' : List A'} (hl : List.Forall₂ RA l l')
    {init : β} {init' : β'} (hinit : Rβ init init') :
    RComp (ps := ps) Rβ (forIn l init body) (forIn l' init' body') := by
  induction hl generalizing init init' with
  | nil => simpa only [List.forIn_nil] using RComp.pure Rβ hinit
  | cons hx _ ih =>
    simp only [List.forIn_cons]
    refine RComp.bind (hbody _ _ _ _ hx hinit) (fun s s' hs => ?_)
    match s, s', hs with
    | .yield b, .yield b', hb => exact ih hb
    | .done b,  .done b',  hb => exact RComp.pure Rβ hb

/-! ## Demo: a `do`-loop transfers in `Id`

A `for`-loop summation over related lists, transferred by the engine. The body is
`yield`-only, so this is the effectful/early-exit generalisation of `foldlR`
specialised back to a pure accumulation. -/

/-- `forIn`-based summation transfers across `Eq`-related lists: the two loops are
    `RComp`-related, hence equal-valued, from `RComp.forIn_list` alone. The body
    relatedness is `RComp.pure` on the `yield` step. -/
example (l : List Nat) (l' : List Nat) (h : List.Forall₂ (· = ·) l l') :
    RComp (M := Id) (· = ·)
      (forIn l 0 (fun x acc => pure (.yield (acc + x))))
      (forIn l' 0 (fun x acc => pure (.yield (acc + x)))) :=
  RComp.forIn_list (· = ·) (· = ·) _ _
    (fun a a' b b' ha hb => RComp.pure (RForInStep _) (by
      show RForInStep _ (.yield (b + a)) (.yield (b' + a'))
      show b + a = b' + a'
      rw [ha, hb])) h rfl

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.RComp.forIn_list' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RComp.forIn_list

end AxiomAudit

end Transfer.Param
