/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Related
import Transfer.Translate.ParamTranslate

/-!
# One witness, both engines — `RelatedBinOp` ⇒ `RArrow`

The two relatedness engines register a realized binary operation under two
different keys: the `Related` engine takes a `RelatedBinOp enc op bop` square
(`Base/Related.lean`, consumed by `rcongr`/`param_cc`/`param_solve`), the `Param`
engine takes a curried `RArrow` witness (`Translate/ParamTranslate.lean`, consumed
by the term translator `⟦·⟧` and registered with `@[param]`). They carry the *same
content*: over the encoding graph `R a b := enc a = b`, the square
`enc (op a b) = bop (enc a) (enc b)` unfolds to
`∀ a a', R a a' → ∀ b b', R b b' → R (op a b) (bop a' b')`, which is exactly
`RArrow R (RArrow R R) op bop`.

This file makes that a **single source of truth**: register the `RelatedBinOp`
square once, and derive the `Param`-engine witness from it with no second proof.
It is the `RelatedBinOp` companion of `ParamNormCast.paramWitOfCastHom` (which does
the same for a `@[norm_cast]` move lemma), closing the loop so a realized operation
is proved once and consumed by every tactic surface.
-/

set_option autoImplicit false

namespace Transfer.Param

/-- The encoding graph of `enc` as a bare-`Prop` relation. -/
abbrev encRel {A α : Type} (enc : A → α) : A → α → Prop := fun a b => enc a = b

/-- **Single source of truth.** A `RelatedBinOp enc op bop` square *is* the curried
    `Param` binary witness `RArrow (encRel enc) (RArrow (encRel enc) (encRel enc)) op bop`.
    Register the square once (for the `Related` engine); this derives the `Param`-engine
    witness — no re-proof. The `@[param]`-registered form is a one-line
    `:= paramWitnessOfRelatedBinOp enc op bop`. -/
theorem paramWitnessOfRelatedBinOp {A α : Type} (enc : A → α)
    (op : A → A → A) (bop : α → α → α) [h : Transfer.RelatedBinOp enc op bop] :
    RArrow (encRel enc) (RArrow (encRel enc) (encRel enc)) op bop :=
  fun a a' (ha : enc a = a') b b' (hb : enc b = b') => (h.comm a b).trans (by rw [ha, hb])

end Transfer.Param
