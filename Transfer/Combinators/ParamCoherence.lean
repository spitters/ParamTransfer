/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Combinators.ParamTrans
import Transfer.Combinators.ParamArrow
import Transfer.Combinators.ParamData

/-!
# The coherence-law suite (functor laws)

The combinators in `ParamTrans`/`ParamArrow`/`ParamData` build annotated
relations; this file proves the coherence laws that govern how they compose.
These are the Lean realizations of the laws of AdapTT (Adjedj, Lennon-Bertrand,
Benjamin, Maillard, *AdapTT: Functoriality for Dependent Type Casts*, POPL 2026):
the cast-adapter identity `AdaptId` and composition `AdaptComp`, plus the
functoriality of each type former over those adapters. AdapTT secures them
*definitionally* via a bespoke cast calculus. In Lean the **cast-form** laws
(`cast_id`/`cast_trans`) hold by `rfl` for free — the composite's forward map is
already function composition, so composition through nested type formers is
automatic and the "stuck adapter" gap Trocq's `stuck.v` documents does not arise;
they need not be *cited*, but they *certify* the functor laws hold, and are used
explicitly where a coercion chain is built by hand (e.g. CatCrypt's dialect-chain
transport). The **relational-form** law (`prod_trans_rel`) is the one proved
propositionally (`funext`/`propext`). The dependent type formers extend the
non-dependent `→`/`×`/`List`/`Option` laws here: `paramForall` (Π,
`ParamForall.lean`) and `paramSigma` (Σ, `ParamSigma.lean`, `sigma_cast_eq` =
`Adapt Σ = Σ Adapt`) carry the same functoriality into the dependent world.

## Contents

1. **Cast-composition (`AdaptComp`/`AdaptId`).** `castViaParam P a := P.fwd.map a`
   is the representation-change coercion. `cast_trans` and `cast_id` are the two
   coherence laws that make coercion chains correct; both hold by `rfl`
   because `Param_trans`'s forward map is `Q.map ∘ P.map` and
   `paramId`'s is `id`.

2. **Combinator distributes over composition (the functor law), forward-map /
   `cast` form.** For each container/type-former combinator, the forward
   map of "compose then combine" equals "combine then compose" — the
   `cast`/forward-map version of the functor law (`prod`, `option`, `list`,
   `arrow`). For `arrow` this is contravariant in the domain.

3. **Combinator-distributes, full relational form.** Proved for `prod` (the
   relation of the composite equals the composite of the relations) via
   `funext`/`propext`. `arrow`/`sum`/`option`/`list` relational forms are noted
   where they need more than the cast form.

4. **Identity laws (`cast` form).** `prod_id`/`arrow_id`: a combinator applied
   to identity `Param`s acts as the identity coercion.

All laws are univalence-free: they live entirely in the `map1`–`map3` forward
fragment, exactly the fragment `ParamHierarchy`'s module docstring marks as
axiom-free in Lean (`funext` is a theorem; only the `map4` *universe* relation
needs univalence).
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A B C : Type u}

/-! ## 1. Cast-composition: AdapTT `AdaptId` / `AdaptComp` -/

/-- The identity annotated relation on `T`: relation `Eq`, both maps `id`,
    full `map3` in both directions. The diagonal `Param`. (Same data as
    `paramEqFull`; named `paramId` to flag its role as the unit of the
    composition `Param_trans`.) -/
def paramId (T : Type u) : Param .map3 .map3 T T where
  R := Eq
  fwd := ⟨id, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨id, fun _ _ h => h.symm, fun _ _ h => h.symm⟩

/-- The identity annotated relation at the forward/backward-`map1` level — the
    input shape `paramArrow` consumes. Relation `Eq`, both maps `id`. -/
def paramId1 (T : Type u) : Param .map1 .map1 T T where
  R := Eq
  fwd := ⟨id⟩
  bwd := ⟨id⟩

/-- The identity annotated relation at the forward-`map2a`, backward-`map0` level
    — the input shape `paramProd`/`paramOption`/`paramList` consume. Relation
    `Eq`, forward map `id` (its graph is `Eq`). -/
def paramIdElt (T : Type u) : Param .map2a .map0 T T where
  R := Eq
  fwd := ⟨id, fun _ _ h => h⟩
  bwd := ⟨⟩

/-- Representation-change coercion induced by a `Param`: its forward map. The
    forward level is `map3` (the level `paramId` and `Param_trans_map3`
    produce); the backward level stays polymorphic. -/
def castViaParam {n : MapClass} (P : Param .map3 n A B) (a : A) : B :=
  P.fwd.map a

/-- `AdaptComp` — coercion through a composite relation is the composition of
    the two coercions. Holds by `rfl`: `Param_trans_map3`'s forward map is
    `Q.fwd.map ∘ P.fwd.map`. This is the law that makes a coercion
    chain (abstract → bytes → field) correct. -/
theorem cast_trans (P : Param .map3 .map3 A B) (Q : Param .map3 .map3 B C)
    (a : A) :
    castViaParam (Param_trans_map3 P Q) a = castViaParam Q (castViaParam P a) :=
  rfl

/-- `AdaptId` — coercion through the identity relation is the identity. Holds
    by `rfl`: `paramId`'s forward map is `id`. -/
theorem cast_id (a : A) : castViaParam (paramId A) a = a := rfl

/-! ### Composing element `Param`s at the level the data combinators consume

`paramProd`/`paramOption`/`paramList` consume `Param .map2a .map0`. Their
two-step composite is again a `Param .map2a .map0`, built from `Map2a_trans`'s
forward record (the backward direction is `map0`, nothing to compose). This is
the data-rule instance of `Param_trans`. -/

/-- Compose two element `Param`s at the forward-`map2a`, backward-`map0` level —
    the shape the data combinators consume. Forward map is `Q.map ∘ P.map`. -/
def Param_trans_map2a_map0 (P : Param .map2a .map0 A B) (Q : Param .map2a .map0 B C) :
    Param .map2a .map0 A C where
  R := R_trans P Q
  fwd := Map2a_trans P Q
  bwd := ⟨⟩

/-- Its forward map is the function composition (definitional). -/
theorem Param_trans_map2a_map0_map
    (P : Param .map2a .map0 A B) (Q : Param .map2a .map0 B C) (a : A) :
    (Param_trans_map2a_map0 P Q).fwd.map a = Q.fwd.map (P.fwd.map a) := rfl

/-! ## 2. Functor law, `cast` / forward-map form

For each combinator: the forward map of *composing two combinator-built
`Param`s* equals *the combinator applied to the composed argument-`Param`s*.
This is the AdapTT type-former functoriality (`Adapt (F …) = F (Adapt …)`) in
its cast form. The data combinators consume `Param .map2a .map0`; the arrow
combinator consumes `Param .map1 .map1`. The forward maps are function
compositions, so each law is `rfl` (or `cases`+`rfl` / `simp` through the
recursive lift). -/

/-! ### Product (covariant in both arguments) -/

/-- `prod_trans` (cast form). The forward map of the product of two composite
    element relations equals the composite of the two product forward maps:
    `prod_map (Q∘P) = prod_map Q ∘ prod_map P`, componentwise. -/
theorem prod_trans_cast
    (PA : Param .map2a .map0 A B) (QA : Param .map2a .map0 B C)
    (PB : Param .map2a .map0 A B) (QB : Param .map2a .map0 B C)
    (p : A × A) :
    (paramProd (Param_trans_map2a_map0 PA QA) (Param_trans_map2a_map0 PB QB)).fwd.map p
      = (paramProd QA QB).fwd.map ((paramProd PA PB).fwd.map p) :=
  rfl

/-! ### Option / List (covariant) -/

/-- `option_trans` (cast form). `Option.map (Q∘P) = Option.map Q ∘ Option.map P`
    on the lifted relations. -/
theorem option_trans_cast
    (PA : Param .map2a .map0 A B) (QA : Param .map2a .map0 B C)
    (o : Option A) :
    (paramOption (Param_trans_map2a_map0 PA QA)).fwd.map o
      = (paramOption QA).fwd.map ((paramOption PA).fwd.map o) := by
  cases o <;> rfl

/-- `list_trans` (cast form). `List.map (Q∘P) = List.map Q ∘ List.map P` on
    the lifted relations. -/
theorem list_trans_cast
    (PA : Param .map2a .map0 A B) (QA : Param .map2a .map0 B C)
    (l : List A) :
    (paramList (Param_trans_map2a_map0 PA QA)).fwd.map l
      = (paramList QA).fwd.map ((paramList PA).fwd.map l) := by
  simp only [paramList, Param_trans_map2a_map0, Map2a_trans, List.map_map,
    Function.comp_def]

/-! ### Arrow (contravariant in the domain)

`paramArrow PA PB` has forward map `fun f a' => PB.fwd.map (f (PA.bwd.map a'))`.
Composing two arrows, the codomain maps compose forward (`PB`) while the domain
*backward* maps compose in the *reverse* order (`PA`) — the contravariance. The
`Param_trans_map3` of the domain supplies a backward map `P.bwd.map ∘ Q.bwd.map`
(reversed), exactly matching the conjugation order, so the law is `rfl`. -/

/-- `arrow_trans` (cast form). The forward map of the composite of two arrow
    `Param`s equals the arrow combinator applied to the composed domain/codomain
    `Param`s — with the domain composed contravariantly. Both sides send
    `f : A → A` to the conjugation `(QB∘PB) ∘ f ∘ (P_A.bwd ∘ Q_A.bwd)`. -/
theorem arrow_trans_cast
    (PA : Param .map1 .map1 A B) (QA : Param .map1 .map1 B C)
    (PB : Param .map1 .map1 A B) (QB : Param .map1 .map1 B C)
    (f : A → A) (c : C) :
    (paramArrow (Param_trans_map1 PA QA) (Param_trans_map1 PB QB)).fwd.map f c
      = (paramArrow QA QB).fwd.map
          ((paramArrow PA PB).fwd.map f) c :=
  rfl

/-! ## 3. Functor law, full relational form (product) -/

/-- `prod_trans` (relational form). The relation of the product of two
    composite element relations *equals* (as a relation, via `funext`/`propext`)
    the composite of the two product relations. This is the strict functor law
    `R_prod (Q∘P) = (R_prod Q) ∘ (R_prod P)` for the product type former.

    Left side: `(a,b) ~ (c,d)` iff `∃ m, PA.R a m ∧ QA.R m c` and likewise on the
    second component (two independent witnesses). Right side: one shared witness
    pair `(m₁,m₂)`. They agree because the product witness can be split/paired. -/
theorem prod_trans_rel
    (PA : Param .map2a .map0 A B) (QA : Param .map2a .map0 B C)
    (PB : Param .map2a .map0 A B) (QB : Param .map2a .map0 B C) :
    R_prod (Param_trans_map2a_map0 PA QA) (Param_trans_map2a_map0 PB QB)
      = R_trans (paramProd PA PB) (paramProd QA QB) := by
  funext p p'
  apply propext
  constructor
  · rintro ⟨⟨m1, h1, h2⟩, ⟨m2, h3, h4⟩⟩
    exact ⟨(m1, m2), ⟨h1, h3⟩, ⟨h2, h4⟩⟩
  · rintro ⟨⟨m1, m2⟩, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨⟨m1, h1, h2⟩, ⟨m2, h3, h4⟩⟩

/-! ## 4. Identity laws (`cast` form): combinator over `paramId` = identity coercion -/

/-- `prod_id`. The product combinator applied to two identity element
    `Param`s has forward map the identity on the product. -/
theorem prod_id_cast (p : A × A) :
    (paramProd (paramIdElt A) (paramIdElt A)).fwd.map p = p :=
  rfl

/-- `arrow_id`. The arrow combinator applied to identity domain and codomain
    `Param`s has forward map the identity on the function space (up to `funext`):
    conjugating by `id` on both sides is the identity. -/
theorem arrow_id_cast (f : A → A) :
    (paramArrow (paramId1 A) (paramId1 A)).fwd.map f = f :=
  rfl

/-! ## Demos: the coherence laws close, and one combinator law -/

section Demo

/-- `cast_trans` closes (`AdaptComp`): coercion through a composite is the
    composition of coercions, on a concrete chain `ℕ → ℕ → ℕ` via diagonals. -/
example (a : ℕ) :
    castViaParam (Param_trans_map3 (paramId ℕ) (paramId ℕ)) a
      = castViaParam (paramId ℕ) (castViaParam (paramId ℕ) a) :=
  cast_trans _ _ a

/-- `cast_id` closes (`AdaptId`): the identity coercion is the identity. -/
example (a : ℕ) : castViaParam (paramId ℕ) a = a := cast_id a

/-- The product functor law (cast form) closes on the diagonal chain. -/
example (p : ℕ × ℕ) :
    (paramProd (Param_trans_map2a_map0 (paramIdElt ℕ) (paramIdElt ℕ))
        (Param_trans_map2a_map0 (paramIdElt ℕ) (paramIdElt ℕ))).fwd.map p
      = (paramProd (paramIdElt ℕ) (paramIdElt ℕ)).fwd.map
          ((paramProd (paramIdElt ℕ) (paramIdElt ℕ)).fwd.map p) :=
  prod_trans_cast _ _ _ _ p

end Demo

end Transfer.Param
