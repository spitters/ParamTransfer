/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Combinators.ParamData

/-!
# Toward a `@[derive Param]` handler (two more mechanized
inductives + the deriving-handler design)

`ParamData.lean` hand-ported the relational lift for the three representative
inductive shapes Trocq's Elpi generates one file per: binary product, optional,
recursive list. This file does two things.

1. Mechanizes two more inductives by hand, in the exact `ParamData` style —
   the binary sum `R_sum`/`paramSum` (Coq `generic/Param_sum.v`), the
   representative *multi-constructor non-recursive* shape, and the parameter-free
   `Nat` `R_nat`/`paramNat` (Coq's natural-number relation), the
   representative *recursive, parameter-free* shape whose relation collapses to
   equality and whose recursor supports the full `map3`.

2. Specifies the deriving-handler algorithm (the design note below), the
   procedure a `DerivingHandler` would run to emit these files
   automatically — what Trocq's Elpi does in Coq.

Implemented: the two hand-ported inductives (fully proved,
`#print axioms`-clean) plus the design note. The full `DerivingHandler`
elaborator is specified, not implemented.

## Design note — the `@[derive Param]` handler algorithm

Given an `InductiveVal` for a simple inductive `F` with type parameters
`(α₁ … α_k : Type)` (no dependent indices), the handler should:

1. Read the parameters. Take `k` element relations
   `Pᵢ : Param mᵢ nᵢ αᵢ αᵢ'`. The output is `Param ? ? (F α₁ … α_k) (F α₁' … α_k')`.
2. Build the relation `R_F`. For each constructor
   `cⱼ : Πfields. F α…`, emit one clause relating `cⱼ x… ~ cⱼ y…` by the
   *pointwise* lift of the field relations: a field of type `αᵢ` uses `Pᵢ.R`; a
   field of recursive type `F α…` uses `R_F` (the recursive call); a field of a
   previously-derived type `G β…` uses `R_G (…)`. Distinct constructors are
   `False`-related. (This is exactly `prodR`/`optionR`/`listR`/`R_sum` above.)
   Mechanically: `inductive R_F … : F α… → F α'… → Prop` with one constructor
   per `cⱼ`, taking the field-relatedness hypotheses — a `Forall₂`-style
   congruence.
3. Synthesize the forward `map` from the recursor. `F.rec` with motive
   `fun _ => F α'…`, each minor premise applying `cⱼ'` to the
   field-images (`Pᵢ.fwd.map` on element fields, the recursive `map` on
   recursive fields). This is `F.map`/`Sum.map`/`Nat.rec` specialized.
4. `map_in_R` (→ `map2a`) by the recursor / induction. Induct on the source
   value (or `subst` the map equation); for each constructor discharge the
   field-relatednesses from the element `Pᵢ.fwd.map_in_R` and the recursive IH.
   Needs each `Pᵢ` forward-`map2a`.
5. `R_in_map` (→ `map2b`, hence `map3`) by induction on the relation. Induct
   on the `R_F` derivation; each constructor case rewrites by the field
   `Pᵢ.fwd.R_in_map` and the recursive IH. Needs each `Pᵢ` forward-`map2b`.
   Funext-free: inductive fields are data, not function space, so unlike the
   arrow rule no `Funext` gate appears (Lean has `funext` as a theorem anyway).
6. Register. Emit `paramF : Param mapk … (F α…) (F α'…)` and add it to the
   `@[param]` database (`ParamDB.lean`).

Class cap. A non-dependent inductive reaches the same level as its weakest
field input — `map0`–`map3` univalence-free (the `Map4` coherence `R_in_mapK`
is the only residual, as everywhere in the port). A dependent index (an
inductive family `F : I → Type` whose constructors constrain the index, e.g. a
length-indexed `Vector`) caps the derivable class: the index equality must be
transported, and recovering the round-trip coherence there is where the
`map3 → map4` jump needs univalence — precisely the paper's `map0–map2a`
ceiling for the *universe*-touching cases. The handler should detect a
non-trivial index and refuse above `map2a` (or require the user to supply the
coherence).

## Bigger picture — reuse Mathlib's `Translate` framework

Mathlib refactored `to_additive` into a generic term-translation framework
`Mathlib.Tactic.Translate` (`Core.lean`, ~1229 LOC). It is structurally this
engine's `@[param]` + `#transfer` translator but far more mature, and this
engine's `#transfer`/`@[param]` should be re-expressed on top of it rather than
reinvented:

* Its DB is a `NameMapAttribute` (`Batteries.Lean.NameMapAttribute`,
  `Core.lean:16`) mapping `src ↦ TranslationInfo` (`:188`) — exactly this
  engine's `paramExt : NameMap (Name × Name)`, but with `reorder`/`relevantArg`
  metadata. The `paramExt` should become a `NameMapExtension` of a
  `Param`-witness record.
* `applyReplacementFun` (`:440`) is a generic structural term rewriter
  parameterised by the DB; `transformDeclRec` (`:742`) walks a declaration and
  its companions. This engine's `translate` is the same walk — `applyReplacementFun`
  should be *parameterised with the `Param`-witness relation* instead of the
  additive name map (i.e. carry the relatedness proof alongside the replaced
  constant, the one thing `to_additive` does not need).
* `proceedFields` (`:983`) already handles structure projections and
  `isInductive` (`:1198`) special-cases inductive declarations — the exact
  machinery the deriving-handler step (3)–(5) re-implements by hand. Reusing it
  gives projection/inductive translation for free.
* `GuessName.lean` auto-derives the target name from the source; this engine's
  translator demands an explicit `c'`, so `GuessName` would let `@[param]` infer
  the transferred constant's name.

The reuse is: instantiate `Translate`'s `TranslateData`/`Config` with a
`Param`-witness payload, replacing the additive-name substitution with the
relatedness-carrying substitution, and let its `transformDeclRec`/`proceedFields`
do the structural+inductive+projection walk that `ParamTranslate` does by hand.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A A' : Type u}

/-! ## Binary sum: the relation `R_sum` (Coq `generic/Param_sum.v`)

The representative *multi-constructor non-recursive* inductive. Two `Sum` values
are related iff they use the same constructor with related payloads; mixed
constructors are `False`-related — the same shape as `R_option`, generalized to
two non-trivial payloads. -/

variable {B B' : Type u}

/-- Trocq `sumR`: `inl a ~ inl a'` iff `PA.R a a'`; `inr b ~ inr b'` iff
    `PB.R b b'`; mixed constructors unrelated. -/
def R_sum {mA nA mB nB : MapClass}
    (PA : Param mA nA A A') (PB : Param mB nB B B') :
    A ⊕ B → A' ⊕ B' → Prop
  | .inl a, .inl a' => PA.R a a'
  | .inr b, .inr b' => PB.R b b'
  | _,      _       => False

/-- Trocq `Map0_sum`: no structure. -/
def Map0_sum {mA nA mB nB : MapClass}
    (PA : Param mA nA A A') (PB : Param mB nB B B') :
    Map0Has (R_sum PA PB) := ⟨⟩

/-- Trocq `sum_map` as a `map1` record: lift each payload forward map through
    the matching constructor (`Sum.map`). Needs `PA`, `PB` forward-`map1`. -/
def Map1_sum (PA : Param .map1 .map0 A A') (PB : Param .map1 .map0 B B') :
    Map1Has (R_sum PA PB) :=
  ⟨Sum.map PA.fwd.map PB.fwd.map⟩

/-- Trocq `sum_map_in_R` as a `map2a` record: the lifted map's graph is included
    in `R_sum`, by cases on the constructor. Needs `PA`, `PB` forward-`map2a`. -/
def Map2a_sum (PA : Param .map2a .map0 A A') (PB : Param .map2a .map0 B B') :
    Map2aHas (R_sum PA PB) where
  map := Sum.map PA.fwd.map PB.fwd.map
  map_in_R := by
    intro s s' e
    subst e
    cases s with
    | inl a => exact PA.fwd.map_in_R a (PA.fwd.map a) rfl
    | inr b => exact PB.fwd.map_in_R b (PB.fwd.map b) rfl

/-- Trocq `R_in_map_sum`: `R_sum`-relatedness implies the lifted map sends `s`
    to `s'`, by cases on the constructor and the payload `R_in_map`. The
    funext-free relation-inclusion half. Needs `PA`, `PB` forward-`map2b`. -/
theorem R_in_map_sum (PA : Param .map2b .map0 A A') (PB : Param .map2b .map0 B B')
    (s : A ⊕ B) (s' : A' ⊕ B') (h : R_sum PA PB s s') :
    Sum.map PA.fwd.map PB.fwd.map s = s' := by
  cases s <;> cases s' <;> simp_all only [R_sum, Sum.map]
  · exact congrArg Sum.inl (PA.fwd.R_in_map _ _ h)
  · exact congrArg Sum.inr (PB.fwd.R_in_map _ _ h)

/-- `paramSum`: from payload relations at forward-`map2a`, backward-`map0`, the
    annotated relation on `Sum`, forward-`map1`, backward-`map0`. -/
def paramSum (PA : Param .map2a .map0 A A') (PB : Param .map2a .map0 B B') :
    Param .map1 .map0 (A ⊕ B) (A' ⊕ B') where
  R := R_sum PA PB
  fwd := ⟨Sum.map PA.fwd.map PB.fwd.map⟩
  bwd := ⟨⟩

/-! ## `Nat`: the relation `R_nat`

The representative *recursive, parameter-free* inductive. With no type
parameter the pointwise lift collapses to equality (`zero ~ zero`,
`succ n ~ succ n'` iff `n ~ n'`, i.e. `n = n'`), and the recursor supports the
*full* `map3` in both directions (the identity map's graph is `Eq`, both
inclusions identities) — univalence-free. This is the base case the handler hits
for any closed (parameter-free) inductive: the derived relation is `Eq` and the
`Param` is the diagonal at `map3`. -/

/-- Trocq's natural-number relation: pointwise lift to `Nat` of the (empty list
    of) parameters, i.e. plain equality. Stated by recursion to mirror the
    constructor-wise shape the handler emits (`zeroR`/`succR`). -/
def R_nat : Nat → Nat → Prop
  | .zero,   .zero   => True
  | .succ n, .succ m => R_nat n m
  | _,       _       => False

/-- `R_nat` is equality: the constructor-wise lift of the parameter-free
    inductive collapses to the diagonal. -/
theorem R_nat_eq_eq : R_nat = Eq := by
  funext n m
  apply propext
  constructor
  · intro h
    induction n generalizing m with
    | zero => cases m with
      | zero => rfl
      | succ _ => exact (h).elim
    | succ n ih => cases m with
      | zero => exact (h).elim
      | succ m => exact congrArg Nat.succ (ih m h)
  · rintro rfl
    induction n with
    | zero => exact True.intro
    | succ n ih => exact ih

/-- Trocq `Map3` for `Nat`: the identity is the forward map and its graph is
    exactly `R_nat` (= `Eq`), both inclusions identities. The recursor of a
    parameter-free inductive supports the full `map3`. -/
def Map3_nat : Map3Has R_nat where
  map := id
  map_in_R := by intro n m e; rw [R_nat_eq_eq]; exact e
  R_in_map := by intro n m h; rw [R_nat_eq_eq] at h; exact h

/-- `paramNat`: the parameter-free inductive `Nat` as the diagonal `Param` at
    forward/backward-`map3`. The handler's base case for any closed inductive. -/
def paramNat : Param .map3 .map3 Nat Nat where
  R := R_nat
  fwd := Map3_nat
  bwd := by
    rw [show symRel R_nat = R_nat from by funext n m; rw [R_nat_eq_eq]; exact propext eq_comm]
    exact Map3_nat

/-! ## Demos -/

section Demo

/-- `R_sum` of two diagonals relates `inl a` to `inl a'` exactly when `a = a'`. -/
example {T S : Type u} (a a' : T) :
    R_sum (paramEqElt T) (paramEqElt S) (.inl a) (.inl a') ↔ a = a' := Iff.rfl

/-- Mixed constructors are unrelated. -/
example {T S : Type u} (a : T) (b : S) :
    ¬ R_sum (paramEqElt T) (paramEqElt S) (.inl a) (.inr b) := id

/-- The sum forward map computes through the constructor. -/
example {T S : Type u} (a : T) :
    (paramSum (paramEqElt T) (paramEqElt S)).fwd.map (.inl a) = Sum.inl a := rfl

/-- `R_nat` is equality. -/
example (n m : Nat) : R_nat n m ↔ n = m := by rw [R_nat_eq_eq]

/-- `paramNat`'s forward map is the identity, related to its argument. -/
example (n : Nat) : (paramNat).R n ((paramNat).fwd.map n) :=
  (paramNat).fwd.map_in_R n n rfl

/-- `#guard_msgs` pin: the derived `Nat` relation collapses to the diagonal. -/
example : R_nat 3 3 := by rw [R_nat_eq_eq]

end Demo

end Transfer.Param
