/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy

/-!
# The arrow (`app` / function) parametricity rule

A faithful Lean port of Trocq's `std/Param_arrow.v` (`coq-community/trocq`):
the combinators that build a `Param` annotated relation on a function space
`(A → B)` from `Param` relations on the domain `A` and codomain `B`.

This is the function rule of the parametricity translation: it tells the
engine how to relate `f : A → B` and `f' : A' → B'`.

## The funext advantage

Coq's `std` variant gates the `map2b`/`map3` arrow combinators on a
`` `{Funext} `` instance, because their `R_in_map` field needs functional
extensionality to prove `map f = f'` from a pointwise relation. Lean has
`funext` as a theorem, so those gates are unnecessary: `map0` through `map3`
(and `map4`, free by proof irrelevance on `Prop`-valued `R`) hold with no
extra axioms.

## Accessor dictionary (Coq → Lean)

At the input levels where the field exists:
- `map PB`        → `PB.fwd.map`        (PB fwd ≥ `map1`)
- `comap PA`      → `PA.bwd.map`        (PA bwd ≥ `map1`)
- `map_in_R PB`   → `PB.fwd.map_in_R`   (PB fwd ≥ `map2a`)
- `R_in_map PB`   → `PB.fwd.R_in_map`   (PB fwd ≥ `map2b`)
- `comap_in_R PA` → `PA.bwd.map_in_R`   (PA bwd ≥ `map2a`)
- `R_in_comap PA` → `PA.bwd.R_in_map`   (PA bwd ≥ `map2b`)

Recall `PA.bwd : MapHas n (symRel PA.R)`, and `symRel PA.R a' a = PA.R a a'`,
so `PA.bwd.map : A' → A`, `PA.bwd.map_in_R : ∀ a' a, PA.bwd.map a' = a → PA.R a a'`,
and `PA.bwd.R_in_map : ∀ a' a, PA.R a a' → PA.bwd.map a' = a`.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A A' B B' : Type u}

/-! ## The function relation `R_arrow` -/

/-- Trocq `R_arrow`: two functions are related when they send `PA`-related
    inputs to `PB`-related outputs. Coq accesses only the `R` field, so the
    level parameters stay fully polymorphic (the function relation does not
    depend on how much structure each component carries). -/
def R_arrow {mA nA mB nB : MapClass}
    (PA : Param mA nA A A') (PB : Param mB nB B B') :
    (A → B) → (A' → B') → Prop :=
  fun f f' => ∀ a a', PA.R a a' → PB.R (f a) (f' a')

/-! ## `map0` — no structure -/

/-- Trocq `Map0_arrow`. -/
def Map0_arrow {mA nA mB nB : MapClass}
    (PA : Param mA nA A A') (PB : Param mB nB B B') :
    Map0Has (R_arrow PA PB) := ⟨⟩

/-! ## `map1` — the forward map `PB.map ∘ f ∘ PA.comap` -/

/-- Trocq `Map1_arrow`: the function map sends `f : A → B` to
    `fun a' => PB.fwd.map (f (PA.bwd.map a'))`. Needs `PA` backward-`map1`
    (to get `comap`) and `PB` forward-`map1` (to get `map`). -/
def Map1_arrow (PA : Param .map0 .map1 A A') (PB : Param .map1 .map0 B B') :
    Map1Has (R_arrow PA PB) :=
  ⟨fun f a' => PB.fwd.map (f (PA.bwd.map a'))⟩

/-! ## `map2a` — map plus graph-inclusion `map_in_R` -/

/-- Trocq `Map2a_arrow`. The function map is the same `PB.map ∘ f ∘ PA.comap`;
    `map_in_R` says: if that map sends `f` to `f'`, then `f` and `f'` are
    `R_arrow`-related. Needs `PA` backward-`map2b` (`R_in_comap`) and
    `PB` forward-`map2a` (`map_in_R`). -/
def Map2a_arrow (PA : Param .map0 .map2b A A') (PB : Param .map2a .map0 B B') :
    Map2aHas (R_arrow PA PB) where
  map := fun f a' => PB.fwd.map (f (PA.bwd.map a'))
  map_in_R := by
    intro f f' e a a' aR
    -- `e` exhibits `f'` as `PB.map ∘ f ∘ PA.comap`; `aR` gives `PA.comap a' = a`.
    subst e
    show PB.R (f a) (PB.fwd.map (f (PA.bwd.map a')))
    rw [PA.bwd.R_in_map a' a aR]
    exact PB.fwd.map_in_R _ _ rfl

/-! ## `map2b` — map plus relation-inclusion `R_in_map` (via funext) -/

/-- Trocq `Map2b_arrow`. `R_in_map` says: if `f`, `f'` are `R_arrow`-related,
    then the function map sends `f` to `f'`. The Coq `std` variant gates this
    on `` `{Funext} ``; in Lean `funext` is a theorem, so it is axiom-free.
    Needs `PA` backward-`map2a` (`comap_in_R`) and `PB` forward-`map2b`
    (`R_in_map`). -/
def Map2b_arrow (PA : Param .map0 .map2a A A') (PB : Param .map2b .map0 B B') :
    Map2bHas (R_arrow PA PB) where
  map := fun f a' => PB.fwd.map (f (PA.bwd.map a'))
  R_in_map := by
    intro f f' hR
    funext a'
    -- pointwise: `PB.map (f (PA.comap a')) = f' a'`, via `PB.R_in_map` on the
    -- relatedness `PB.R (f (PA.comap a')) (f' a')`, which `hR` supplies once
    -- `PA.comap_in_R` gives `PA.R (PA.comap a') a'`.
    exact PB.fwd.R_in_map _ _ (hR (PA.bwd.map a') a' (PA.bwd.map_in_R a' _ rfl))

/-! ## `map3` — both inclusions (via funext) -/

/-- Trocq `Map3_arrow`: the full graph relation, combining `Map2a_arrow`'s
    `map_in_R` and `Map2b_arrow`'s `R_in_map`. Needs both inclusions on each
    component: `PA` backward-`map3`, `PB` forward-`map3`. Axiom-free in Lean
    (the `R_in_map` half uses `funext`). -/
def Map3_arrow (PA : Param .map0 .map3 A A') (PB : Param .map3 .map0 B B') :
    Map3Has (R_arrow PA PB) where
  map := fun f a' => PB.fwd.map (f (PA.bwd.map a'))
  map_in_R := by
    intro f f' e a a' aR
    subst e
    show PB.R (f a) (PB.fwd.map (f (PA.bwd.map a')))
    rw [PA.bwd.R_in_map a' a aR]
    exact PB.fwd.map_in_R _ _ rfl
  R_in_map := by
    intro f f' hR
    funext a'
    exact PB.fwd.R_in_map _ _ (hR (PA.bwd.map a') a' (PA.bwd.map_in_R a' _ rfl))

/-! ## `map4` — `map3` plus the (free, proof-irrelevant) coherence -/

/-- Trocq `Map4_arrow`. Over `Prop`-valued `R` the coherence `R_in_mapK` is
    automatic by proof irrelevance, so the univalent level is constructible
    without univalence. Needs `PA` backward-`map3`, `PB` forward-`map3`. -/
def Map4_arrow (PA : Param .map0 .map3 A A') (PB : Param .map3 .map0 B B') :
    Map4Has (R_arrow PA PB) where
  map := fun f a' => PB.fwd.map (f (PA.bwd.map a'))
  map_in_R := by
    intro f f' e a a' aR
    subst e
    show PB.R (f a) (PB.fwd.map (f (PA.bwd.map a')))
    rw [PA.bwd.R_in_map a' a aR]
    exact PB.fwd.map_in_R _ _ rfl
  R_in_map := by
    intro f f' hR
    funext a'
    exact PB.fwd.R_in_map _ _ (hR (PA.bwd.map a') a' (PA.bwd.map_in_R a' _ rfl))
  R_in_mapK := by intro a b r; rfl

/-! ## The `Param`-level arrow combinator

Assembling forward and backward structure into a `Param` on the function space.
The forward-`map1`, backward-`map1` output needs only a forward and a backward
map on each component, i.e. `PA PB : Param .map1 .map1`.

- The forward map is `Map1_arrow`'s `PB.map ∘ · ∘ PA.comap`.
- The backward map is the symmetric `PA.map ∘ · ∘ PB.comap` — `Map1_arrow` run
  on the directions of `PA.symm`, `PB.symm`. Since `Map1Has` (and hence the
  `bwd` field `MapHas .map1 (symRel (R_arrow PA PB))`) records only a function,
  it is built inline and no relation-coercion is needed. -/

/-- `paramArrow`: from `PA PB : Param .map1 .map1`, an annotated relation
    `Param .map1 .map1 (A → B) (A' → B')` whose relation is `R_arrow PA PB`,
    forward map `PB.map ∘ · ∘ PA.comap`, backward map `PA.map ∘ · ∘ PB.comap`. -/
def paramArrow (PA : Param .map1 .map1 A A') (PB : Param .map1 .map1 B B') :
    Param .map1 .map1 (A → B) (A' → B') where
  R := R_arrow PA PB
  fwd := ⟨fun f a' => PB.fwd.map (f (PA.bwd.map a'))⟩
  bwd := ⟨fun f a => PB.bwd.map (f (PA.fwd.map a))⟩

/-! ## Demo: the arrow combinators compose on a concrete pair

The identity (equality) relation on a type, packaged at the levels each arrow
rule consumes (`Param .map0 .map3` as domain, `Param .map3 .map0` as codomain,
`Param .map1 .map1` for `paramArrow`), feeds two copies through the arrow
combinators; the resulting function relation is the pointwise lift of
equality. -/

section Demo

/-- The diagonal as a domain input for the arrow rules: forward-`map0`,
    backward-`map3`. -/
def paramEqDom (T : Type u) : Param .map0 .map3 T T where
  R := Eq
  fwd := ⟨⟩
  bwd := ⟨id, fun _ _ h => h.symm, fun _ _ h => h.symm⟩

/-- The diagonal as a codomain input for the arrow rules: forward-`map3`,
    backward-`map0`. -/
def paramEqCod (S : Type u) : Param .map3 .map0 S S where
  R := Eq
  fwd := ⟨id, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨⟩

/-- The arrow combinator applied to two diagonals yields the diagonal on the
    function space *as a relation*: `R_arrow` of `Eq` and `Eq` says `f` and `f'`
    agree on equal inputs, i.e. pointwise equality. -/
example {T S : Type u} (f f' : T → S) :
    R_arrow (paramEqDom T) (paramEqCod S) f f' ↔ ∀ a, f a = f' a := by
  constructor
  · intro h a; exact h a a rfl
  · intro h a a' (haa' : a = a'); subst haa'; exact h a

/-- `Map3_arrow` is constructible on the diagonals (all six obligations close),
    and its forward `map` is the expected `PB.map ∘ f ∘ PA.comap`, which for the
    diagonal is just `f` itself. -/
example {T S : Type u} (f : T → S) :
    (Map3_arrow (paramEqDom T) (paramEqCod S)).map f = f := rfl

/-- The diagonal at the forward-`map1`, backward-`map1` level (the input shape
    `paramArrow` consumes). -/
def paramEq1 (T : Type u) : Param .map1 .map1 T T where
  R := Eq
  fwd := ⟨id⟩
  bwd := ⟨id⟩

/-- The `Param`-level combinator assembles, and its relation is `R_arrow`. -/
example {T S : Type u} :
    (paramArrow (paramEq1 T) (paramEq1 S)).R = R_arrow (paramEq1 T) (paramEq1 S) := rfl

/-- Its forward and backward function maps are both the identity-conjugation,
    which collapse to plain application on the diagonal. -/
example {T S : Type u} (f : T → S) :
    (paramArrow (paramEq1 T) (paramEq1 S)).fwd.map f = f := rfl

end Demo

end Transfer.Param
