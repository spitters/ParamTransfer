/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Hierarchy.ParamHierarchy

/-!
# The dependent-Π (`∀` / forall) parametricity rule

A Lean port of Trocq's `std/Param_forall.v` (<https://github.com/rocq-community/trocq>):
the combinators that build a `Param` annotated relation on a **dependent**
function space `(∀ a, B a)` from a `Param` relation `PA` on the domain and a
*family* `PB` of `Param` relations on the codomain, one for each pair of
related inputs.

This is the dependent-Π / dependent-motive rule of the parametricity
translation. Where the arrow rule (`ParamArrow.lean`) relates `f : A → B` and
`f' : A' → B'` with a *constant* codomain relation, here the codomain type
`B a` (resp. `B' a'`) depends on the argument, and the relation tying
`f a : B a` to `f' a' : B' a'` is itself indexed by the witness `aR : PA.R a a'`.

## The funext advantage

Coq's `std` variant gates the `map2b`/`map3` forall combinators on a
`` `{Funext} `` instance. Lean has `funext` as a theorem, so those gates
are unnecessary.

## The level table

The rule holds at every output level. `forallReq` gives the backward level the
domain must carry and `forallFiberReq` the forward level of the codomain family:

| output `t` | domain backward | family forward |
|---|---|---|
| `map0` | `map0` | `map0` |
| `map1` | `map2a` | `map1` |
| `map2a` | `map3` | `map2a` |
| `map2b` | `map2a` | `map2b` |
| `map3` | `map3` | `map3` |
| `map4` | `map3` | `map3` |

The forward map at `a'` applies the family at the pair `(PA.bwd.map a', a')`, with
the witness `PA.bwd.map_in_R a' _ rfl`; so every level from `map1` up reads the
domain backward at `map2a` at least. `map2b` asks for nothing more: a relation
`R_forall PA PB f g` is used only at that witness, and `funext` concludes.

`map2a` also asks for `R_in_map` of the domain, to identify an arbitrary `a` related
to `a'` with `PA.bwd.map a'`. Substituting this equation transports the family, and
the witness that results and the given `aR` are proofs of one proposition, so they
are equal by proof irrelevance. Relations here are `Prop`-valued, which is why no
`map4` of the domain is used; Trocq's `map4` requirement comes from `Type`-valued
relations, where the two witnesses must be related by `R_in_mapK`. Output `map4` is
output `map3` with a coherence between proofs of a proposition.

The rule uses no univalence at any output level. The boundary is the relation
between universes (`UnivalenceStatus`), which is outside this rule: here the family
`PB` is given.

## Accessor dictionary (Coq → Lean), backward direction of `PA`

Recall `PA.bwd : MapHas n (symRel PA.R)`, and `symRel PA.R a' a` is defeq
`PA.R a a'`. So at the input levels where the field exists:
- `PA.bwd.map      : A' → A`                                   (PA bwd ≥ `map1`)
- `PA.bwd.map_in_R : ∀ a' a, PA.bwd.map a' = a → PA.R a a'`     (PA bwd ≥ `map2a`)
- `(PB a a' aR).fwd.map : B a → B' a'`                          (PB fwd ≥ `map1`)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u}

/-! ## The dependent forall relation `R_forall` -/

/-- Trocq `R_forall`: two dependent functions are related when, for every pair
    of `PA`-related inputs `a`, `a'` with witness `aR`, their outputs are
    `(PB a a' aR)`-related. The codomain relation is a *family* indexed by the
    relatedness witness `aR : PA.R a a'`. Only the `R` fields are touched, so
    the level parameters stay fully polymorphic. -/
def R_forall {mA nA mB nB : MapClass}
    (PA : Param mA nA A A')
    (PB : ∀ a a', PA.R a a' → Param mB nB (B a) (B' a')) :
    (∀ a, B a) → (∀ a', B' a') → Prop :=
  fun f f' => ∀ a a' (aR : PA.R a a'), (PB a a' aR).R (f a) (f' a')

/-! ## `map0` — no structure -/

/-- Trocq `Map0_forall`. -/
def Map0_forall {mA nA mB nB : MapClass}
    (PA : Param mA nA A A')
    (PB : ∀ a a', PA.R a a' → Param mB nB (B a) (B' a')) :
    Map0Has (R_forall PA PB) := ⟨⟩

/-! ## `map1` — the dependent-Π forward map

The dependent motive's forward transfer, axiom-free (only `PA` backward-`map2a`).

For each `a' : A'`, set `a := PA.bwd.map a'`. The backward `map_in_R` at `rfl`
gives a witness `aR : PA.R a a'`. The codomain family at that pair has a
forward map `(PB a a' aR).fwd.map : B a → B' a'`, applied to `f a`. -/
def Map1_forall
    (PA : Param .map0 .map2a A A')
    (PB : ∀ a a', PA.R a a' → Param .map1 .map0 (B a) (B' a')) :
    Map1Has (R_forall PA PB) :=
  ⟨fun f a' =>
    (PB (PA.bwd.map a') a' (PA.bwd.map_in_R a' (PA.bwd.map a') rfl)).fwd.map
      (f (PA.bwd.map a'))⟩

/-! ## The forward map and its two inclusions, over relations

These three are stated for a relation `AR` on the domain and a family `BR` of
relations over its witnesses, with no level attached. -/

section Relational

variable {AR : A → A' → Prop} {BR : ∀ a a', AR a a' → B a → B' a' → Prop}

/-- The map of a dependent function: the backward map of the domain, then the fiber
    map at its witness. -/
def forallMap (imap : A' → A) (wit : ∀ a', AR (imap a') a')
    (fmap : ∀ a a', AR a a' → B a → B' a') : (∀ a, B a) → ∀ a', B' a' :=
  fun f a' => fmap _ _ (wit a') (f (imap a'))

/-- The graph of `forallMap` lies in the relation of dependent functions, when the
    domain's backward map contains its relation and the graph of each fiber map lies
    in the fiber relation. Substituting `imap a' = a` transports the family; the
    witnesses agree by proof irrelevance. -/
theorem forallMap_in_R (imap : A' → A) (wit : ∀ a', AR (imap a') a')
    (fmap : ∀ a a', AR a a' → B a → B' a') (hA : ∀ a a', AR a a' → imap a' = a)
    (hB : ∀ a a' h x, BR a a' h x (fmap a a' h x)) (f : ∀ a, B a) (g : ∀ a', B' a')
    (e : forallMap imap wit fmap f = g) (a : A) (a' : A') (h : AR a a') :
    BR a a' h (f a) (g a') := by
  subst e
  obtain rfl := hA a a' h
  exact hB _ _ _ _

/-- The relation of dependent functions lies in the graph of `forallMap`, when each
    fiber map contains its relation. -/
theorem R_in_forallMap (imap : A' → A) (wit : ∀ a', AR (imap a') a')
    (fmap : ∀ a a', AR a a' → B a → B' a')
    (hB : ∀ a a' h x y, BR a a' h x y → fmap a a' h x = y) (f : ∀ a, B a) (g : ∀ a', B' a')
    (r : ∀ a a' h, BR a a' h (f a) (g a')) : forallMap imap wit fmap f = g :=
  funext fun a' => hB _ _ _ _ _ (r _ a' (wit a'))

end Relational

/-! ## `map2a`, `map2b`, `map3`, `map4` — the rule above the forward map

Only the backward structure of the domain and the forward structure of the family
are used, so the other two levels stay free. -/

/-- Output `map2a`: the domain backward at `map3`, the family forward at `map2a`.
    The domain's `R_in_map` identifies an arbitrary related input with the image of
    the backward map. -/
def Map2a_forall {mA nB : MapClass}
    (PA : Param mA .map3 A A')
    (PB : ∀ a a', PA.R a a' → Param .map2a nB (B a) (B' a')) :
    Map2aHas (R_forall PA PB) :=
  ⟨forallMap (AR := PA.R) PA.bwd.map (fun a' => PA.bwd.map_in_R a' _ rfl)
      fun a a' h => (PB a a' h).fwd.map,
    fun f g e a a' h => forallMap_in_R (BR := fun a a' h => (PB a a' h).R) _ _ _
      (fun a a' h => PA.bwd.R_in_map a' a h)
      (fun a a' h x => (PB a a' h).fwd.map_in_R x _ rfl) f g e a a' h⟩

/-- Output `map2b`: the domain backward at `map2a`, the family forward at `map2b`.
    A related pair of functions is read at the witness of the backward map, and
    `funext` concludes. -/
def Map2b_forall {mA nB : MapClass}
    (PA : Param mA .map2a A A')
    (PB : ∀ a a', PA.R a a' → Param .map2b nB (B a) (B' a')) :
    Map2bHas (R_forall PA PB) :=
  ⟨forallMap (AR := PA.R) PA.bwd.map (fun a' => PA.bwd.map_in_R a' _ rfl)
      fun a a' h => (PB a a' h).fwd.map,
    fun f g r => R_in_forallMap (BR := fun a a' h => (PB a a' h).R) _ _ _
      (fun a a' h => (PB a a' h).fwd.R_in_map) f g r⟩

/-- Output `map3`: the domain backward at `map3`, the family forward at `map3`. -/
def Map3_forall {mA nB : MapClass}
    (PA : Param mA .map3 A A')
    (PB : ∀ a a', PA.R a a' → Param .map3 nB (B a) (B' a')) :
    Map3Has (R_forall PA PB) :=
  ⟨forallMap (AR := PA.R) PA.bwd.map (fun a' => PA.bwd.map_in_R a' _ rfl)
      fun a a' h => (PB a a' h).fwd.map,
    fun f g e a a' h => forallMap_in_R (BR := fun a a' h => (PB a a' h).R) _ _ _
      (fun a a' h => PA.bwd.R_in_map a' a h)
      (fun a a' h x => (PB a a' h).fwd.map_in_R x _ rfl) f g e a a' h,
    fun f g r => R_in_forallMap (BR := fun a a' h => (PB a a' h).R) _ _ _
      (fun a a' h => (PB a a' h).fwd.R_in_map) f g r⟩

/-- Output `map4`: the inputs of `map3`. The coherence `R_in_mapK` is an equation
    between proofs of a proposition. -/
def Map4_forall {mA nB : MapClass}
    (PA : Param mA .map3 A A')
    (PB : ∀ a a', PA.R a a' → Param .map3 nB (B a) (B' a')) :
    Map4Has (R_forall PA PB) :=
  let h := Map3_forall PA PB
  ⟨h.map, h.map_in_R, h.R_in_map, fun _ _ _ => rfl⟩

/-! ## The level table -/

/-- The backward level of the domain required by the dependent-Π rule at an output
    forward level. -/
def forallReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map2a
  | .map2a => .map3
  | .map2b => .map2a
  | .map3 => .map3
  | .map4 => .map3

/-- The forward level of the codomain family required by the dependent-Π rule at an
    output forward level. -/
def forallFiberReq : MapClass → MapClass
  | .map0 => .map0
  | .map1 => .map1
  | .map2a => .map2a
  | .map2b => .map2b
  | .map3 => .map3
  | .map4 => .map3

/-- No output level asks for `map4` of the domain. -/
theorem forallReq_ne_map4 (t : MapClass) : forallReq t ≠ .map4 := by
  cases t <;> decide

/-- No output level asks for `map4` of the family. -/
theorem forallFiberReq_ne_map4 (t : MapClass) : forallFiberReq t ≠ .map4 := by
  cases t <;> decide

/-- The dependent-Π rule at every output forward level, with the inputs the tables
    `forallReq` and `forallFiberReq` give. -/
def mapHas_forall {mA nB : MapClass} : (t : MapClass) →
    (PA : Param mA (forallReq t) A A') →
    (PB : ∀ a a', PA.R a a' → Param (forallFiberReq t) nB (B a) (B' a')) →
    MapHas t (R_forall PA PB)
  | .map0, _, _ => (⟨⟩ : Map0Has _)
  | .map1, PA, PB =>
    let PA : Param mA .map2a A A' := PA
    let PB : ∀ a a', PA.R a a' → Param .map1 nB (B a) (B' a') := PB
    (⟨forallMap (AR := PA.R) PA.bwd.map (fun a' => PA.bwd.map_in_R a' _ rfl)
      fun a a' h => (PB a a' h).fwd.map⟩ : Map1Has _)
  | .map2a, PA, PB => Map2a_forall (mA := mA) PA PB
  | .map2b, PA, PB => Map2b_forall (mA := mA) PA PB
  | .map3, PA, PB => Map3_forall (mA := mA) PA PB
  | .map4, PA, PB => Map4_forall (mA := mA) PA PB

/-! ## `Param`-level assembly -/

/-- Structure of level `m` of a relation is structure of level `m` of a logically
    equivalent relation, with the same map. -/
def MapHas.ofIff {α β : Type u} {R S : α → β → Prop} (hRS : ∀ a b, R a b ↔ S a b) :
    (m : MapClass) → MapHas m R → MapHas m S
  | .map0, _ => (⟨⟩ : Map0Has S)
  | .map1, h => (⟨(h : Map1Has R).map⟩ : Map1Has S)
  | .map2a, h =>
    let h : Map2aHas R := h
    (⟨h.map, fun a b e => (hRS a b).1 (h.map_in_R a b e)⟩ : Map2aHas S)
  | .map2b, h =>
    let h : Map2bHas R := h
    (⟨h.map, fun a b r => h.R_in_map a b ((hRS a b).2 r)⟩ : Map2bHas S)
  | .map3, h =>
    let h : Map3Has R := h
    (⟨h.map, fun a b e => (hRS a b).1 (h.map_in_R a b e),
      fun a b r => h.R_in_map a b ((hRS a b).2 r)⟩ : Map3Has S)
  | .map4, h =>
    let h : Map4Has R := h
    (⟨h.map, fun a b e => (hRS a b).1 (h.map_in_R a b e),
      fun a b r => h.R_in_map a b ((hRS a b).2 r), fun _ _ _ => rfl⟩ : Map4Has S)

/-- The dependent-Π `Param` at every pair of output levels `(t, s)`: the domain at
    `(forallReq s, forallReq t)` and the family at
    `(forallFiberReq t, forallFiberReq s)`. The backward direction is the rule applied
    to the flipped domain and the flipped family. -/
def paramForallAt (t s : MapClass)
    (PA : Param (forallReq s) (forallReq t) A A')
    (PB : ∀ a a', PA.R a a' → Param (forallFiberReq t) (forallFiberReq s) (B a) (B' a')) :
    Param t s (∀ a, B a) (∀ a', B' a') where
  R := R_forall PA PB
  fwd := mapHas_forall t PA PB
  bwd := MapHas.ofIff (fun _ _ => ⟨fun r a a' h => r a' a h, fun r a' a h => r a a' h⟩) s
    (mapHas_forall (B := B') (B' := B) s PA.symm fun a' a h => (PB a a' h).symm)

/-! ## `Param`-level assembly at `(map1, map0)` from a domain at `(map0, map2a)` -/

/-- Assemble the dependent-Π `Param` from a domain `Param02a` and a `Param10`
    codomain family: forward structure `map1` (via `Map1_forall`), backward
    structure `map0` (trivial). `paramForallAt` is the rule at the other levels. -/
def paramForall
    (PA : Param .map0 .map2a A A')
    (PB : ∀ a a', PA.R a a' → Param .map1 .map0 (B a) (B' a')) :
    Param .map1 .map0 (∀ a, B a) (∀ a', B' a') where
  R := R_forall PA PB
  fwd := Map1_forall PA PB
  bwd := ⟨⟩

/-! ## Non-dependent corollary: recover the arrow relation

When `B`/`B'` are constant families, the dependent forall relation `R_forall`
specialises to the (non-dependent) arrow relation: two functions are related
when they send related inputs to related outputs. Here the codomain family is
the constant family `fun _ _ _ => PB`. -/

/-- The constant-family specialisation of `R_forall` over a flat codomain
    `C`, `C'`. This is definitionally the arrow relation
    `fun f f' => ∀ a a' (_ : PA.R a a'), PB.R (f a) (f' a')`. -/
def R_forall_const {mA nA : MapClass} {C C' : Type u}
    (PA : Param mA nA A A') (PB : Param .map0 .map0 C C') :
    (A → C) → (A' → C') → Prop :=
  R_forall (B := fun _ => C) (B' := fun _ => C') PA (fun _ _ _ => PB)

/-! ## Demo: `Map1_forall` on a concrete family

A small end-to-end instantiation showing the forward map computes. Take the
domain to be `Unit` related by full relation with a backward map, and a
codomain family `B a := Bool`, `B' a' := Bool` related by equality, forward
`map := id`. The forward dependent-Π map then transports a `fun _ => true`. -/

/-- Diagonal domain `Param` on `Unit`: `R = fun _ _ => True`, forward `map0`,
    backward `map2a` with `map := id` and the trivial `map_in_R`. -/
def paramUnit : Param .map0 .map2a Unit Unit where
  R := fun _ _ => True
  fwd := ⟨⟩
  bwd := ⟨fun _ => (), fun _ _ _ => trivial⟩

/-- Codomain family on `Bool` (equality graph), forward `map1` with `map := id`,
    backward `map0`. -/
def paramBoolFam :
    ∀ a a', paramUnit.R a a' → Param .map1 .map0 Bool Bool :=
  fun _ _ _ => { R := fun b b' => b = b', fwd := ⟨id⟩, bwd := ⟨⟩ }

/-- The forward dependent-Π map exists and applies (computation demo). -/
example : (∀ _ : Unit, Bool) → (∀ _ : Unit, Bool) :=
  (Map1_forall (B := fun _ => Bool) (B' := fun _ => Bool) paramUnit paramBoolFam).map

/-- It sends the constant-`true` function to the constant-`true` function. -/
example :
    (Map1_forall (B := fun _ => Bool) (B' := fun _ => Bool)
      paramUnit paramBoolFam).map (fun _ => true) = (fun _ => true) := rfl

end Transfer.Param
