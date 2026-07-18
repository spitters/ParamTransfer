/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy

/-!
# The dependent-Π (`∀` / forall) parametricity rule

A faithful Lean port of Trocq's `std/Param_forall.v` (`coq-community/trocq`):
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
are unnecessary. The forward map of the dependent-Π rule —
`Map1_forall` below — is *univalence-free*: it only needs the domain's
backward structure at level `map2a` (a map plus `map a' = a → R a a'`),
which `Param02a`/`Param04` all provide. This is the axiom-free part:
the dependent motive's forward transfer.

## Where univalence enters (`Map2a_forall`)

The forward map `Map1_forall` instantiates the codomain family at the *single*
related pair `(PA.bwd.map a', a')` reachable from the backward map applied to
`a'`. That is enough to *produce* an element of `B' a'` from `f`, i.e. to build
the `map` field of `Map2aHas`. But the next level `Map2a_forall` also needs
the `map_in_R` field:

  `map_in_R : ∀ f g, (Map1_forall …).map f = g → R_forall PA PB f g`,

i.e. for an *arbitrary* related pair `(a, a')` with witness `aR : PA.R a a'`, it
must relate `(map f) a' : B' a'` — which was built using the *specific* witness
`PA.bwd.map_in_R a' (PA.bwd.map a') rfl` at the input `PA.bwd.map a'` — to
`f a : B a` at the *given* `a`. Reconciling the two requires identifying the
input `a` with `PA.bwd.map a'` **and transporting the codomain family `PB`
along that identification coherently**. Over a general `Param`, the only data
that delivers a *coherent* such transport — `bwd.map a' = a` reflecting back to
`R a a'` *and* round-tripping (`R_in_mapK`) — is the domain backward relation at
`map4`, i.e. a univalent equivalence. Hence `Map2a_forall` requires
`PA : Param04` (domain backward `map4`), and that `map4` coherence is where
the dependent-Π rule requires univalence: the dependent-Π output at level `≥ map2a`
needs the domain relation to be an equivalence so the motive transports.

Concretely, the signature not implemented here (would require the
`map4`/univalence machinery; stated as a comment, no `sorry`):

  `def Map2a_forall (PA : Param .map0 .map4 A A')`
  `    (PB : ∀ a a', PA.R a a' → Param .map2a .map0 (B a) (B' a')) :`
  `    Map2aHas (R_forall PA PB)`

with the `map` field reusing `Map1_forall`'s, and the `map_in_R` field the part
that consumes the `map4` coherence (`PA.bwd.R_in_mapK`) to transport `PB`.

## Accessor dictionary (Coq → Lean), backward direction of `PA`

Recall `PA.bwd : MapHas n (symRel PA.R)`, and `symRel PA.R a' a` is defeq
`PA.R a a'`. So at the input levels where the field exists:
- `PA.bwd.map      : A' → A`                                   (PA bwd ≥ `map1`)
- `PA.bwd.map_in_R : ∀ a' a, PA.bwd.map a' = a → PA.R a a'`     (PA bwd ≥ `map2a`)
- `(PB a a' aR).fwd.map : B a → B' a'`                          (PB fwd ≥ `map1`)
-/

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

/-! ## `map1` — the univalence-free dependent-Π forward map

The dependent motive's forward transfer, axiom-free (only `PA`
backward-`map2a`, no `map4`/univalence).

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

/-! ## `Param`-level assembly: the dependent-Π annotated relation at `(map1, map0)` -/

/-- Assemble the dependent-Π `Param` from a domain `Param02a` and a `Param10`
    codomain family: forward structure `map1` (via `Map1_forall`), backward
    structure `map0` (trivial). This is the level the univalence-free forward
    map supports — no `map4`/univalence used. -/
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
