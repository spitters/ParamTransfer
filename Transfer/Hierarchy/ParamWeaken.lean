/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamLevel
import Transfer.Hierarchy.ParamEquiv

/-!
# The `⊑`-driven `Param` weakening (level navigation)

`ParamLevel.lean` supplies the `MapClass` lattice order `⊑` and the meet. This
module supplies the witness-level counterpart: the function that turns a
synthesized witness at a level into a witness at any lower level the lattice
order permits. This is the mechanism behind "synthesize at the strongest
available level, then use at the minimal level a goal needs" — the downward
(forget) half of the level navigation.

The crux is `forgetMapHas`: for any `m' ⊑ m`, a `MapHas m R` forgets down to a
`MapHas m' R`, by composing the per-level forgets already proved in
`ParamHierarchy.lean` (`Map4Has.toMap3`, `Map3Has.toMap2a`/`toMap2b`,
`Map2aHas.toMap1`/`Map2bHas.toMap1`, `Map1Has.forget`). It is a full case
enumeration on the *target* `m'` then the *source* `m`; the lattice-invalid
pairs are discharged from the hypothesis `h : m' ⊑ m`, which reduces to
`false = true` there.

`Param.weaken` then forgets both directions (forward on `fwd`, backward on
`bwd`), giving the lattice's action on annotated relations:

> a witness at `(m, n)` supplies a witness at every `(m', n')` with
> `m' ⊑ m` and `n' ⊑ n`.

## Navigation and the remaining search

This completes the lattice navigation: `meet` (the least common level,
`ParamLevel`) plus `forgetMapHas`/`Param.weaken` (forget down to it). The
remaining piece of the level solver is the upward search — picking which
level to synthesize at, i.e. a `MetaM`/`outParam` resolver that reads the
`arrowReq`/`forallReq` decision tables (`ParamLevel.lean`) to choose the
combinator and the minimal feasible level before invoking the synthesizer. That
resolver, `resolveParamLevel`, is the final step; `Param.weaken` lets it
synthesize high and land at the lower level a goal uses.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

/-! ## `forgetMapHas` — forget one direction down the lattice -/

/-- Forget down the lattice (one direction). For `m' ⊑ m`, downgrade a
    `MapHas m R` to a `MapHas m' R` by composing the per-level forgets from
    `ParamHierarchy.lean`. Full case enumeration on the target `m'` then the
    source `m`; lattice-invalid pairs (`m' ⊑ m` is `false`) are discharged from
    `h : m' ⊑ m`, whose type reduces to `false = true`. -/
def forgetMapHas {A B : Type u} {R : A → B → Prop} :
    (m' m : MapClass) → m' ⊑ m → MapHas m R → MapHas m' R
  -- target map0: the empty record, available from every source.
  | .map0,  .map0,  _, _ => (⟨⟩ : Map0Has R)
  | .map0,  .map1,  _, _ => (⟨⟩ : Map0Has R)
  | .map0,  .map2a, _, _ => (⟨⟩ : Map0Has R)
  | .map0,  .map2b, _, _ => (⟨⟩ : Map0Has R)
  | .map0,  .map3,  _, _ => (⟨⟩ : Map0Has R)
  | .map0,  .map4,  _, _ => (⟨⟩ : Map0Has R)
  -- target map1: forget down to the bare map.
  | .map1,  .map0,  h, _ => by simp [MapClass.le] at h
  | .map1,  .map1,  _, x => x
  | .map1,  .map2a, _, x => x.toMap1
  | .map1,  .map2b, _, x => x.toMap1
  | .map1,  .map3,  _, x => x.toMap2a.toMap1
  | .map1,  .map4,  _, x => x.toMap3.toMap2a.toMap1
  -- target map2a.
  | .map2a, .map0,  h, _ => by simp [MapClass.le] at h
  | .map2a, .map1,  h, _ => by simp [MapClass.le] at h
  | .map2a, .map2a, _, x => x
  | .map2a, .map2b, h, _ => by simp [MapClass.le] at h
  | .map2a, .map3,  _, x => x.toMap2a
  | .map2a, .map4,  _, x => x.toMap3.toMap2a
  -- target map2b.
  | .map2b, .map0,  h, _ => by simp [MapClass.le] at h
  | .map2b, .map1,  h, _ => by simp [MapClass.le] at h
  | .map2b, .map2a, h, _ => by simp [MapClass.le] at h
  | .map2b, .map2b, _, x => x
  | .map2b, .map3,  _, x => x.toMap2b
  | .map2b, .map4,  _, x => x.toMap3.toMap2b
  -- target map3.
  | .map3,  .map0,  h, _ => by simp [MapClass.le] at h
  | .map3,  .map1,  h, _ => by simp [MapClass.le] at h
  | .map3,  .map2a, h, _ => by simp [MapClass.le] at h
  | .map3,  .map2b, h, _ => by simp [MapClass.le] at h
  | .map3,  .map3,  _, x => x
  | .map3,  .map4,  _, x => x.toMap3
  -- target map4: only map4 ⊑ map4.
  | .map4,  .map0,  h, _ => by simp [MapClass.le] at h
  | .map4,  .map1,  h, _ => by simp [MapClass.le] at h
  | .map4,  .map2a, h, _ => by simp [MapClass.le] at h
  | .map4,  .map2b, h, _ => by simp [MapClass.le] at h
  | .map4,  .map3,  h, _ => by simp [MapClass.le] at h
  | .map4,  .map4,  _, x => x

/-! ## `Param.weaken` — the lattice action on annotated relations -/

set_option linter.dupNamespace false in
/-- Weaken an annotated relation down the lattice. Given `m' ⊑ m` and
    `n' ⊑ n`, a `Param m n A B` forgets to a `Param m' n' A B`: keep the
    relation `R`, forget the forward witness `fwd` to level `m'` and the
    backward witness `bwd` to level `n'`. This is the "synthesize-high, use-low"
    move: the synthesizer may produce at the strongest available level, and
    `Param.weaken` brings it to the minimal level the goal needs. -/
def Param.weaken {m m' n n' : MapClass} {A B : Type u}
    (hm : m' ⊑ m) (hn : n' ⊑ n) (p : Param m n A B) : Param m' n' A B where
  R := p.R
  fwd := forgetMapHas m' m hm p.fwd
  bwd := forgetMapHas n' n hn p.bwd

/-! ## Examples — exercising the weakening on the concrete witnesses

`paramOfEmbedding : Param map3 map0` (graph of an encoder, no decoder) and
`paramOfEquiv : Param map3 map2b` (left-inverse encoding) are the two concrete
`Param` constructors in the hierarchy. Every weakening below is a one-liner
`Param.weaken (by decide) (by decide) _`. -/

open Transfer in
/-- `paramOfEmbedding : Param map3 map0` weakens to `Param map1 map0`
    (forward forgets `map3 → map1`; backward stays `map0`). -/
def embeddingAsMap1 {A α : Type u} [ReprEmbeddingClass A α] : Param .map1 .map0 A α :=
  Param.weaken (by decide) (by decide) paramOfEmbedding

open Transfer in
/-- `paramOfEmbedding : Param map3 map0` weakens to `Param map2a map0`
    (forward forgets `map3 → map2a`, the map-with-graph-inclusion). -/
def embeddingAsMap2a {A α : Type u} [ReprEmbeddingClass A α] : Param .map2a .map0 A α :=
  Param.weaken (by decide) (by decide) paramOfEmbedding

open Transfer in
/-- `paramOfEquiv : Param map3 map2b` weakens to `Param map0 map2b`
    (forward forgets all the way to `map0`; backward stays `map2b`). -/
def equivAsMap0Map2b {A α : Type u} [ReprEquivClass A α] : Param .map0 .map2b A α :=
  Param.weaken (by decide) (by decide) paramOfEquiv

open Transfer in
/-- `paramOfEquiv : Param map3 map2b` weakens to `Param map1 map0`
    (forward `map3 → map1`; backward `map2b → map0`). -/
def equivAsMap1Map0 {A α : Type u} [ReprEquivClass A α] : Param .map1 .map0 A α :=
  Param.weaken (by decide) (by decide) paramOfEquiv

/-! ## Tie to the minimal-level solver

The general "synthesize-high, use-low" statement: any witness at `(m, n)`
supplies one at every lattice-lower target `(m', n')`. A level resolver thus
synthesizes at the strongest level available and applies `Param.weaken` to land
at the minimal level a goal requires; the `⊑` premises are decidable
(`MapClass.le` is `Bool`-valued), so each landing is a `by decide`. -/

/-- Synthesize-high, use-low. Given a witness at `(m, n)` and any target
    `(m', n')` lattice-below it, `Param.weaken` supplies the target witness. This
    is the downward half of the level solver. -/
theorem weaken_lands_below {m m' n n' : MapClass} {A B : Type u}
    (hm : m' ⊑ m) (hn : n' ⊑ n) (p : Param m n A B) :
    Nonempty (Param m' n' A B) :=
  ⟨p.weaken hm hn⟩

/-- The minimal common forward level of two witnesses is reachable from either by
    weakening: `meet` (the GLB from `ParamLevel`) is a lattice lower bound, so
    `Param.weaken` can bring any `(m, n)` witness down to `(meet m m₂, n)`. This
    connects the meet (least common level) to the weakening that realizes it. -/
example {m m₂ n : MapClass} {A B : Type u} (p : Param m n A B) :
    Param (MapClass.meet m m₂) n A B :=
  p.weaken (MapClass.meet_le_left m m₂) (MapClass.le_refl n)

end Transfer.Param
