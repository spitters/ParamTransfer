/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Synthesis.ParamSynth
import Transfer.Hierarchy.ParamEquiv

/-!
# The coercion integration (`Param` witness → `Coe`)

This module derives a Lean `Coe`/`CoeTC` from a `Param` witness by extracting
its **forward map**, so a representation change occurs during elaboration:
writing `(a : B)` for `a : A` inserts the transfer's forward map automatically.
This is the Lean analogue of Coq-Trocq's coercion fallback, realized through
Lean's *per-pair* `Coe`/`CoeTC` instance mechanism rather than
a general "expected-X-got-Y → run-a-tactic" hook (see the Scope note below).

The building blocks:

* `Param.fwdMap` projects the forward function `A → B` out of any
  `Param .map1 n A B` (and `Param.fwdMapOfMap3` does the same from a `.map3`
  forward witness, via the `ParamHierarchy.lean` forget chain). Every level
  `≥ map1` carries the `map` field, so this is total on the relevant fragment.
* `coeOfParam` is the same forward function, named for its coercion role.
* `coeTCOfHasParam` is a **scoped** blanket `CoeTC A B` derived from a
  synthesized `HasParam .map1 .map1 A B` witness.

## Scope

Lean 4 has **no general coercion *fallback* hook** — there is no analogue of
Coq-Elpi's `CoercionFallbackTactic`, i.e. no "when the expected type is `X` but
the term has type `Y`, run this tactic to bridge them" entry point. Coercion in
Lean is driven entirely by registered `Coe`/`CoeTC`/`CoeHead`/`CoeTail`
instances keyed on the specific `(A, B)` pair, resolved by the instance cache.
So the realization here is necessarily **per-`(A, B)` instances derived from
`Param` witnesses**, not a single catch-all tactic the elaborator calls.

Two consequences worth stating plainly:

* **Only the forward map survives.** A coercion is *just a function*
  `A → B`; inserting it discards the `Param` relation's relatedness *proof*
  (`map_in_R` / `R_in_map`). The coercion says "here is a `B`", not "here is a
  `B` provably related to the original `A`". To *also* carry the relatedness —
  e.g. to rewrite a goal mentioning `a : A` into the related goal over `B` and
  keep the equivalence — you must use the transfer tactic (`transfer!` /
  `synth_param` and the `Param`-translation machinery in this directory), not a
  plain coercion.
* **The blanket instance is scoped, not global.** A *global* blanket
  `[HasParam .map1 .map1 A B] : CoeTC A B` is dangerous: with `idHasParam`
  giving `HasParam .map1 .map1 A A` for *every* `A`, and `arrowHasParam`
  recursing through `→`, an always-on instance invites the coercion resolver to
  attempt `HasParam` synthesis on every type-mismatch site (over-applying, and
  re-entrant search through the arrow rule). It is `scoped` so it is only
  active where a module explicitly `open`s this namespace and opts in; the
  trade-off is opt-in convenience vs. global safety. A *specific* `Coe`
  (`coeNatWrap` below) is the safest form when a single pair is wanted.
-/

set_option autoImplicit false
-- The `Param.*` accessors live in the `Param` namespace by design (dot-notation
-- on the `Param` structure), giving the intentional `Param.Param.*` shape.
set_option linter.dupNamespace false

universe u

namespace Transfer.Param

/-! ## The forward-map extractor

Every `Map_k.Has R` with `k ≥ map1` carries a `map : A → B` field. `MapHas .map1 R`
reduces (by the defining `match`) to `Map1Has R`, so `p.fwd.map` typechecks
directly for a `.map1` forward witness. -/

/-- The forward map of a `Param .map1 n A B` — the function the relation's
    forward direction encodes. -/
def Param.fwdMap {n : MapClass} {A B : Type u} (p : Param .map1 n A B) : A → B :=
  p.fwd.map

/-- The forward map of a `.map3` forward witness, obtained by forgetting down to
    `map1` (`Map3Has.toMap2a.toMap1`). Lets an embedding's `Param .map3 .map0`
    (e.g. `paramOfEmbedding`) feed the coercion machinery directly. -/
def Param.fwdMapOfMap3 {n : MapClass} {A B : Type u} (p : Param .map3 n A B) : A → B :=
  p.fwd.toMap2a.toMap1.map

/-! ## A coercion function from a `Param` witness -/

/-- The forward map of a `Param .map1 n A B`, named for its role as the function
    underlying a derived coercion `A → B`. Definitionally `Param.fwdMap`. -/
def coeOfParam {n : MapClass} {A B : Type u} (p : Param .map1 n A B) : A → B :=
  p.fwdMap

/-! ## Deriving `Coe`/`CoeTC` from a `Param` witness

### Scoped blanket (opt-in)

A `CoeTC A B` for any pair carrying a synthesized `HasParam .map1 .map1 A B`.
`scoped` so it only fires where a module `open`s this namespace — see the Scope
note for why a global version over-fires. -/

/-- Scoped blanket coercion: derive `CoeTC A B` from a `HasParam .map1 .map1 A B`
    witness by inserting its forward map. Active only under
    `open scoped Transfer.Param`. -/
scoped instance coeTCOfHasParam {A B : Type u} [HasParam .map1 .map1 A B] : CoeTC A B where
  coe a := coeOfParam (HasParam.param : Param .map1 .map1 A B) a

/-! ## Demo: a concrete pair + elaboration-time transfer

A safe, self-contained demonstration that does not rely on the scoped blanket:
a hand-built `Param .map1 .map0` whose forward map is the wrapper constructor,
turned into a specific `Coe`. -/

/-- A demo target type for the coercion. -/
structure Wrap where
  /-- The wrapped natural number. -/
  val : Nat

/-- A `Param .map1 .map0 Nat Wrap`: forward map is `Wrap.mk` (graph relation),
    no backward structure. -/
def natWrapParam : Param .map1 .map0 Nat Wrap where
  R := fun a b => Wrap.mk a = b
  fwd := ⟨Wrap.mk⟩
  bwd := ⟨⟩

/-- A *specific* coercion `Nat → Wrap` derived from `natWrapParam` (the safe,
    non-blanket form). -/
instance coeNatWrap : Coe Nat Wrap where
  coe := coeOfParam natWrapParam

/-- Elaboration-time transfer via the specific `Coe`: a `Nat` is accepted where a
    `Wrap` is expected; the `Param`'s forward map (`Wrap.mk`) is inserted by the
    elaborator. -/
example (a : Nat) : Wrap := a

/-- The inserted coercion is exactly the `Param` forward map. -/
example (a : Nat) : ((a : Wrap)) = Wrap.mk a := rfl

/-! ### Demo of the scoped blanket on a cross-type witness

To show the *blanket* itself applies (not the specific `coeNatWrap`), this demo
uses a fresh pair `Boxed`/`Nat` that has only a `HasParam .map1 .map1` witness and
no hand-written `Coe`. With the namespace open, `(b : Nat)` for `b : Boxed`
resolves through `coeTCOfHasParam`. -/

/-- A second demo source type, distinct from `Wrap`, with no specific `Coe`. -/
structure Boxed where
  /-- The boxed natural number. -/
  contents : Nat

/-- A diagonal-fragment witness `HasParam .map1 .map1 Boxed Nat`: forward map
    `Boxed.contents`, backward map `Boxed.mk`. -/
instance hasParamBoxedNat : HasParam .map1 .map1 Boxed Nat where
  param :=
    { R := fun a b => Boxed.contents a = b
      fwd := ⟨Boxed.contents⟩
      bwd := ⟨Boxed.mk⟩ }

section ScopedDemo
open scoped Transfer.Param

/-- With the scoped blanket open, the `HasParam` witness drives the coercion:
    a `Boxed` is accepted where `Nat` is expected, transfer (its forward map
    `Boxed.contents`) inserted at elaboration time. -/
example (b : Boxed) : Nat := b

/-- The inserted coercion is the `HasParam` witness's forward map. -/
example (b : Boxed) : ((b : Nat)) = b.contents := rfl

end ScopedDemo

end Transfer.Param
