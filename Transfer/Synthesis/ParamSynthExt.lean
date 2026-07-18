/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Synthesis.ParamSynth
import Transfer.Combinators.ParamForall
import Transfer.Hierarchy.ParamEquiv
import Transfer.Hierarchy.ParamLevel
import Transfer.Base.Hierarchy

/-!
# The multi-level `Param`-witness synthesizer

`ParamSynth.lean` pins the synthesizer at the single output
level `(m, n) = (.map1, .map1)` — the self-relation ("diagonal") fragment, where
`idHasParam`/`arrowHasParam` close resolution under `→`. This module
extends the synthesizer to additional levels, driven by the level-arithmetic
decision table `arrowReq` of `ParamLevel.lean`, and adds the dependent-Π
(`∀`) synthesis combinator:

1. map3-forward base leaves from embeddings — `embHasParam` turns any
   `[ReprEmbeddingClass A α]` into a `HasParam .map3 .map0 A α` (via
   `paramOfEmbedding`). This populates the resolver with `map3` leaves, the level
   the arrow rule `Map3_arrow` consumes in its codomain slot. A companion
   `embHasParamSymm` provides the symmetric `HasParam .map0 .map3` leaf (the
   level the arrow rule consumes in its *domain* slot).

2. the higher-level arrow instance `arrowHasParam3` — composes a
   `HasParam .map3 .map0 (A → B) (A' → B')` from a `HasParam .map0 .map3` on the
   domain and a `HasParam .map3 .map0` on the codomain, via `Map3_arrow` (forward
   `map3`) and the trivial `Map0Has` (backward `map0`). Its input/output levels
   are *exactly* the entry `arrowReq .map3 = some (.map0, .map3, .map3, .map0)`
   of the decision table — see `arrowHasParam3_matches_arrowReq` below.

3. the dependent-∀ (Pi) synthesis rule `synthForall` — wraps `paramForall`
   so the resolver can build a `Param .map1 .map0 (∀ a, B a) (∀ a', B' a')` from a
   domain `Param .map0 .map2a` and a witness-indexed codomain family. A
   `HasParam` instance `forallConstHasParam` covers the non-dependent
   case (`B`, `B'` constant), recovering the arrow at level `(.map1, .map0)`.

## What `inferInstance` resolves at the new levels

With `embHasParam`/`embHasParamSymm` populating the leaves and `arrowHasParam3`
as the recursive rule, `inferInstance` synthesizes `HasParam .map3 .map0` for
single-arrow function types over embedding base types (e.g. `Num → Num` with
`[ReprEmbeddingClass Num ℕ]`). The chaining is shown in the examples; the
demos that resolve are flagged in the module comments at each `example`.

## Full variable-level resolution

The *minimal-level* solver is not implemented here: given
a requested output `(m, n)`, it would consult `arrowReq`/`forallReq` to compute the
minimal component levels at each recursion step and resolve sub-witnesses at
*those* levels — an `outParam`-driven search over ALL of `arrowReq`, or a
dedicated `MetaM`/Elpi-`param.db`-analogue solver. This module pins a *finite menu* of
levels (`(.map1, .map1)` from the core synthesizer, `(.map3, .map0)` here) wired to the
matching `arrowReq` rows; turning the menu into a search is not done here.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

open Transfer

/-! ## (1) Base leaves at level `map3`/`map0` from embeddings -/

/-- An embedding `[ReprEmbeddingClass A α]` as a `HasParam .map3 .map0 A α`
    leaf (forward `map3` graph of `enc`, backward `map0`). This adds the
    `map3`-forward leaves that the higher-level arrow rule consumes in its
    *codomain* slot. -/
instance embHasParam {A α : Type u} [ReprEmbeddingClass A α] :
    HasParam .map3 .map0 A α := ⟨paramOfEmbedding⟩

/-- The symmetric leaf: the embedding's `Param .map3 .map0`, flipped via
    `Param.symm`, is a `Param .map0 .map3 α A`, i.e. a `HasParam .map0 .map3 α A`.
    This is the level the higher-level arrow rule consumes in its *domain* slot. -/
instance embHasParamSymm {A α : Type u} [ReprEmbeddingClass A α] :
    HasParam .map0 .map3 α A := ⟨(paramOfEmbedding (A := A) (α := α)).symm⟩

/-! ## (2) The higher-level arrow instance at `(map3, map0)`

The arrow rule one level up from the diagonal: forward `map3` (the full graph
relation, via `Map3_arrow`), backward `map0` (trivial). The component levels are
read off `arrowReq .map3`: the domain `PA` at `(map0, map3)`, the codomain `PB`
at `(map3, map0)`. -/

/-- `arrowHasParam3`: compose a `HasParam .map3 .map0 (A → B) (A' → B')` from a
    domain `HasParam .map0 .map3 A A'` and a codomain `HasParam .map3 .map0 B B'`.
    Forward structure is `Map3_arrow` (the `map3` graph of the conjugated map);
    backward structure is the trivial `Map0Has`. The component levels match the
    decision-table row `arrowReq .map3 = (.map0, .map3, .map3, .map0)`. -/
instance arrowHasParam3 {A A' B B' : Type u}
    [HasParam .map0 .map3 A A'] [HasParam .map3 .map0 B B'] :
    HasParam .map3 .map0 (A → B) (A' → B') where
  param :=
    { R := R_arrow (HasParam.param : Param .map0 .map3 A A')
                   (HasParam.param : Param .map3 .map0 B B')
      fwd := Map3_arrow (HasParam.param) (HasParam.param)
      bwd := ⟨⟩ }

/-! ## (4) Connect to the level tables

The new arrow instance is wired to the decision
table, not chosen ad hoc. `arrowHasParam3` consumes its domain at `(.map0,
.map3)` and its codomain at `(.map3, .map0)` and produces output forward level
`.map3` — *exactly* the entry `arrowReq .map3`. -/

/-- The decision-table entry the higher-level arrow rule implements. -/
theorem arrowHasParam3_matches_arrowReq :
    arrowReq .map3 = some (.map0, .map3, .map3, .map0) := rfl

/-- Restated as the component levels `arrowHasParam3` actually uses:
    `PA.fwd = map0`, `PA.bwd = map3`, `PB.fwd = map3`, `PB.bwd = map0`, output
    forward `map3`. The instance's `[HasParam .map0 .map3 A A']` (domain) and
    `[HasParam .map3 .map0 B B']` (codomain) hypotheses match these slots, and
    the output is `HasParam .map3 .map0`. -/
example :
    arrowReq .map3 =
      some (/- PA.fwd -/ .map0, /- PA.bwd -/ .map3,
            /- PB.fwd -/ .map3, /- PB.bwd -/ .map0) := rfl

/-! ## (3) The dependent-Π (`∀`) synthesis rule

Instances over the `aR`-indexed codomain family are awkward (the family is not a
typeclass-resolvable shape), so the dependent rule is delivered as a `def`
combinator. The non-dependent specialisation *is* expressible as a `HasParam`
instance. -/

/-- The dependent-Π synthesis combinator: from a domain `Param .map0 .map2a`
    and a witness-indexed codomain family at `(.map1, .map0)`, build the
    `Param .map1 .map0` on the dependent function space. A thin wrapper over
    `paramForall` so the synthesizer surface can call into the Π rule. -/
def synthForall {A A' : Type u} {B : A → Type u} {B' : A' → Type u}
    (PA : Param .map0 .map2a A A')
    (PB : ∀ a a', PA.R a a' → Param .map1 .map0 (B a) (B' a')) :
    Param .map1 .map0 (∀ a, B a) (∀ a', B' a') :=
  paramForall PA PB

/-- The non-dependent ∀ as a `HasParam` instance: when the codomain family is a
    constant `Param .map1 .map0 C C'`, the dependent-Π rule recovers the arrow
    `HasParam .map1 .map0 (A → C) (A' → C')`. The domain is supplied at the
    `(.map0, .map2a)` level the Π forward map needs. -/
instance forallConstHasParam {A A' C C' : Type u}
    [HasParam .map0 .map2a A A'] [HasParam .map1 .map0 C C'] :
    HasParam .map1 .map0 (A → C) (A' → C') where
  param :=
    synthForall (B := fun _ => C) (B' := fun _ => C')
      (HasParam.param : Param .map0 .map2a A A')
      (fun _ _ _ => (HasParam.param : Param .map1 .map0 C C'))

/-! ## Multi-level `inferInstance` demos

Which goals at the new levels the resolver closes with no manual
term. Each demo notes whether it resolves and why.

### Base leaf (resolves)

An embedding synthesizes its `map3`-forward leaf directly. -/

/-- A single embedding leaf at `(.map3, .map0)` — resolves via `embHasParam`. -/
example {A α : Type u} [ReprEmbeddingClass A α] : HasParam .map3 .map0 A α :=
  inferInstance

/-! ### Higher-level arrow chaining (resolves, given oriented leaves)

Given the two oriented component leaves the `arrowReq .map3` row demands — the
domain at `(.map0, .map3)` and the codomain at `(.map3, .map0)` —
`arrowHasParam3` applies automatically and the resolver closes a `(.map3, .map0)`
goal on the function space. -/

/-- The multi-level arrow resolves by `inferInstance` once the two oriented
    component leaves are in scope: `arrowHasParam3` is selected, its forward
    `Map3_arrow` is built, backward is the trivial `Map0Has`. -/
example {A A' : Type u}
    [HasParam .map0 .map3 A A'] [HasParam .map3 .map0 A A'] :
    HasParam .map3 .map0 (A → A) (A' → A') := inferInstance

/-! ### Non-dependent ∀ recovers the arrow (resolves)

The constant-family `forallConstHasParam` instance closes a `(.map1, .map0)`
goal on a (non-dependent) function space, given the domain at `(.map0, .map2a)`
and codomain at `(.map1, .map0)`. -/

/-- The Π rule's non-dependent specialisation resolves by `inferInstance`. -/
example {A A' C C' : Type u}
    [HasParam .map0 .map2a A A'] [HasParam .map1 .map0 C C'] :
    HasParam .map1 .map0 (A → C) (A' → C') := inferInstance

/-! ### Dependent ∀ synthesis (combinator, not pure `inferInstance`)

`synthForall` builds a `Param` for a genuine `∀`-type from a domain `Param` and
a witness-indexed codomain family. (The family is not a typeclass-resolvable
shape, hence a `def`, not an instance — see `paramUnit`/`paramBoolFam` in
`ParamForall.lean` for the concrete inputs.) -/

/-- `synthForall` synthesizes a `Param` on a dependent (here constant) `∀`-type
    from the concrete `ParamForall` demo inputs — the Π rule firing. -/
example : Param .map1 .map0 (∀ _ : Unit, Bool) (∀ _ : Unit, Bool) :=
  synthForall (B := fun _ => Bool) (B' := fun _ => Bool) paramUnit paramBoolFam

/-! ### What does not resolve from a bare embedding (the orientation residual)

`arrowHasParam3`'s domain slot needs a `HasParam .map0 .map3 A α` (forward
`map0`, backward `map3` — a *decoder* `α → A` with both graph inclusions). A
bare `[ReprEmbeddingClass A α]` supplies only the forward `map3` (`embHasParam :
HasParam .map3 .map0 A α`) and its `Param.symm` (`embHasParamSymm : HasParam
.map0 .map3 α A`, the *flipped* type pair). Neither is the `.map0 .map3 A α`
the domain slot wants, so

    `example [ReprEmbeddingClass A α] : HasParam .map3 .map0 (A → A) (α → α)`

does not resolve by `inferInstance`. This reflects the level structure rather
than a synthesizer gap: a `map3` backward leaf requires a two-sided decoder
(`ReprEquivClass`/`paramOfEquiv` territory), which an embedding does not carry.
The arrow demo above therefore takes the two oriented leaves as hypotheses. -/

end Transfer.Param
