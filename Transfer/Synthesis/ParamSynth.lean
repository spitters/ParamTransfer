/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Combinators.ParamArrow

/-!
# The `Param`-witness synthesizer

This module is the Lean-idiomatic analogue of Trocq's Elpi logic-program search
(`coq-community/trocq`, the `param.db` / `solve` Elpi predicates): it composes
`Param` annotated relations for closed type structure by typeclass
resolution. Where Trocq drives an Elpi program that, given a goal type, picks
the parametricity combinator (`app` / arrow / `∀`) and recurses on the
subterms, here the Lean instance resolver plays exactly that role — the
combinators (`paramArrow`, …) become `instance`s, and `inferInstance` performs
the search.

## What this synthesizer does (and at what level)

This synthesizer works at a fixed target level `(m, n) = (.map1, .map1)`: the
self-relation ("diagonal") fragment of the lattice, where every component carries
a forward and a backward map and nothing else. At this level:

* `idHasParam` is the base case — the diagonal `Param .map1 .map1 A A` with
  `R := Eq`, forward and backward maps `id` (the leaf rule of `⟦·⟧`);
* `arrowHasParam` is the recursive `app`/function rule — it composes a `Param`
  on `A → B` from `Param`s on `A` and `B` via `paramArrow`.

Because `paramArrow` consumes and produces `Param .map1 .map1`, these two
instances close under function-space formation: the resolver synthesizes a
witness for any closed type built from base types by `→` (including curried
multi-argument functions and higher-order arguments), with no manual proof.
This is the `app`/arrow rule of the translation `⟦·⟧`, applied automatically.

## The minimal-`(m, n)` level solver

The minimal-level solver, which this module does not build, is the
variant where the output level `(m, n)` is not
fixed but searched for, subject to the per-combinator level arithmetic the
arrow combinators encode. Recall (from `ParamArrow.lean`) that each arrow
level consumes *different* component levels:

| output | needs `PA` (domain, backward) | needs `PB` (codomain, forward) |
|---|---|---|
| `Map1_arrow` | `Param .map0 .map1` | `Param .map1 .map0` |
| `Map2a_arrow` | `Param .map0 .map2b` | `Param .map2a .map0` |
| `Map2b_arrow` | `Param .map0 .map2a` | `Param .map2b .map0` |
| `Map3_arrow`  | `Param .map0 .map3`  | `Param .map3 .map0`  |

So a full solver must, given a *requested* output `(m, n)`, compute the
*minimal* component levels at each recursion step (the level-meet / lattice
order of `ParamHierarchy.lean`'s weakening maps) and resolve sub-witnesses at
*those* levels. That needs either `outParam` level inference with a Prolog-style
level-arithmetic relation, or a dedicated `MetaM` solver (the Elpi
`param`-database analogue). This module pins the
fixed-`(map1, map1)` specialization, which is sound and automates the
function-rule composition.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

/-! ## The resolvable class -/

/-- `HasParam m n A B`: a typeclass carrying a `Param m n A B` witness. The
    level indices `(m, n)` are explicit (not `outParam`), so resolution
    runs at a *fixed* target level — the analogue of asking Trocq's Elpi search
    for a witness at a pinned annotation. The fixed level used by the base and
    arrow instances below is `(.map1, .map1)`, the self-relation fragment. -/
class HasParam (m n : MapClass) (A B : Type u) where
  param : Param m n A B

/-! ## Base instance: the identity / diagonal -/

/-- The diagonal base case (leaf rule of `⟦·⟧`): the equality relation on `A`
    as a `Param .map1 .map1 A A`, with forward and backward maps `id`. Built
    directly here so resolution has a self-relation witness for every closed
    base type. -/
instance idHasParam (A : Type u) : HasParam .map1 .map1 A A where
  param :=
    { R := Eq
      fwd := ⟨id⟩
      bwd := ⟨id⟩ }

/-! ## The recursive `app` / arrow instance -/

/-- The `app`/function rule as an instance: given self-relation witnesses on the
    domain `A`/`A'` and codomain `B`/`B'`, compose a `Param .map1 .map1` on the
    function space via `paramArrow`. With `idHasParam`, this closes resolution
    under `→`, so curried and higher-order function types synthesize
    automatically. -/
instance arrowHasParam {A A' B B' : Type u}
    [HasParam .map1 .map1 A A'] [HasParam .map1 .map1 B B'] :
    HasParam .map1 .map1 (A → B) (A' → B') where
  param := paramArrow (HasParam.param) (HasParam.param)

/-! ## Auto-synthesis with no manual proof

The resolver composes the curried/higher-order arrow witnesses purely from
`arrowHasParam` + `idHasParam`. None of the examples below write a `Param` term
by hand. -/

/-- A two-argument curried function type: resolution applies `arrowHasParam`
    twice and `idHasParam` thrice. -/
example : HasParam .map1 .map1 (Nat → Nat → Nat) (Nat → Nat → Nat) := inferInstance

/-- A higher-order argument `(Nat → Bool) → Nat`: the domain is itself a
    function type, so `arrowHasParam` recurses into it. -/
example : HasParam .map1 .map1 ((Nat → Bool) → Nat) ((Nat → Bool) → Nat) := inferInstance

/-- Heterogeneous base types in a three-deep curry. -/
example : HasParam .map1 .map1 (Nat → Bool → String → Nat) (Nat → Bool → String → Nat) :=
  inferInstance

/-- Extracting the underlying `Param` (and hence its relation) from a synthesized
    witness — the relation is `R_arrow` of the component relations, exactly the
    pointwise lift of the leaf equality, with no hand-written term. -/
example :
    ((inferInstance : HasParam .map1 .map1 (Nat → Nat) (Nat → Nat)).param).R
      = R_arrow (HasParam.param : Param .map1 .map1 Nat Nat)
                (HasParam.param : Param .map1 .map1 Nat Nat) := rfl

/-! ## The `synth_param` tactic

A macro that closes a `Param .map1 .map1 _ _` goal by delegating to the
resolver: it asks for the corresponding `HasParam` instance and projects out the
`.param` field. This is the surface command for "synthesize a witness for this
(closed) type", the user-facing analogue of Trocq's automatic generation. -/

/-- Close a `Param .map1 .map1 _ _` goal by typeclass-synthesizing the
    corresponding `HasParam` witness and projecting `.param`. -/
macro "synth_param" : tactic =>
  `(tactic| exact (inferInstance : HasParam _ _ _ _).param)

/-- Demo: `synth_param` closes a function-type `Param` goal — the witness is
    composed by the resolver, not supplied by the user. -/
example : Param .map1 .map1 (Nat → Nat → Bool) (Nat → Nat → Bool) := by
  synth_param

/-- Demo: it also closes a higher-order goal. -/
example : Param .map1 .map1 ((Bool → Nat) → Bool) ((Bool → Nat) → Bool) := by
  synth_param

end Transfer.Param
