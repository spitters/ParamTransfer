/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Congruence.RCongr
import Transfer.Integrations.GrindIntegration

/-!
# `param_cc` — relational congruence closure over `Related`

`rcongr` (`RCongr.lean`) is *goal-directed* relational descent: it peels a
cross-head op-tree `Related enc (op a b) (bop a' b')` one congruence layer at a
time and dispatches each leaf to instance resolution. Two things it does not
do, which a congruence-closure (SMT-style) procedure must:

* Saturate. It descends the goal but never *derives* new relatedness facts
  by composing the facts it already has. A goal whose proof needs a hypothesis
  chained through a congruence step that is itself off the descent spine is out
  of reach.
* Use transitivity. Its leaf closer is `exact inferInstance | rfl`. Local
  hypotheses of class type `Related enc a b` are usable there (Lean treats a
  class-typed hypothesis as a *local instance*), so a leaf that matches a
  hypothesis *syntactically* closes — but a leaf reachable only by **chaining
  an equation through the relation** (`Related enc a c` plus `c = b ⊢
  Related enc a b`) does not: `inferInstance` keys on the syntactic `b`, and
  `rfl` cannot bridge `c`–`b`.

`param_cc` is the saturating, context-incorporating analogue: the set-level,
univalence-free Lean counterpart of the Emil Gjørup–Spitters *cubical*
congruence closure (which runs the same congruence/transitivity/reflexivity
closure over `PathP` with a union-find equivalence graph). Here it runs over the
Trocq `Related`/`RelatedBinOp` relation instead of paths.

## What `param_cc` does

The `Related` relation is an encoding equation:
`Related enc a b := (enc a = b)`. Over such a relation, relational congruence
closure *reduces to ordinary congruence closure on the `enc`-images*:

* the **congruence rule** `composeBinOp`/`rcongrBinOp`
  (`enc (op a b) = bop (enc a) (enc b)`, the `RelatedBinOp` square) becomes a
  rewrite among `enc`-equations;
* **transitivity** and **symmetry** of `Related` are exactly transitivity and
  symmetry of `=` on the `enc`-images;
* **reflexivity** (`leaf`/`leafId`) is `rfl`.

So the whole closure is dischargeable by an *equational* congruence-closure
engine once the relation is unfolded to its equation and the available squares /
hypotheses are presented as equations. `grind` is that engine.

Concretely, `param_cc`:

1. scans the local context and, for every hypothesis `h : Related enc a b`,
   surfaces its underlying equation `h.rel : enc a = b`; for every
   `h : RelatedBinOp enc op bop`, surfaces its commuting square
   `h.comm : ∀ x y, enc (op x y) = bop (enc x) (enc y)`. (Registered global
   `RelatedBinOp` squares — e.g. the Baby Bear field squares dual-tagged
   `@[grind =]` in `GrindIntegration.lean` — are already in `grind`'s database,
   so the *registered* leaf facts need no surfacing.)
2. reduces the goal `Related enc s t` to its equation `enc s = t` (constructor),
   leaving a goal already in `=`-form when the goal was an equation;
3. closes by `grind`, whose congruence closure now composes the squares and the
   surfaced hypothesis-equations transitively to a fixpoint.

This is the realization: relational-CC over the encoding relation =
equational-CC on the `enc`-images, dischargeable by `grind`. The saturation
(deriving facts to a fixpoint), the transitivity, and the context-hypothesis
incorporation are all performed by `grind`'s congruence-closure core; the
tactic's job is the relation→equation translation that makes the closure
visible to it.

## What this does that `rcongr` cannot

Two demos below are out of `rcongr`'s reach:

* a transitivity goal — `Related enc a b` from `Related enc a c` and a
  separate `c = b` link — where `rcongr`'s `inferInstance | rfl` leaf fails
  (pinned with `#guard_msgs`);
* a saturating congruence over context hypotheses — a two-level op-tree
  whose operands are bare local variables related to their images only by
  context hypotheses, with one registered leaf — which needs the congruence
  rule *and* the hypotheses chained together.

## Scope and residual

`param_cc` handles the encoding-relation case, where `Related` unfolds to an
equation and the closure collapses onto ordinary congruence closure. The
remaining case is a relation-generic closure — a union-find over an
equivalence graph for relations that are *not* encoding-equations (where there
is no `=` to reduce to, so transitivity/symmetry must be supplied as relation
lemmas and the congruence rule applied directly over the graph). That is the
full Emil-style procedure; over a non-equational relation `grind` cannot stand
in for it. The present tactic is the set-level, equational specialization that
the Trocq `Related` relation admits.
-/

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField
open Lean Elab Tactic Meta

/-- Relational congruence-closure core. Saturating, context-incorporating
    closure of a `Related enc s t` (or `=`) goal:

1. For every local hypothesis `h : Related enc a b`, assert its equation
   `h.rel : enc a = b`; for every `h : RelatedBinOp enc op bop`, assert its
   commuting square `h.comm`. These become facts for the closure engine.
2. Reduce a `Related enc s t` goal to the equation `enc s = t` (constructor); an
   already-`=` goal is left as is.
3. Close by `grind`, whose congruence closure composes the surfaced equations
   and the registered (`@[grind =]`) squares transitively to a fixpoint.

Over the encoding relation this is exactly relational congruence closure:
congruence (the squares), transitivity/symmetry (`=` on `enc`-images), and
reflexivity (`rfl`) are all realized by the equational closure. -/
def paramCCCore : TacticM Unit := withMainContext do
  -- Phase 1: surface relatedness facts from the local context as equations.
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    if ty.isAppOf ``Related then
      let pf ← mkAppOptM ``Related.rel #[none, none, none, none, none, some ldecl.toExpr]
      let eqTy ← inferType pf
      liftMetaTactic fun mv => do
        let mv' ← mv.assert (← mkFreshUserName `hrel) eqTy pf
        let (_, mv'') ← mv'.intro1
        return [mv'']
    else if ty.isAppOf ``RelatedBinOp then
      let pf ← mkAppOptM ``RelatedBinOp.comm #[none, none, none, none, none, some ldecl.toExpr]
      let eqTy ← inferType pf
      liftMetaTactic fun mv => do
        let mv' ← mv.assert (← mkFreshUserName `hcomm) eqTy pf
        let (_, mv'') ← mv'.intro1
        return [mv'']
  -- Phase 2 + 3: reduce a `Related` goal to its equation, then close by closure.
  withMainContext do
    let tgt ← instantiateMVars (← getMainTarget)
    if tgt.isAppOf ``Related then
      evalTactic (← `(tactic| refine ⟨?_⟩))
    evalTactic (← `(tactic| grind))

/-- The `param_cc` tactic — relational congruence closure over `Related`.

`param_cc` is `grind` plus a relation→equation prelude: it surfaces the
relatedness facts as `enc`-equations and lets `grind`'s congruence-closure core
do the saturation. `param_solve` (`ParamSolve.lean`) is the unified entry point
that uses this closure as the leaf discharger under cross-head descent
(`rcongr`/`hgcongr`); this tactic and its demos remain the standalone closure and
the witness that `rcongr` cannot close a pure transitivity goal (the
`#guard_msgs` rejection below).

Closes a `Related enc s t` (or its underlying `enc s = t`) goal by saturating
the available relatedness facts — registered `Related`/`RelatedBinOp` instances
**and** context hypotheses of relatedness type — under congruence, transitivity,
and reflexivity, to a fixpoint. Unlike the goal-directed `rcongr`, it
incorporates context hypotheses chained through congruence steps and closes
transitivity goals. See the module docstring for the realization (relational-CC
over the encoding relation = equational-CC on the `enc`-images, run by `grind`)
and the relation-generic residual. -/
elab "param_cc" : tactic => paramCCCore

/-! ## Demonstrations

### 1. Transitivity — the leaf `rcongr` cannot close

`Related enc a b` from `Related enc a c` (hypothesis) and a separate `c = b`
link. `param_cc` surfaces `hac.rel : enc a = c`, reduces the goal to
`enc a = b`, and `grind` chains it through `hcb : c = b`. -/

/-- Transitivity, by `param_cc`. The relation is closed under transitivity
    via the underlying `enc a = c`, `c = b` equations. -/
example {A α : Type} (enc : A → α) (a : A) (c b : α)
    (hac : Related enc a c) (hcb : c = b) :
    Related enc a b := by param_cc

/-! `rcongr` cannot close the same goal. Its leaf closer is
`exact inferInstance | rfl`: `inferInstance` keys on the syntactic `b` (the
local instance `hac` has image `c`, not `b`), and `rfl` cannot bridge the
`c`–`b` link. The `#guard_msgs` pins the `rfl` failure. -/

/--
error: Tactic `rfl` failed: The left-hand side
  a
is not definitionally equal to the right-hand side
  b

A α : Type
enc : A → α
a : A
c b : α
hac : Related enc a c
hcb : c = b
⊢ Related enc a b
-/
#guard_msgs (error) in
example {A α : Type} (enc : A → α) (a : A) (c b : α)
    (hac : Related enc a c) (hcb : c = b) :
    Related enc a b := by rcongr

/-! ### 2. Saturating congruence over context hypotheses

A two-level op-tree `op (op x y) z` whose operands `x`, `y` are bare local
variables related to their images `x'`, `y'` *only* by context hypotheses
`hx`, `hy`, with `z` related to `z'` by a third hypothesis. The proof needs the
congruence rule (the `RelatedBinOp` square) **and** all three hypotheses
composed — i.e. saturation. `param_cc` surfaces `hop.comm` and the three
`h*.rel` equations, then `grind` composes them. -/

/-- Saturating congruence + context hyps, by `param_cc`. The square
    `hop.comm` and the hypothesis equations `enc x = x'`, `enc y = y'`,
    `enc z = z'` are composed by `grind` through both op layers. -/
example {A α : Type} (enc : A → α) (op : A → A → A) (bop : α → α → α)
    [hop : RelatedBinOp enc op bop]
    (x y : A) (x' y' : α) (z : A) (z' : α)
    (hx : Related enc x x') (hy : Related enc y y')
    (hz : Related enc z z') :
    Related enc (op (op x y) z) (bop (bop x' y') z') := by param_cc

/-! ### 3. Registered squares — the Baby Bear field

With no context hypotheses at all: the registered `@[grind =]` Baby Bear field
squares (`mul_repr`/`add_repr`, dual-tagged in `GrindIntegration.lean`) live in
`grind`'s database, so `param_cc` closes the composite directly. This is the
`Related.lean`/`rcongr` payoff obtained through the closure engine. -/

/-- Registered-square composite, by `param_cc`. The closure uses only the
    globally registered squares. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_cc

/-- Larger registered composite. The closure scales without positional
    rewrite control. -/
example (a b c d e f : F) :
    (a * b + c * d) * (e + f)
      = bbFieldMul (bbFieldAdd (bbFieldMul a b) (bbFieldMul c d)) (bbFieldAdd e f) := by
  param_cc

/-! ### 4. Combined: registered squares + context relatedness + transitivity

A goal mixing all three closure ingredients — a registered field square, a
context relatedness hypothesis, and a transitivity link — to show the closure
saturates over the whole fact set at once. -/

/-- Mixed closure, by `param_cc`. `hp : Related id p (a * b)` (context) is
    chained through the registered `*`-square and the transitivity link
    `q = bbFieldMul a b` to reach the goal image. -/
example (a b p : F) (q : F)
    (hp : Related (id : F → F) p (a * b)) (hq : a * b = q) :
    Related (id : F → F) p q := by param_cc

/-! ### Named witnesses (for axiom-hygiene verification) -/

/-- Named transitivity demo (axiom-hygiene witness for `param_cc`). -/
theorem param_cc_trans_demo {A α : Type} (enc : A → α) (a : A) (c b : α)
    (hac : Related enc a c) (hcb : c = b) :
    Related enc a b := by param_cc

/-- Named saturating-congruence demo (axiom-hygiene witness for `param_cc`). -/
theorem param_cc_saturate_demo {A α : Type} (enc : A → α)
    (op : A → A → A) (bop : α → α → α) [RelatedBinOp enc op bop]
    (x y : A) (x' y' : α) (z : A) (z' : α)
    (hx : Related enc x x') (hy : Related enc y y')
    (hz : Related enc z z') :
    Related enc (op (op x y) z) (bop (bop x' y') z') := by param_cc

end Transfer
