/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.TransferTactic
import Mathlib.Tactic.GCongr

/-!
# `rcongr` — relational (cross-head) congruence descent

`gcongr` is *congruence of one function with varying arguments*: it reduces
`R (f a₁ … aₙ) (f b₁ … bₙ)` to the per-argument goals `Rᵢ aᵢ bᵢ`. Trocq
relatedness is the opposite shape — it relates two different functions, a
source operation `op` and its target realization `bop`, by a registered
commuting square `enc (op x y) = bop (enc x) (enc y)` (`RelatedBinOp`). `gcongr`
cannot descend such a goal (see the gcongr verdict below).

`rcongr` is the relational analogue: a `TacticM` recursion on a goal
`Related enc t t'` (or an `=` bridged to one) that, when `t = op a b` and
`t' = bop a' b'` are linked by a **registered** `RelatedBinOp enc op bop`,
applies the cross-head congruence rule `rcongrBinOp`, leaving the two
per-argument relatedness subgoals `Related enc a a'`, `Related enc b b'`, and
recurses on them — bottoming out at leaves via the registry (`leaf`/`leafId`
instances) and `rfl`. It does for *cross-head* op-trees what `gcongr` does for
single-head ones, driven by the `RelatedBinOp` lemma database.

## Registration mechanism

`rcongr` reuses the existing `RelatedBinOp` instances (the `@[transfer]`-flavoured
square set from `Related.lean`) directly — no new attribute is introduced.
The single generic congruence rule `rcongrBinOp` is parametric over *any*
registered square: the descent applies it with the operands left as `?_`
subgoals and lets instance resolution discharge the `RelatedBinOp` premise
(exactly as `gcongr` discharges its side goals while recursing on the main
ones). Adding a new realized operation is therefore a one-line `instance
… : RelatedBinOp …`, the same registration the ground composer `composeBinOp`
already consumes — `rcongr` and the instance composer share one database.

This is cleaner than a dedicated `@[rcongr]` attribute: the latter would
duplicate the `RelatedBinOp` set under a second key with no added expressive
power, since every cross-head binary square is already a `RelatedBinOp`.

## Relation to `transferCore`

`rcongr` generalizes `transferCore` (`TransferTactic.lean`). `transferCore`
descends on a fixed menu of *goal shapes* — `Iff`-of-`∀` (`forall_congr'`),
`∀`/`→` (`intro`), function equality (`funext`) — and dispatches each whole
*leaf* (a closed first-order equation) to instance resolution in one shot
(`transferLeaf` → `transferGround`), so the cross-head op-tree is collapsed
inside a single `inferInstance`. `rcongr` instead descends *into the op-tree
itself*: it makes the cross-head step a first-class, lemma-driven structural
move (`rcongrBinOp`) with the per-argument relatedness left as recursable
subgoals. The capability is cross-head descent driven by a registered
congruence DB — the thing `gcongr` structurally cannot host. The two are
composable: `transferCore` for the binder/`∀`/`λ` layer, `rcongr` for the
relational op-tree leaf.

## Scope: `gcongr` cannot be made cross-head

`gcongr` cannot be made cross-head through any existing hook.
`Mathlib.Tactic.GCongr.Core` enforces the
single-head constraint at both ends:

* **Registration** (`makeGCongrLemma`): a `@[gcongr]` lemma's conclusion
  `R lhs rhs` is rejected unless `lhsHead == rhsHead && lhsArgs.size ==
  rhsArgs.size` ("LHS and RHS do not have the same head function and arity").
  A `RelatedBinOp`-shaped lemma (`R (op a b) (bop a' b')`, `op ≠ bop`) cannot
  even be tagged.
* **Lookup / descent** (`Lean.MVarId.gcongr`): the runtime loop re-checks
  `lhsHead == rhsHead && lhsArgs.size == rhsArgs.size` before doing anything,
  and the lemma database is keyed by a **single** head — `key := { relName,
  head := lhsHead, arity }`. So even a hypothetically-registered cross-head
  lemma is unreachable: there is no key under which the two heads `op`, `bop`
  could both be found.

The two discharger hooks (`mainGoalDischarger`, `sideGoalDischarger`) fire only
on already-produced *leaf*/side goals, never on the structural descent, so they
offer no cross-head entry point either.

A cross-head `gcongr` would be a Mathlib-level generalization to
heterogeneous (relational) congruence: two heads `f`, `g` linked by a
*registered head correspondence*, with the arguments related pairwise. Concretely
in `makeGCongrLemma`/`Lean.MVarId.gcongr` that means (i) dropping the
`head == head'` requirement and storing both heads in the lemma data and the
lookup key (`GCongrKey` gains a second head, or keys on a registered
`(f, g)` correspondence), and (ii) recursing the per-argument subgoals under
possibly-different relations as it already does. `rcongr` here is the in-tree
realization of exactly that idea, specialized to the `Related`/`RelatedBinOp`
database.
-/

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField
open Lean Elab Tactic Meta

universe u

/-- The cross-head congruence rule. Reduce a binary cross-head goal
    `Related enc (op a b) (bop a' b')` to its two per-argument relatedness
    subgoals `Related enc a a'`, `Related enc b b'`, discharging the commuting
    square `RelatedBinOp enc op bop` by instance resolution. This is the
    relational analogue of a `@[gcongr]` monotonicity lemma — except the two
    heads `op`, `bop` *differ*, which is precisely why it cannot be a
    `@[gcongr]` lemma. It is definitionally the instance composer
    `composeBinOp`, repackaged with the operands as explicit hypotheses so the
    descent can leave them as subgoals. -/
theorem rcongrBinOp {A α : Type u} (enc : A → α) (op : A → A → A) (bop : α → α → α)
    {a b : A} {a' b' : α}
    [RelatedBinOp enc op bop] (ha : Related enc a a') (hb : Related enc b b') :
    Related enc (op a b) (bop a' b') :=
  composeBinOp enc op bop a b a' b'

/-- Relational congruence descent. A `TacticM` recursion on the goal:

* on `Related enc t t'` with `t = op a b` binary, apply `rcongrBinOp` (the
  cross-head rule), leaving the two per-argument `Related` subgoals, and recurse
  on each;
* on a bare `Related` leaf (or when the binary rule does not apply), close it
  via the shared fast registry leaf `transferRegistryLeaf` (`inferInstance` — the
  `leaf`/`leafId` instances — or `rfl`);
* on an `=` goal, bridge through `transferGround` (`Related id a b → a = b`) and
  recurse on the resulting `Related` goal.

Termination: each binary step strips one operation layer, so the recursion is
well-founded on op-tree size; leaves make no goal. -/
partial def rcongrCore : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  match tgt.getAppFnArgs with
  | (``Related, #[_A, _α, _enc, lhs, _rhs]) =>
      if lhs.getAppNumArgs == 2 then
        try
          evalTactic (← `(tactic| refine rcongrBinOp _ _ _ ?_ ?_))
          allGoals rcongrCore
          return
        catch _ => pure ()
      transferRegistryLeaf
  | (``Eq, #[_α, _, _]) =>
      evalTactic (← `(tactic| refine transferGround (h := ?_)))
      rcongrCore
  | _ =>
      transferRegistryLeaf

/-- The `rcongr` tactic — relational (cross-head) congruence descent.

`rcongr` is the hard-wired specialization of the relation-generic,
attribute-driven `hgcongr` (`HGCongr.lean`): its descent rule `rcongrBinOp` is
fixed to the `Related`/`RelatedBinOp` square database rather than looked up by a
registered head pair. `param_solve` (`ParamSolve.lean`) is the unified entry
point that combines this descent with the relational congruence closure
`param_cc` as its leaf discharger; this tactic and its demos remain the
specialized descent and the capability boundary witness (the `#guard_msgs`
gcongr-rejection proof below).

Closes a relatedness goal `Related enc t t'` (or an `=` bridged to one) by
descending through a registered op-tree: at each binary node `op a b` ↔
`bop a' b'` it applies the cross-head congruence rule `rcongrBinOp` (the
registered `RelatedBinOp` square), recursing on the per-argument relatedness
subgoals, and bottoms out at leaves via the registry. This is the relational
analogue of `gcongr`, for goals whose two sides have *different* head functions
— a shape `gcongr` rejects (see the module "Scope" section). -/
elab "rcongr" : tactic => rcongrCore

/-! ## The cross-head demo `gcongr` cannot do

The Baby Bear field composite `a * b + c` realized by the emitted op-tree
`bbFieldAdd (bbFieldMul a b) c`: the heads are `*`/`+` on the left and
`bbFieldMul`/`bbFieldAdd` on the right (registered as `RelatedBinOp` squares
`bbMulRelated`/`bbAddRelated` in `Related.lean`). `rcongr` descends through both
cross-head nodes; `gcongr` cannot — it needs `lhsHead == rhsHead`. -/

/-- Cross-head relatedness, by `rcongr`. The composite transfers through two
    cross-head nodes (`+`↔`bbFieldAdd`, then `*`↔`bbFieldMul`); the descent
    leaves per-argument leaves which the registry closes. -/
example (a b c : F) :
    Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c) := by rcongr

/-- The same composite as an equation, by `rcongr`. The `=` form is bridged
    to `Related id _ _` via `transferGround`, then descended. This is the
    `Related.lean` result, obtained by *structural cross-head descent*
    rather than a single opaque `inferInstance`. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by rcongr

/-! `gcongr` rejects the very same goal. The two sides have different head
functions (`*`/`+` vs `bbFieldMul`/`bbFieldAdd`), so `gcongr` makes no progress
— the `#guard_msgs` below pins the failure. This is the capability boundary
`rcongr` crosses. -/

/-- error: gcongr did not make progress -/
#guard_msgs in
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by gcongr

end Transfer
