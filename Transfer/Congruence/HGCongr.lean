/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Congruence.HGCongrInit

/-!
# `hgcongr` — heterogeneous (cross-head) generalized congruence

`gcongr` ("generalized congruence") reduces a relational goal
`R (f a₁ … aₙ) (f b₁ … bₙ)` to per-argument subgoals `Rᵢ aᵢ bᵢ`. It is
structurally homogeneous: the two sides must share the *same* head function
`f` and arity. `Mathlib.Tactic.GCongr.Core` enforces this at three sites — lemma
registration, the runtime descent, and the single-head lookup key (see the
"Upstream patch" section).

`hgcongr` is the heterogeneous generalization: it allows the two sides to
have *different* heads `f ≠ g` (and even different arities), linked by a
**registered head correspondence** — a `@[hgcongr]` lemma whose conclusion is
`R (f a₁ … aₘ) (g b₁ … bₙ)`. The lemma database is keyed on the head *pair*
`(f, g)` together with the relation, rather than on a single head. This is the
upstream-mergeable, attribute-driven, relation-generic form of what the in-tree
`rcongr` (`RCongr.lean`) does ad hoc for the `Related`/`RelatedBinOp` database.

The engine (head-pair env extension, the `@[hgcongr]` attribute, and the
`hgcongr` tactic) lives in `HGCongrInit.lean` — an `initialize` env-extension
cannot be evaluated in the module that defines it, and applying `@[hgcongr]`
forces that evaluation, so the registered correspondences and demos must sit in
this importer. This module holds those correspondences and the capability demos.

## How it differs from `rcongr`

`rcongr` is specialized to one relation (`Related enc`) and one square database
(`RelatedBinOp` instances): its descent rule `rcongrBinOp` is hard-wired and the
"registration" is the `RelatedBinOp` instance set. `hgcongr` is the gcongr
*architecture* generalized:

* attribute-driven — new correspondences are added by tagging a lemma
  `@[hgcongr]`, exactly as `@[gcongr]` adds homogeneous ones (no bespoke
  typeclass);
* relation-generic — the relation `R` is read off the lemma's conclusion
  (`Eq`, `≤`, `Related`, …), not fixed to one relation;
* head-pair keyed — the lemma DB is a `(relName, lhsHead, rhsHead)`-keyed
  map, the minimal change to gcongr's single-head `GCongrKey` that admits
  cross-head lemmas.

The diagonal pair `(f, f)` recovers gcongr's homogeneous case, so `hgcongr`
subsumes the same-head architecture as a special case. `param_solve`
(`ParamSolve.lean`) uses cross-head descent of this kind as its structural step,
with the relational congruence closure `param_cc` as the leaf discharger.

## Upstream patch (Mathlib `GCongr/Core.lean`)

`hgcongr` here is a standalone in-tree realization; the same change applies
upstream by relaxing the single-head constraint at the three enforcing sites.
Quoting the identifiers/lines of
`Mathlib/Tactic/GCongr/Core.lean` (as read for this file):

1. **`GCongrKey`** (lines 147-156). Keys on one `head : Name`. Add a
   second head and key on the pair:
   ```
   structure GCongrKey where
     relName : Name
     lhsHead : Name   -- was `head`
     rhsHead : Name   -- NEW
     arity   : Nat
   ```
   The `Ord`/`BEq` instances (lines 156-159) extend componentwise. Backward
   compatibility: a homogeneous lemma has `lhsHead = rhsHead`, so the existing
   diagonal entries are unchanged in meaning; only the key gains a field that is
   equal to the single-head one on the diagonal.

2. **`makeGCongrLemma`** (lines 240-301). Drop the single-head guard at line 250
   ```
   unless head == head' && lhsArgs.size == rhsArgs.size do
     fail "LHS and RHS do not have the same head function and arity"
   ```
   replacing it with an arity-free admission that stores both heads. The
   varying-argument pairing (lines 252-264) zips `lhsArgs`/`rhsArgs`
   positionally, which assumes equal arity; for the heterogeneous case the pairs
   must instead be recovered from the *hypotheses* (each main hyp `Rᵢ lᵢ rᵢ`
   with `lᵢ ∈ lhsArgs`, `rᵢ ∈ rhsArgs` is a varying pair) — see `makeHGCongrLemma`
   (`HGCongrInit.lean`), which does exactly this and is robust to
   `arity(f) ≠ arity(g)` (the `HMul.hMul` head has arity 6, `bbFieldMul` has
   arity 2). The key built at line 300 becomes
   `{ relName, lhsHead, rhsHead, arity := lhsArgs.size }`.

3. **`Lean.MVarId.gcongr`** (lines 609-704). Drop the runtime head re-check at
   line 655
   ```
   unless lhsHead == rhsHead && lhsArgs.size == rhsArgs.size do …
   ```
   and look up by the pair key at line 661
   ```
   let key := { relName, head := lhsHead, arity := lhsArgs.size }
   ```
   becoming `{ relName, lhsHead, rhsHead, arity := lhsArgs.size }`. The
   per-argument recursion (lines 687-691) already threads a possibly-different
   relation per main subgoal (`mdataLhs?'`/`isContra`), so no change is needed
   there — heterogeneous heads reuse the existing per-arg relational descent.

Backward compatibility. Every current `@[gcongr]` lemma is the diagonal pair
`(f, f)`; with `lhsHead = rhsHead` the pair key/lookup coincide with the
single-head ones, and the dropped guards only *admit more* lemmas. No existing
proof changes.

Risks. (i) *Lookup ambiguity*: many `(f, g)` pairs may share a relation; the
priority-sorted list per key (already present as `List GCongrLemma`) handles
this, tried in succession as today. (ii) *Discharger interaction*: side goals on
a heterogeneous lemma (e.g. a nonnegativity premise) still flow to
`gcongr_discharger`; nothing in the discharger assumes equal heads, so it is
unaffected. (iii) *Positional pairing*: the one new piece of logic is
hyp-driven varying-pair recovery (point 2), needed only when arities differ;
on the diagonal it agrees with the positional zip.
-/

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField

/-! ## Registered correspondences for the Baby Bear field

These are the `@[hgcongr]` lemmas the demo below uses. Each relates an abstract
arithmetic head (`HMul.hMul` arity 6, `HAdd.hAdd` arity 6) to its emitted
op-tree head (`bbFieldMul`, `bbFieldAdd`, arity 2) under `Eq`. They are exactly
the cross-head shape `@[gcongr]` cannot accept. -/

/-- Cross-head correspondence `· * ·` ↔ `bbFieldMul` (heads `HMul.hMul`/`bbFieldMul`,
    arities 6/2). -/
@[hgcongr]
theorem mul_bbFieldMul_hcongr {a₁ b₁ a₂ b₂ : F} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    a₁ * b₁ = bbFieldMul a₂ b₂ := by
  subst h₁; subst h₂; exact (bbFieldMul_eq _ _).symm

/-- Cross-head correspondence `· + ·` ↔ `bbFieldAdd` (heads `HAdd.hAdd`/`bbFieldAdd`,
    arities 6/2). -/
@[hgcongr]
theorem add_bbFieldAdd_hcongr {a₁ b₁ a₂ b₂ : F} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    a₁ + b₁ = bbFieldAdd a₂ b₂ := by
  subst h₁; subst h₂; exact (bbFieldAdd_eq _ _).symm

/-! ## Demos -/

/-- The cross-head composite `@[gcongr]` rejects, closed by `hgcongr`. The
    goal `a * b + c = bbFieldAdd (bbFieldMul a b) c` has heads `+`/`*` on the
    left and `bbFieldAdd`/`bbFieldMul` on the right (different heads *and*
    different arities, 6 vs 2). `hgcongr` descends through both cross-head nodes
    via the registered correspondences, leaving per-argument `rfl` leaves. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by hgcongr

-- `gcongr` rejects the same goal — its two sides have different head
-- functions, so it makes no progress. This is the capability boundary
-- `hgcongr` crosses.
/-- error: gcongr did not make progress -/
#guard_msgs in
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by gcongr

/-! ## Subsumption of the homogeneous (diagonal) case

A same-head correspondence `(f, f)` is just a `@[hgcongr]` lemma with
`lhsHead = rhsHead`. Registering one and mixing it with a cross-head step shows
`hgcongr` subsumes gcongr's homogeneous architecture. -/

/-- Homogeneous (diagonal) correspondence `bbFieldMul` ↔ `bbFieldMul`: the same
    head on both sides — exactly the shape a `@[gcongr]` lemma has, here keyed on
    the diagonal pair `(bbFieldMul, bbFieldMul)`. -/
@[hgcongr]
theorem bbFieldMul_self_hcongr {a₁ b₁ a₂ b₂ : F} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
    bbFieldMul a₁ b₁ = bbFieldMul a₂ b₂ := by
  subst h₁; subst h₂; rfl

/-- Mixing a diagonal step with a cross-head step. The outer node is the
    cross-head `+`↔`bbFieldAdd`; its left child is the diagonal
    `bbFieldMul`↔`bbFieldMul` step (closed via `bbFieldMul_self_hcongr`), its
    right child a `rfl` leaf. `hgcongr` handles both with one descent — the
    diagonal pair `(f, f)` is the homogeneous gcongr case as a special instance
    of the head-pair architecture. -/
example (a b c : F) :
    bbFieldMul a b + c = bbFieldAdd (bbFieldMul a b) c := by hgcongr

end Transfer
