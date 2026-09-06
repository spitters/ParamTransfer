/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public meta import Transfer.Synthesis.ParamInfer
public meta import Transfer.Hierarchy.ParamWeaken
public import Transfer.Hierarchy.ParamWeaken
public meta import Transfer.Statements.ParamTransferTac
public import Transfer.Statements.ParamTransferTac
public import Transfer.Synthesis.ParamInfer

/-!
# Auto-weakening of witnesses + a unified transfer entry

`ParamWeaken.lean` proves the lattice action `Param.weaken : Param m n A B →
m' ⊑ m → n' ⊑ n → Param m' n' A B` and `weaken_lands_below` (synthesize-high,
use-low). `ParamResolve.lean` consults it for a hardcoded candidate list. This
module supplies two things at the *surface* level:

## 1. Auto-weakening (upstream's `Trocq Use` "all sub-class versions")

Upstream Trocq, on registering a relatedness lemma, synthesizes every
lattice-below class version so a goal at a lower class resolves without the user
restating the lemma. This module mirrors that two ways:

* **`allWeakenings`** (the enumerating function): given a witness at `(m, n)`,
  returns the full below-set `{(m', n', Param m' n' A B) | m' ⊑ m, n' ⊑ n}`,
  each entry produced by `Param.weaken`. `belowList`/`mem_belowList` give the
  decidable below-set with its membership characterization.
* **`RegisteredParam`** (a sibling registry typeclass, distinct from `paramExt`):
  carries one witness at its strongest available class `(m, n)` (the level pair
  is an `outParam`, recovered from `(A, B)`). The tactic **`auto_weaken`** then
  closes a goal at *any* lattice-lower `(m', n')` by `Param.weaken (by decide)
  (by decide) RegisteredParam.reg` — the user registers once, at the strong
  level, and lower-class goals resolve with no hand-written lower witness.

`Param.weaken` is the engine; this module is the surface that makes "register
high, use low" automatic.

## 2. A unified transfer entry — `transfer_auto`

`param_transfer` (the `∀`-rule) and the `R_arrow` `app`-rule are separate
surface entries. `transfer_auto` is a single tactic dispatching both:

* a `∀`-implication goal `(∀ a, P a) → (∀ a', P' a')` runs the abstraction-theorem
  `∀`-rule with the domain `Param` resolved by `TransferDom` (`forallTransferAuto`),
  falling back to an explicit-domain `forallTransfer`;
* an `R_arrow PA PB f f'` relatedness goal peels to its pointwise codomain
  obligation (the `app`-rule content).

It runs the translation at a fixed output class (the univalence-free
`Prop`-motive level the `∀`/arrow combinators consume). Per-subterm *level
inference* — picking the minimal output class per occurrence — is the job of the
constraint-graph solver `inferParamLevels` in `ParamInfer.lean`; that solver
generalizes the fixed class choice here (its `inferRootClass` is exactly the
class `transfer_auto` would synthesize at, then `Param.weaken` down). This file
documents that consumption point; it does not duplicate the solver.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param

open Transfer

/-! ## Part 1a — `allWeakenings`: enumerate every lattice-below class version -/

/-- The six structure classes, in ascending lattice order. -/
def allClasses : List MapClass := [.map0, .map1, .map2a, .map2b, .map3, .map4]

/-- The decidable below-set of a class `m`: every class `m' ⊑ m`. -/
def belowList (m : MapClass) : List MapClass :=
  allClasses.filter (fun m' => MapClass.le m' m)

/-- Membership in `belowList m` is exactly the lattice order `m' ⊑ m`. -/
theorem mem_belowList {m' m : MapClass} (h : MapClass.le m' m = true) :
    m' ∈ belowList m := by
  simp only [belowList, List.mem_filter, allClasses]
  refine ⟨?_, h⟩
  cases m' <;> simp

/-- The converse: anything in `belowList m` really is `⊑ m`. -/
theorem belowList_le {m' m : MapClass} (h : m' ∈ belowList m) :
    MapClass.le m' m = true := by
  simp only [belowList, List.mem_filter] at h
  exact h.2

/-- **All sub-class versions of a witness.** Given a `Param m n A B`, synthesize
    every lattice-below class version `(m', n', Param m' n' A B)` via
    `Param.weaken`. This is the data-level analogue of upstream's `Trocq Use`
    "register every sub-class version": one registration at `(m, n)` materialises
    the whole below-set, so a consumer at any lower class has a witness ready. -/
def allWeakenings {m n : MapClass} {A B : Type u} (p : Param m n A B) :
    List (Σ m' : MapClass, Σ n' : MapClass, Param m' n' A B) :=
  (belowList m).flatMap (fun m' =>
    (belowList n).filterMap (fun n' =>
      if hm : MapClass.le m' m = true then
        if hn : MapClass.le n' n = true then
          some ⟨m', n', p.weaken hm hn⟩
        else none
      else none))

/-! ## Part 1b — `RegisteredParam` + `auto_weaken`: register high, resolve low

`RegisteredParam A B m n` is a sibling registry typeclass (independent of
`ParamDB.paramExt`): it carries one witness at the *strongest* class `(m, n)` a
type pair offers, with `(m, n)` an `outParam` so resolution recovers it from
`(A, B)`. The `auto_weaken` tactic then closes a goal at any lattice-lower
`(m', n')` from that single registration. -/

/-- A sibling registry typeclass carrying a `Param m n A B` witness at the
    strongest available class for the pair `(A, B)`. The level pair `(m, n)` is an
    `outParam`, recovered during resolution — the user registers once, at the
    strong level. Deliberately NOT `ParamDB.paramExt`: this is the lattice
    auto-weakening registry, a sibling mechanism. -/
class RegisteredParam (A B : Type u) (m n : outParam MapClass) where
  /-- The registered witness, at the strongest available class. -/
  reg : Param m n A B

/-- **Close a `Param m' n' A B` goal by auto-weakening a registered witness.**
    Resolves `RegisteredParam A B m n` (the strong registration) and applies
    `Param.weaken` down to the goal's `(m', n')`, discharging the `⊑` side
    conditions by `decide`. The user never writes the lower-class witness. -/
macro "auto_weaken" : tactic =>
  `(tactic| exact Param.weaken (by decide) (by decide) (RegisteredParam.reg))

/-! ## Part 1 — demonstrations of auto-weakening

A single witness is registered at a high class `(map3, map0)` (the embedding
shape), closing goals at strictly lower classes automatically — no hand-written
lower-class witness. -/

/-- A concrete registration at the high class `(map3, map0)`: the diagonal on
    `Nat` as the graph of `id` (forward `map3`, backward `map0`). This stands in
    for any strong witness one would register. -/
instance regNatNat : RegisteredParam Nat Nat .map3 .map0 where
  reg :=
    { R := Eq
      fwd := ⟨id, fun _ _ h => h, fun _ _ h => h⟩
      bwd := ⟨⟩ }

/-- **Lower-class resolves automatically.** A goal at `(map0, map0)` — strictly
    below the registered `(map3, map0)` — is closed by `auto_weaken` alone, with
    no hand-written `(map0, map0)` witness in scope. -/
example : Param .map0 .map0 Nat Nat := by auto_weaken

/-- Another strictly-lower target, `(map1, map0)`. -/
example : Param .map1 .map0 Nat Nat := by auto_weaken

/-- A target on the incomparable `map2b` branch, still `⊑ map3`. -/
example : Param .map2b .map0 Nat Nat := by auto_weaken

/-- And the registered class itself, `(map3, map0)` (weakening is reflexive). -/
example : Param .map3 .map0 Nat Nat := by auto_weaken

/-- The `allWeakenings` count for the `(map3, map0)` registration: the forward
    below-set of `map3` is `{map0, map1, map2a, map2b, map3}` (5 classes) and the
    backward below-set of `map0` is `{map0}` (1 class), so 5 weakenings. -/
example : (allWeakenings (regNatNat.reg)).length = 5 := by native_decide

/-! ## Part 2 — the unified transfer tactic `transfer_auto`

A single entry subsuming the per-shape `param_transfer` (`∀`-rule) and the
`R_arrow` `app`-rule. It runs at the fixed univalence-free output class the
`∀`/arrow combinators consume; `ParamInfer.inferRootClass` generalizes the class
choice (see the module docstring). -/

/-- **Unified transfer.** For the goal's shape:
    * a `∀`-implication goal runs the abstraction-theorem `∀`-rule with the domain
      `Param` resolved by `TransferDom` (`forallTransferAuto`), or an explicit
      domain (`forallTransfer`);
    * an `R_arrow PA PB f f'` relatedness goal peels to its pointwise codomain
      obligation (the `app`-rule).
    The caller then discharges the residual pointwise content. -/
macro "transfer_auto" : tactic =>
  `(tactic| first
      | refine forallTransferAuto ?_
      | refine forallTransfer ?_ ?_
      | (intro a a' har))

/-! ### `∀`-goal demos (the abstraction-theorem rule, domain auto-resolved) -/

/-- **Same-type `∀`-goal.** `(∀ n, P n) → (∀ n, Q n)` from pointwise `P n → Q n`,
    domain `Param` resolved automatically — closed through the single
    `transfer_auto`. -/
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) :
    (∀ n : ℕ, P n) → (∀ n : ℕ, Q n) := by
  transfer_auto
  intro a a' (e : a = a') hp
  exact e ▸ h a hp

/-- **Change-of-representation `∀`-goal** (`Num → ℕ`): the domain `Param` is the
    `Num ↦ ℕ` cast graph, resolved automatically by `TransferDom Num ℕ`. The same
    `transfer_auto` dispatches it — no separate per-shape entry. -/
example : (∀ n : Num, 0 ≤ n) → (∀ k : ℕ, 0 ≤ k) := by
  transfer_auto
  intro _ _ _ _
  exact Nat.zero_le _

/-! ### Arrow-goal demo (the `R_arrow` `app`-rule, peeled to pointwise) -/

/-- **Arrow-relatedness goal.** `R_arrow (paramEqDom ℕ) (paramEqCod ℕ) f f'` — the
    statement that `f`, `f'` send equal inputs to equal outputs — is reduced by
    the *same* `transfer_auto` to its pointwise codomain obligation, then closed
    from a pointwise hypothesis. The arrow `app`-rule and the `∀`-rule share one
    entry. -/
example (f f' : ℕ → ℕ) (h : ∀ a, f a = f' a) :
    R_arrow (paramEqDom ℕ) (paramEqCod ℕ) f f' := by
  transfer_auto
  rename_i a a' har
  show f a = f' a'
  cases har
  exact h a

/-! ## Dependence on the `ParamInfer` level-inference build

`transfer_auto` fixes the output class to the univalence-free `Prop`-motive
level the combinators consume. The general engine chooses, per occurrence, the
*minimal* class — the job of `ParamInfer.inferParamLevels` / `inferRootClass`
(the constraint-graph least-fixpoint solver over the proven lattice). The
generalization fits together exactly as documented in `ParamInfer`: read off
`inferRootClass` for the goal's (shape-abstracted) type, synthesize at that
class, and `Param.weaken` down — the very move `auto_weaken` automates here. The
two halves compose: `inferRootClass` (which class) + `auto_weaken`/`Param.weaken`
(land there). -/

/-- The level solver picks a *minimal* class for an unconstrained arrow shape —
    `map0`, never the inconsistent `map4`. This is the class `transfer_auto`'s
    general form would synthesize at; the fixed-class prototype here is the
    `map0`-bottom specialization made explicit. -/
example : inferRootClass (.arrow .leaf .leaf) = .map0 := by native_decide

/-- For a shape whose codomain is registered at `map3`, the solver picks exactly
    `map3` (not `map4`) — the minimal output class whose `arrowReq` codomain slot
    covers the demand. A level-directed `transfer_auto` would synthesize there,
    then `Param.weaken` to the goal's class. -/
example : inferRootClass (.arrow .leaf (.base (some .map3))) = .map3 := by native_decide

end Transfer.Param
