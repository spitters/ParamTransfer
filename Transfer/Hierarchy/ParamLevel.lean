/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Combinators.ParamArrow
public import Transfer.Combinators.ParamForall

/-!
# The level lattice + the minimal-`(m,n)` solver core

The synthesizer (`ParamSynth`) composes `Param` witnesses at a fixed level. The
full engine picks the minimal `(m,n)` a goal needs and synthesizes there. This
module supplies the solver's mathematical core:

* the `MapClass` lattice order `≤` (not linear — `map2a`/`map2b` are incomparable,
  both below `map3`), with `Decidable`, the partial-order laws, and the meet (`⊓`)
  = greatest lower bound (the "least common level");
* the level-arithmetic decision table `arrowReq`, with `forallReq` in `ParamForall.lean`: for a
  desired output level, the exact input levels each `Map_k_arrow`/`Map_k_forall` requires. A
  level-directed resolution or a
  `MetaM` solver consults these to dispatch the right combinator — the Lean analogue of
  Trocq's Elpi `param-class` constraint solver.

What remains for the full solver is the *resolution wiring* (variable-level
`HasParam` with these tables driving instance selection), built on this substrate.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.Param

/-! ## The lattice order on `MapClass` -/

/-- The structure order: `map0 ⊑ map1 ⊑ {map2a, map2b} ⊑ map3 ⊑ map4`, with `map2a`,
    `map2b` incomparable. `le m' m` means `m'` carries no more structure than `m`. -/
def MapClass.le : MapClass → MapClass → Bool
  | .map0, _      => true
  | .map1, .map0  => false
  | .map1, _      => true
  | .map2a, .map2a => true
  | .map2a, .map3  => true
  | .map2a, .map4  => true
  | .map2a, _      => false
  | .map2b, .map2b => true
  | .map2b, .map3  => true
  | .map2b, .map4  => true
  | .map2b, _      => false
  | .map3, .map3  => true
  | .map3, .map4  => true
  | .map3, _      => false
  | .map4, .map4  => true
  | .map4, _      => false

/-- `m' ⊑ m`: `m'` carries no more structure than `m` (the lattice order). -/
scoped infix:50 " ⊑ " => fun a b => MapClass.le a b = true

/-- Reflexivity. -/
theorem MapClass.le_refl (m : MapClass) : m ⊑ m := by cases m <;> rfl
/-- Transitivity. -/
theorem MapClass.le_trans {a b c : MapClass} (h1 : a ⊑ b) (h2 : b ⊑ c) : a ⊑ c := by
  cases a <;> cases b <;> cases c <;> simp_all [MapClass.le]
/-- Antisymmetry. -/
theorem MapClass.le_antisymm {a b : MapClass} (h1 : a ⊑ b) (h2 : b ⊑ a) : a = b := by
  cases a <;> cases b <;> simp_all [MapClass.le]

/-- The meet (greatest lower bound): the least common structure level. -/
def MapClass.meet : MapClass → MapClass → MapClass
  | .map0, _ => .map0
  | _, .map0 => .map0
  | .map1, _ => .map1
  | _, .map1 => .map1
  | .map2a, .map2a => .map2a
  | .map2b, .map2b => .map2b
  | .map2a, .map2b => .map1     -- incomparable ⇒ drop to map1
  | .map2b, .map2a => .map1
  | .map2a, _ => .map2a
  | _, .map2a => .map2a
  | .map2b, _ => .map2b
  | _, .map2b => .map2b
  | .map3, .map3 => .map3
  | .map3, .map4 => .map3
  | .map4, .map3 => .map3
  | .map4, .map4 => .map4

/-- The meet is a lower bound (left). -/
theorem MapClass.meet_le_left (a b : MapClass) : MapClass.meet a b ⊑ a := by
  cases a <;> cases b <;> rfl
/-- The meet is a lower bound (right). -/
theorem MapClass.meet_le_right (a b : MapClass) : MapClass.meet a b ⊑ b := by
  cases a <;> cases b <;> rfl

/-! ## The level-arithmetic decision tables (the solver's dispatch core)

For a desired **output forward** level of the arrow/forall combinator, these give the
exact `(m,n)` the two arguments must have — read directly off `ParamArrow.lean` /
`ParamForall.lean`. A level-directed resolver consults these to choose which
`Map_k_{arrow,forall}` to apply. -/

/-- Required argument levels for `Map_k_arrow` at a given output forward level.
    Returns `(PA.fwd, PA.bwd, PB.fwd, PB.bwd)`. From `ParamArrow.lean`:
    `Map1_arrow ← Param01/Param10`, `Map2a_arrow ← Param02b/Param2a0`,
    `Map2b_arrow ← Param02a/Param2b0`, `Map3_arrow ← Param03/Param30`. -/
def arrowReq : MapClass → Option (MapClass × MapClass × MapClass × MapClass)
  | .map0  => some (.map0, .map0, .map0, .map0)
  | .map1  => some (.map0, .map1, .map1, .map0)
  | .map2a => some (.map0, .map2b, .map2a, .map0)
  | .map2b => some (.map0, .map2a, .map2b, .map0)
  | .map3  => some (.map0, .map3, .map3, .map0)
  | .map4  => some (.map0, .map3, .map3, .map0)   -- map4 via map3 inputs (Prop coherence free)

/-- The table of the dependent-Π rule (`forallReq`, defined with `mapHas_forall` in
    `ParamForall.lean`) asks for at most `map3` of the domain at every output level. -/
theorem forallReq_le_map3 (t : MapClass) : forallReq t ⊑ .map3 := by
  cases t <;> rfl

/-- The table of the dependent-Π rule asks for at most `map3` of the codomain family at
    every output level. -/
theorem forallFiberReq_le_map3 (t : MapClass) : forallFiberReq t ⊑ .map3 := by
  cases t <;> rfl

end Transfer.Param
