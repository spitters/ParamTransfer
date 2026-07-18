/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Synthesis.ParamSynth
import Transfer.Synthesis.ParamSynthExt
import Transfer.Hierarchy.ParamWeaken

/-!
# The upward level search (`param_resolve`)

The synthesizer (`ParamSynth`/`ParamSynthExt`) builds `Param` witnesses at a finite
menu of registered levels; `ParamWeaken` downgrades a witness along the lattice.
This module ties them into the level-directed resolver: a recursive tactic
`param_resolve` that closes a `Param m n A B`
goal at any target level reachable in the lattice, by

1. trying a registered instance exactly at the goal's `(m,n)` (the fixed-menu
   synthesizer — handles the self-relation `(map1,map1)` and `(map3,map0)` arrows
   and leaves directly);
2. else synthesizing at a stronger registered level and `Param.weaken`-ing down
   to the goal's `(m,n)` (the "synthesize-high, use-low" search — the `⊑` side
   conditions are discharged by `decide`);
3. else decomposing an arrow (`apply paramArrow`) and recursing on the two
   components;
4. else falling back to the embedding / equivalence leaves.

For the univalence-free fragment, witness synthesis is
level-directed (any `(m,n)` ⊑ a synthesizable level, over arrow/base
structure) rather than pinned to a fixed menu. The map4 universe relation remains
unreachable — and, as `UnivalenceStatus` proves, necessarily so (UA is
inconsistent in Lean). Beyond this lies the full term-level `⟦t⟧`
over arbitrary (non-type-directed) terms — a separate, larger metaprogram.
-/

set_option autoImplicit false

namespace Transfer.Param

open Transfer

/-- The level-directed resolver. Closes a `Param m n A B` goal at any
    lattice-reachable level. See the module docstring for the four strategies. -/
syntax "param_resolve" : tactic

macro_rules
  | `(tactic| param_resolve) =>
    `(tactic|
      first
        -- 1. registered instance exactly at the goal's level
        | exact (inferInstance : HasParam _ _ _ _).param
        -- 2. synthesize at a stronger level, weaken down (the upward search)
        | exact Param.weaken (by decide) (by decide)
            (inferInstance : HasParam .map1 .map1 _ _).param
        | exact Param.weaken (by decide) (by decide)
            (inferInstance : HasParam .map3 .map0 _ _).param
        -- 3. decompose an arrow and recurse
        | (apply paramArrow <;> param_resolve)
        -- 4. leaves
        | exact paramOfEmbedding
        | exact paramOfEquiv)

/-! ## Demonstrations: level-directed resolution at multiple targets

Each goal is closed by `param_resolve` alone — the level is found, not supplied. -/

/-- At the registered self-level (direct, strategy 1). -/
example : Param .map1 .map1 (Nat → Nat → Nat) (Nat → Nat → Nat) := by param_resolve

/-- Below the registered level — synthesized at `(map1,map1)` then weakened to
    `(map0,map0)` (strategy 2, the upward search). -/
example : Param .map0 .map0 (Nat → Nat) (Nat → Nat) := by param_resolve

/-- A leaf weakened to `map0` forward. -/
example : Param .map0 .map0 Nat Nat := by param_resolve

/-- A function type at `(map1, map0)` — weakened from the self-level. -/
example : Param .map1 .map0 (Bool → Nat) (Bool → Nat) := by param_resolve

/-- A base at `(map1, map1)` direct. -/
example : Param .map1 .map1 Bool Bool := by param_resolve

end Transfer.Param
