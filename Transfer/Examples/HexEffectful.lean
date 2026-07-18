/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Integrations.ParamTripleTransfer
import Mathlib.Data.List.Basic

/-!
# Transferring a `hex` elimination step across dense storage, effectfully

`hex`'s core algorithms are iterative: `HexBareiss` (fraction-free Gaussian
elimination), `HexRowReduce`, `HexLLL` all run loops whose bodies read and combine
matrix entries. When such a body is phrased as a monadic computation, its
correctness is a Hoare/`wp` triple, and transferring that triple across a change
of storage representation is the *effectful* analogue of the pure `∀`-transfer
(`possibility 3`). This module transfers a Bareiss-style elimination step across
the dense-storage refinement of `HexMatrixCorrespondence` using the Kleisli-level
logical relation `RComp` and `triple_transfer` from
`Integrations/ParamTripleTransfer`.

## The step and its two representations

A single elimination step reads two entries and combines them (`a - b`, the shape
of a Bareiss/Gauss update). It is written twice:

* `hexStep` reads from `hex`'s dense list storage (`l.getD i 0`);
* `absStep` reads from the abstract Mathlib vector (`v i`).

On inputs related by the dense-storage refinement (entry-wise `l.getD i 0 = v i`,
the relation of `HexMatrixCorrespondence.decV`), the two computations are
`RComp`-related at value equality — the witness assembled structurally from
`RComp.pure`/`RComp.bind`, one leaf per `pure`/`bind` in the do-block. That is the
abstraction theorem at the monad level: the relation on computations induced by
the relation on the entries they read.

## Transfer

`triple_transfer` then moves the source triple (proved by `mvcgen`) for the
dense-storage step to the abstract step, with the postconditions related through
the entry equalities. A correctness statement established once over `hex`'s
concrete storage is transported to the Mathlib specification with no re-proof of
the loop body.
-/

set_option autoImplicit false

open Std.Do

namespace Transfer.Param

/-! ## A Bareiss-style elimination step, over the two representations -/

/-- The elimination step over `hex`'s dense list storage: read two stored
    entries and combine them (`a - b`). -/
def hexStep (l : List ℤ) : Id ℤ := do
  let a ← pure (l.getD 0 0)
  let b ← pure (l.getD 1 0)
  pure (a - b)

/-- The same step over the abstract Mathlib vector. -/
def absStep {n : ℕ} (v : Fin (n + 2) → ℤ) : Id ℤ := do
  let a ← pure (v 0)
  let b ← pure (v 1)
  pure (a - b)

/-! ## The `RComp` witness across the storage change

Assembled leaf-by-leaf from `RComp.pure`/`RComp.bind` — the compositional core of
the monad-level abstraction theorem. The two input relations
`l.getD i 0 = v i` are the entry-wise instances of the dense-storage refinement
(`HexMatrixCorrespondence.decV`). -/

/-- On inputs related by the dense-storage refinement (`l.getD 0 0 = v 0`,
    `l.getD 1 0 = v 1`), the concrete and abstract elimination steps are
    `RComp`-related at value equality. The witness mirrors the do-block: two
    `bind`s over two `pure` reads, then a `pure` of the combination. -/
theorem hexStep_RComp {n : ℕ} (l : List ℤ) (v : Fin (n + 2) → ℤ)
    (h0 : l.getD 0 0 = v 0) (h1 : l.getD 1 0 = v 1) :
    RComp (M := Id) (fun a a' => a = a') (hexStep l) (absStep v) :=
  RComp.bind (RComp.pure _ h0) (fun a a' ha =>
    RComp.bind (RComp.pure _ h1) (fun b b' hb =>
      RComp.pure _ (by rw [ha, hb])))

/-! ## The source triple and its transfer -/

/-- Correctness of the step over `hex`'s dense storage, proved by `mvcgen`. -/
theorem hexStep_spec (l : List ℤ) :
    ⦃⌜True⌝⦄ (hexStep l) ⦃⇓r => ⌜r = l.getD 0 0 - l.getD 1 0⌝⦄ := by
  mvcgen [hexStep]

/-- **The effectful transfer.** The correctness triple established over `hex`'s
    concrete dense storage is transported to the abstract Mathlib step, along the
    `RComp` witness, with the postconditions related through the entry equalities
    `l.getD i 0 = v i`. The loop body is not re-verified: its abstract
    specification is *derived* from the concrete one by transfer. -/
theorem absStep_spec {n : ℕ} (l : List ℤ) (v : Fin (n + 2) → ℤ)
    (h0 : l.getD 0 0 = v 0) (h1 : l.getD 1 0 = v 1) :
    ⦃⌜True⌝⦄ (absStep v) ⦃⇓r => ⌜r = v 0 - v 1⌝⦄ := by
  refine triple_transfer (Rα := fun a a' => a = a') (hexStep_RComp l v h0 h1)
    ?_ (hexStep_spec l)
  intro a a' (haa : a = a') hc
  subst haa; rw [← h0, ← h1]; exact hc

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.hexStep_RComp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hexStep_RComp

end AxiomAudit

end Transfer.Param
