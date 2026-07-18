/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransferTac
import Transfer.Hierarchy.ParamEquiv
import Transfer.Examples.HexMatrixCorrespondence
import Mathlib.Tactic
import Mathlib.Data.List.Basic

/-!
# `hex`'s `Array`-backed storage: carrier-agnostic refinement + verified compute

`leanprover/hex` stores matrices and vectors in `Array`, for O(1) indexing and
tight compiled code — not `List`. This module shows two things about targeting
`hex` CoqEAL-style:

1. **The refinement is carrier-agnostic.** Re-running the dense-storage
   correspondence of `HexMatrixCorrespondence` on `Array ℤ` instead of `List ℤ`
   changes only the retraction lemma's backing (`Array.ofFn`/`Array.getD` in place
   of `List.ofFn`/`List.getD`); the `Param .map0 .map2a` witness, the
   `TransferDom` instance, and the `param_transfer` proof are structurally
   identical. The engine is indifferent to the concrete carrier — the property
   that lets `hex`'s efficient structures sit underneath the same transfer with no
   reproof.

2. **Prove at the spec, run on the efficient carrier.** A `@[csimp]` verified
   swap installs an `Array.foldl`-based implementation as the runtime realization
   of a spec-level fold, with the equality proved. Compiled code runs the fast
   `Array` version; the proof rides along. This is the CoqEAL "refinements for
   computation" payoff — the mechanism by which `Matrix.det` (proof-oriented)
   would execute through `HexDeterminant` (efficient) while staying verified.

The `Array` retraction (`decVA (encVA v) = v`) is total and the refinement lands
at `map2a` (backward section + `map_in_R`), identical to the `List` case — the
level analysis is a property of the *relation*, not the data structure.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Transfer.Param

open Transfer

/-! ## The `Array` retraction primitive (O(1) dense access) -/

/-- The `Array` analogue of `HexMatrixCorrespondence.getD_ofFn`: decoding an
    `Array.ofFn` at an in-range index returns the function value. The single fact
    that generates the `Array` correspondence — same shape as the `List` one,
    different backing. -/
theorem getD_ofFnA {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (Array.ofFn f).getD i d = f i := by
  rw [Array.getD]; simp [i.isLt]

/-- `hex`'s efficient dense vector: an `Array` of integers (O(1) access). -/
abbrev HVecA : Type := Array ℤ

/-- Decoder `HVecA → AVec n` (dense read, out-of-range default `0`). `AVec` is
    shared with `HexMatrixCorrespondence` — the same abstract carrier, now
    refined by `Array` instead of `List`. -/
def decVA (n : ℕ) (a : HVecA) : AVec n := fun i => a.getD i 0

/-- Section `AVec n → HVecA` (dense write). -/
def encVA {n : ℕ} (v : AVec n) : HVecA := Array.ofFn v

/-- The retraction law, on the `Array` carrier. -/
theorem decVA_encVA {n : ℕ} (v : AVec n) : decVA n (encVA v) = v := by
  funext i; simp only [decVA, encVA]; exact getD_ofFnA v i 0

/-- The `Array`-vector refinement as `Param .map0 .map2a HVecA (AVec n)`.
    Compare `HexMatrixCorrespondence.hVecDom` on `List ℤ`: the body is identical
    up to the carrier — the engine is indifferent to `List` vs `Array`. -/
def hVecADom (n : ℕ) : Param .map0 .map2a HVecA (AVec n) where
  R := fun a v => decVA n a = v
  fwd := ⟨⟩
  bwd := ⟨encVA, fun v a (h : encVA v = a) => by subst h; exact decVA_encVA v⟩

/-- `TransferDom` for the efficient `Array` carrier. -/
instance instTransferDomHVecA (n : ℕ) : TransferDom HVecA (AVec n) where
  dom := hVecADom n

/-- The same correspondence demo as the `List` version, on `Array`: the dense
    decoder is surjective onto `AVec n`, obtained by `param_transfer` from the
    reflexive source fact. The proof is byte-identical to the `List` case. -/
example (n : ℕ) :
    (∀ a : HVecA, decVA n a = decVA n a) → (∀ v : AVec n, ∃ a : HVecA, decVA n a = v) := by
  param_transfer
  intro a v (hav : decVA n a = v) _
  exact ⟨a, hav⟩

/-! ## Verified-compute swap: run the spec on the `Array` carrier

A spec-level fold (`List.sum`) and its efficient `Array`-based implementation
(`Array.foldl`) are proved equal, and the equality is installed with `@[csimp]`
so *compiled code runs the `Array` version* while the abstract statement remains
the spec. This is the "prove at Mathlib, run at hex" loop: the efficient carrier
carries the proof. -/

/-- Spec-level summation (proof-oriented). -/
def specSum (l : List ℤ) : ℤ := l.sum

/-- Efficient implementation routing through `Array.foldl` (hex's access
    pattern). -/
def fastSum (l : List ℤ) : ℤ := l.toArray.foldl (· + ·) 0

/-- The verified swap: `specSum` and `fastSum` are equal, installed as the
    runtime realization. Compiled `specSum` executes `Array.foldl`, carrying this
    proof. -/
@[csimp] theorem specSum_eq_fastSum : @specSum = @fastSum := by
  funext l
  simp only [specSum, fastSum, List.foldl_toArray', List.sum_eq_foldl]

/-- The swapped definition still computes (and, when compiled, via `Array`). -/
example : specSum [1, 2, 3, 4, 5] = 15 := by decide

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.hVecADom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hVecADom

/-- info: 'Transfer.Param.specSum_eq_fastSum' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms specSum_eq_fastSum

end AxiomAudit

end Transfer.Param
