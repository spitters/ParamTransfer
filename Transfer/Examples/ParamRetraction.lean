/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransferTac
import Transfer.Hierarchy.ParamEquiv
import Mathlib.Data.ZMod.Basic

/-!
# The `ℤ ↠ ZMod p` retraction transfer domain (non-diagonal)

This module builds the paper's ring-quotient example (`int ↔ Zmodp`) as a
non-diagonal transfer domain for the `Param` engine — a representation change
where the two sides are *different types* and the round-trip holds on one side
only (a retraction, not an equivalence). It realizes the witness shape that
`ParamCryptoExamples`'s §4 note describes without constructing.

## Why this is a retraction, and the exact `Param` class it reaches

The encoding is `Int.cast : ℤ → ZMod p` with graph relation `R i x := (↑i = x)`.

* Forward is `map3`. `R` is *literally* the graph of `Int.cast`, so both
  inclusions (`map a = b → R a b` and `R a b → map a = b`) are the identity on the
  defining equation. The forward direction populates `map`, `map_in_R`, `R_in_map`.
* Backward is `map2a` — and *not* `map2b`/`map3`. The decoder is
  `g : ZMod p → ℤ := fun x => (↑x.val : ℤ)`. The backward `Map2aHas (symRel R)`
  needs `map := g` plus `map_in_R : g x = i → symRel R x i`, i.e. (after `subst`)
  the retraction law `Int.cast (↑x.val) = x`, which is `ZMod.natCast_val`'s
  right-inverse on `ZMod p` cast through `Int → Nat`. This holds. But `map2b`'s
  `R_in_map : (↑i = x) → g x = i` would say *every* integer with `↑i = x` equals
  the canonical `g x`, which is false (`i` and `i + p` both satisfy `↑i = x`). So
  the backward direction stops at `map2a`: section + `map_in_R`, no `R_in_map`.

Hence the retraction is exactly a `Param .map3 .map2a ℤ (ZMod p)`. Compare
`paramOfEquiv` (`Param .map3 .map2b`, *left* inverse) — incomparable backward
class. A two-sided bijection would reach `map3`/`map4`; the quotient cannot,
because `section ∘ Int.cast` is reduction-mod-`p`, not `id` on `ℤ`.

## Feeding the `∀`-rule and `TransferDom`

`forallTransfer`/`TransferDom` consume the domain at `(.map0, .map2a)` — forward
*nothing*, backward `map2a`. The witness here is *stronger* forward (`map3`), so
the forward structure is forgotten down to `map0` (`Map3Has → … → Map0Has`) and the
result fits `TransferDom ℤ (ZMod p)` directly. No shape gap: the retraction's
backward `map2a` is precisely what the engine needs, so `param_transfer` resolves
this non-diagonal domain with no caller-named relation.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Transfer.Param

open Transfer

/-! ## The retraction witness `ℤ ↠ ZMod p` -/

/-- The `ℤ ↠ ZMod p` retraction as a `Param .map3 .map2a`.

    Relation `R i x := (↑i = x)` (graph of `Int.cast`). Forward `map3` (graph of
    `Int.cast`, both inclusions trivial). Backward `map2a`: decoder
    `g x := (↑x.val : ℤ)` with `map_in_R` the retraction `Int.cast (↑x.val) = x`
    (`ZMod.natCast_val` cast through `Int.cast_natCast`). It is *not* `map2b`,
    because the quotient is not injective — the class is asymmetric. -/
def intZModParam (p : ℕ) [NeZero p] : Param .map3 .map2a ℤ (ZMod p) where
  R := fun i x => (Int.cast i : ZMod p) = x
  fwd := ⟨Int.cast, fun _ _ h => h, fun _ _ h => h⟩
  bwd :=
    ⟨fun x => (x.val : ℤ),
     fun x i (h : (x.val : ℤ) = i) => by
       subst h
       -- goal: symRel R x ↑x.val, i.e. (Int.cast (↑x.val) : ZMod p) = x
       simp only [symRel, Int.cast_natCast]
       exact ZMod.natCast_rightInverse x⟩

/-! ## Weakening into the `∀`-rule level and the `TransferDom` instance -/

/-- Forget the forward `map3` of `intZModParam` down to `map0`, landing at the
    `(.map0, .map2a)` level that `forallTransfer`/`TransferDom` consume. The
    backward `map2a` retraction is preserved verbatim. -/
def intZModDom (p : ℕ) [NeZero p] : Param .map0 .map2a ℤ (ZMod p) where
  R := (intZModParam p).R
  fwd := ⟨⟩
  bwd := (intZModParam p).bwd

/-- `TransferDom` accepts the retraction. The `ℤ ↠ ZMod p` change of
    representation resolves automatically for `param_transfer`: the engine takes
    the backward `map2a` (decoder + retraction) it needs, with no caller-named
    relation. This is a *non-diagonal* `TransferDom` (distinct source and
    target types), unlike the diagonal `TransferDom A A`. -/
instance instTransferDomIntZMod (p : ℕ) [NeZero p] : TransferDom ℤ (ZMod p) where
  dom := intZModDom p

/-! ## A non-diagonal transfer demo across `ℤ`/`ZMod p`

The relation on related pairs `(i, x)` is `(↑i : ZMod p) = x`, so the pointwise
obligation is phrased with the integer `i` *cast into* `ZMod p` — a real
representation change. We transfer a `∀ i : ℤ` statement to a `∀ x : ZMod p`
statement, supplying the predicate correspondence and discharging the emitted
obligation through the cast equation. -/

/-- Non-diagonal `∀`-transfer (`ℤ ↠ ZMod p`). From `∀ i : ℤ, (P i : Prop)`
    the transfer yields `∀ x : ZMod p, P' x` whenever, on related pairs `(i, x)` with
    `(↑i : ZMod p) = x`, the integer property `P i` implies the modular property
    `P' x`. The domain `Param` is the retraction, resolved by `TransferDom`. -/
def intZModForallTransfer {p : ℕ} [NeZero p] {P : ℤ → Prop} {P' : ZMod p → Prop}
    (PB : ∀ (i : ℤ) (x : ZMod p), (Int.cast i : ZMod p) = x → (P i → P' x)) :
    (∀ i : ℤ, P i) → (∀ x : ZMod p, P' x) :=
  forallTransfer (intZModDom p) PB

/-- Concrete transfer demo. Transfer `∀ i : ℤ, ↑i = (↑i : ZMod p)` (trivially
    true) to `∀ x : ZMod p, ∃ i : ℤ, (↑i : ZMod p) = x` — the *surjectivity of the
    quotient*, obtained purely by transferring an integer statement across the
    retraction. On a related pair `(i, x)` with `↑i = x`, the witness is `i`
    itself, so the pointwise obligation is discharged from the relation hypothesis.
    The representation change `ℤ ↦ ZMod p` is invisible at the call site beyond the
    supplied pointwise step. -/
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, ∃ i : ℤ, (Int.cast i : ZMod p) = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) _
  exact ⟨i, hix⟩

/-- A second concrete demo with a nontrivial pointwise step. Transfer the
    integer fact `∀ i : ℤ, (↑i : ZMod p) + 0 = ↑i` to the modular fact
    `∀ x : ZMod p, x + 0 = x`, rewriting along the relation `↑i = x`. -/
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) + 0 = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, x + 0 = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) h
  rw [← hix]; exact h

/-! ## Secondary retraction: `ℕ ↠ ZMod p` (for `[NeZero p]`)

A cleaner natural-number retraction in the same shape: `Nat.cast : ℕ → ZMod p`
(for `[NeZero p]`) is surjective with section `ZMod.val`, round-trip on the
`ZMod p` side only (`ZMod.natCast_rightInverse`, since `ZMod.val ∘ Nat.cast` is
reduction-mod-`p`, not `id` on `ℕ`). Same `Param .map3 .map2a` class, same
`TransferDom` wiring — a second witness that the non-diagonal machinery is not
tied to the `ℤ` source. -/

/-- The `ℕ ↠ ZMod p` retraction as a `Param .map3 .map2a` (for `[NeZero p]`):
    forward `Nat.cast` (graph, `map3`), backward `ZMod.val` with `map_in_R` the
    retraction `Nat.cast (↑x.val) = x` (`ZMod.natCast_rightInverse`). -/
def natZModParam (p : ℕ) [NeZero p] : Param .map3 .map2a ℕ (ZMod p) where
  R := fun k x => (Nat.cast k : ZMod p) = x
  fwd := ⟨Nat.cast, fun _ _ h => h, fun _ _ h => h⟩
  bwd :=
    ⟨fun x => x.val,
     fun x k (h : x.val = k) => by
       subst h
       simpa only [symRel] using ZMod.natCast_rightInverse x⟩

/-- The `ℕ ↠ ZMod p` domain at the `∀`-rule level `(.map0, .map2a)`. -/
def natZModDom (p : ℕ) [NeZero p] : Param .map0 .map2a ℕ (ZMod p) where
  R := (natZModParam p).R
  fwd := ⟨⟩
  bwd := (natZModParam p).bwd

/-- `TransferDom` accepts the `ℕ ↠ ZMod p` retraction too. -/
instance instTransferDomNatZMod (p : ℕ) [NeZero p] : TransferDom ℕ (ZMod p) where
  dom := natZModDom p

/-- `ℕ ↠ ZMod p` transfer demo. Transfer `∀ k : ℕ, (↑k : ZMod p) = ↑k`
    to `∀ x : ZMod p, ∃ k : ℕ, (↑k : ZMod p) = x` (surjectivity of the
    reduction), across the secondary retraction. -/
example (p : ℕ) [NeZero p] :
    (∀ k : ℕ, (Nat.cast k : ZMod p) = (Nat.cast k : ZMod p)) →
      (∀ x : ZMod p, ∃ k : ℕ, (Nat.cast k : ZMod p) = x) := by
  param_transfer
  intro k x (hkx : (Nat.cast k : ZMod p) = x) _
  exact ⟨k, hkx⟩

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.intZModParam' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms intZModParam

/-- info: 'Transfer.Param.intZModForallTransfer' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms intZModForallTransfer

end AxiomAudit

end Transfer.Param
