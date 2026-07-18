/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Hierarchy
import Transfer.Examples.PeanoBinNat

/-!
# Transported induction, the equiv-level combinator

This module automates the equiv-level (bijection) case of the dependent-motive
induction transfer. The `peano_bin_nat` flagship's manual `binNatInduction`
(`PeanoBinNat.lean`) pulled `Nat`'s recursor back along the specific bijection
`Num ≃ ℕ` by hand: rewrite `n = Num.ofNat' (n : ℕ)`, generalize the cast, and run
`Nat`'s recursor. Here that argument is made generic over the equivalence: for
any type `A` with a registered `ReprEquivClass A ℕ` (a bijection to `ℕ`),
`natEquivInduction` transfers `ℕ`'s induction principle to `A` — the manual
`binNatInduction` is a single application of it (re-derived below as
`binNatInduction'`, the same statement as `PeanoBinNat.BinNatInductionTarget`).

A `transfer_induction` tactic macro applies the combinator to a `∀ a : A, P a`
goal, leaving the base/step subgoals stated through the decoder, so the
transported induction is obtained without restating the combinator.

## Scope

This is the equiv-level (bijection) slice of the dependent-motive transfer.
Because `A ≃ ℕ` is a bijection, the motive `P : A → Prop` pulls back to
`fun k => P (dec k)` with no variance subtlety: `Prop` is the target and the
equivalence is invertible, so a single `induction` on the `ℕ`-side carrier
discharges everything. Any `ReprEquivClass A ℕ` gets induction this way.

## The general case

The general case is a dependent motive `P : A → Type` with mixed variance
over an arbitrary base recursor (not just `ℕ`). There the motive occurs both
covariantly and contravariantly, so the automatic route needs the relation on
`A → Type` (a parametricity `Param` of types) and the `(m,n)` level inference
that computes the minimal relation level each subterm requires. That level-
inference engine — over an arbitrary base type's recursor — is not implemented here;
this file closes the equiv/`ℕ` instance of it.
-/

set_option autoImplicit false

namespace Transfer.TransferInduction

open Transfer

/-! ## The generic transported-induction combinator

For any `A` equivalent to `ℕ`, `ℕ`'s `0`/`succ` induction transfers to `A`. The
proof is the manual `binNatInduction` argument made generic: rewrite
`a = dec (enc a)` via `dec_enc`, generalize `enc a` to a fresh `k : ℕ`, and run
`Nat`'s recursor on `k`, mapping `0 ↦ h0` and `k+1 ↦ hs k`. -/

/-- Transported induction across an equivalence to `ℕ`. For any type `A` with
    a `ReprEquivClass A ℕ` (a bijection `A ≃ ℕ`) and any motive
    `P : A → Prop`, proving `P` at the decoded zero and decoded successors
    suffices to prove `P` everywhere. This is `ℕ`'s induction principle pulled
    back along the equivalence — the generic form of the manual `binNatInduction`.

    Stated through the decoder `ReprMapClass.dec`: `h0` is `P (dec 0)` and `hs`
    steps from `P (dec k)` to `P (dec (k+1))`. -/
theorem natEquivInduction {A : Type} [ReprEquivClass A ℕ] (P : A → Prop)
    (h0 : P (ReprEquivClass.dec (A := A) (α := ℕ) 0))
    (hs : ∀ k : ℕ, P (ReprEquivClass.dec (A := A) (α := ℕ) k) →
      P (ReprEquivClass.dec (A := A) (α := ℕ) (k + 1))) :
    ∀ a : A, P a := by
  intro a
  rw [← ReprEquivClass.dec_enc (α := ℕ) a]
  generalize ReprMapClass.enc (α := ℕ) a = k
  induction k with
  | zero => exact h0
  | succ j ih => exact hs j ih

/-! ## Re-deriving the flagship `binNatInduction` through the combinator

The manual `PeanoBinNat.binNatInduction` is a single application of
`natEquivInduction` at the registered `ReprEquivClass Num ℕ`. To state the clean
`Num` `0`/`+1` principle, the decoded base and step must reduce to `Num`'s `0` and
`· + 1`. The decoder is `Num.ofNat'`, so:

* `dec 0 = (0 : Num)` holds definitionally (`Num.ofNat' 0` reduces to `0`);
* `dec (k+1) = dec k + 1` is `PeanoBinNat.num_ofNat'_succ` (`Num.ofNat'` pushed
  through successor via `Num.ofNat'_eq`).

These two helpers turn the combinator's decoder-stated obligations into the
`Num`-native `P 0` / `P n → P (n+1)`, giving back exactly
`PeanoBinNat.BinNatInductionTarget`. -/

/-- Decoded zero reduces to `Num`'s `0`. The `Num ≃ ℕ` decoder is `Num.ofNat'`,
    and `Num.ofNat' 0` reduces definitionally to `(0 : Num)`. -/
theorem dec_zero_num : ReprEquivClass.dec (A := Num) (α := ℕ) 0 = (0 : Num) := rfl

/-- Decoded successor reduces to `Num`'s `· + 1`. This is `num_ofNat'_succ`, the
    decoder mapped through successor. -/
theorem dec_succ_num (k : ℕ) :
    ReprEquivClass.dec (A := Num) (α := ℕ) (k + 1)
      = ReprEquivClass.dec (A := Num) (α := ℕ) k + 1 :=
  PeanoBinNat.num_ofNat'_succ k

/-- The `Num` induction principle, re-derived through `natEquivInduction`.
    Same statement as `PeanoBinNat.BinNatInductionTarget`; the manual recursor
    transfer is one application of the generic equiv-level combinator, with
    the decoded base/step rewritten to `Num`'s native `0` / `· + 1` by
    `dec_zero_num` / `dec_succ_num`. -/
theorem binNatInduction' : PeanoBinNat.BinNatInductionTarget := by
  intro P h0 hstep
  refine natEquivInduction (A := Num) P ?_ ?_
  · rw [dec_zero_num]; exact h0
  · intro k ih
    rw [dec_succ_num]
    exact hstep _ ih

/-- The re-derivation `binNatInduction'` proves the same proposition
    as the manual `PeanoBinNat.binNatInduction`. -/
theorem binNatInduction'_eq_manual :
    binNatInduction' = PeanoBinNat.binNatInduction := rfl

/-! ## A `transfer_induction` tactic

`transfer_induction` applies `natEquivInduction` to a `∀ a : A, P a` goal where
`A` carries a `ReprEquivClass A ℕ`, leaving the decoder-stated base/step
subgoals. The user then closes those with the base type's automation. -/

/-- Apply the equiv-level transported-induction combinator to the current
    `∀ a : A, _` goal, leaving the `h0` (decoded-zero) and `hs` (decoded-step)
    subgoals. -/
macro "transfer_induction" : tactic =>
  `(tactic| refine natEquivInduction _ ?_ ?_)

/-! ## Demo: `transfer_induction` on a `Num` goal

A trivially-true motive over `Num`; `transfer_induction` produces the base and
step subgoals through the decoder, each closed by `simp`. This is the transported
induction obtained without restating the combinator. -/

/-- Demonstration: every `Num` is `≥ 0`, proved by transported induction. The
    `transfer_induction` tactic leaves the decoded base/step; `simp` closes each. -/
theorem demo_num_zero_le : ∀ n : Num, 0 ≤ n := by
  transfer_induction
  · rw [PeanoBinNat.num_le_iff_to_nat_le]; simp
  · intro k _; rw [PeanoBinNat.num_le_iff_to_nat_le]; simp

end Transfer.TransferInduction
