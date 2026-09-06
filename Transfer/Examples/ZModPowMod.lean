/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

/-!
# `powMod`: binary modular exponentiation for kernel-`decide` modular arithmetic

`ZModDecide` decides a ground `ZMod m` ring identity by a bounded integer-residue
computation, reducing `% m` after every operation. Its `pow` node computes `base ^ n`
in full before the final `% m`, so a huge exponent — a Legendre-symbol exponent
`(p - 1) / 2 ≈ 2 ^ 380` at BLS12-381 size — builds an astronomically large
intermediate and stalls the kernel.

This module supplies the missing piece: a square-and-multiply modular exponentiation
`powMod b e m` that reduces `% m` after every squaring and multiply, so no intermediate
exceeds `m ^ 2`. The recursion is structural on a fuel argument, and the fuel is only a
termination certificate — the `e = 0` guard halts the loop after `⌈log₂ e⌉` steps — so
the Lean kernel reduces a fully applied `powMod` in a logarithmic number of steps and
`decide` stays on the GMP `Nat` fast path.

On top of it sit two number-theoretic deciders whose exponents were previously out of
reach: a modular inverse via Fermat's little theorem, and a quadratic-residue test via
Euler's criterion.

## Main results

* `powMod` / `powModGo` — square-and-multiply modular exponentiation and its
  fuelled worker.
* `powMod_cast` — the correctness lemma: `(powMod b e m : ZMod m) = (b : ZMod m) ^ e`.
* `powMod_lt` — the output is a residue, `powMod b e m < m` for `1 < m`.
* `invMod` / `invMod_cast` — modular inverse for a prime modulus, `a ^ (p - 2) % p`,
  correct as `(a : ZMod p)⁻¹`.
* `isSquare_of_powMod` / `not_isSquare_of_powMod` — the Euler-criterion quadratic-residue
  decider: `IsSquare (a : ZMod p)` reduces to a kernel `decide` on
  `powMod a.val (p / 2) p = 1`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.ZModPowMod

/-! ## Binary modular exponentiation -/

/-- Square-and-multiply worker for modular exponentiation. `fuel` bounds the number of
    squarings; `base` is the running square `b ^ (2 ^ k)`, `e` the remaining exponent bits,
    and `acc` the accumulated product, all kept reduced `% m`. The `e = 0` guard halts the
    loop, so the actual recursion depth is the bit length of the initial exponent. -/
def powModGo (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,      _,    _, acc => acc
  | fuel+1, base, e, acc =>
      if e = 0 then acc else
        let acc' := if e % 2 = 1 then (acc * base) % m else acc
        powModGo m fuel ((base * base) % m) (e / 2) acc'

/-- `b ^ e mod m` by square-and-multiply, reducing `% m` after every operation. Fuel `e`
    is a termination certificate (`e < 2 ^ e`); the `e = 0` guard in `powModGo` stops the
    loop after `⌈log₂ e⌉` steps, so a fully applied `powMod` reduces in the kernel in a
    logarithmic number of GMP `Nat` operations. -/
def powMod (b e m : ℕ) : ℕ := powModGo m e (b % m) e (1 % m)

/-- The worker invariant: cast back into `ZMod m`, `powModGo` computes
    `acc * base ^ e`, provided the fuel covers the exponent (`e < 2 ^ fuel`). -/
theorem powModGo_cast (m : ℕ) :
    ∀ (fuel base e acc : ℕ), e < 2 ^ fuel →
      ((powModGo m fuel base e acc : ℕ) : ZMod m) = (acc : ZMod m) * (base : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
      intro base e acc he
      have he0 : e = 0 := by simpa using he
      subst he0; simp [powModGo]
  | succ fuel ih =>
      intro base e acc he
      rw [powModGo]
      by_cases h0 : e = 0
      · subst h0; simp
      · simp only [h0, if_false]
        have hlt : e / 2 < 2 ^ fuel := by
          have : (2 : ℕ) ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
          omega
        rw [ih _ _ _ hlt]
        have hbase : (((base * base) % m : ℕ) : ZMod m) = (base : ZMod m) ^ 2 := by
          rw [ZMod.natCast_mod]; push_cast; ring
        rw [hbase]
        have hacc : (((if e % 2 = 1 then (acc * base) % m else acc) : ℕ) : ZMod m)
              = (acc : ZMod m) * (base : ZMod m) ^ (e % 2) := by
          by_cases h1 : e % 2 = 1
          · simp only [h1, if_true]; rw [ZMod.natCast_mod]; push_cast; ring
          · have : e % 2 = 0 := by omega
            simp [this]
        rw [hacc, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega

/-- **Correctness.** In `ZMod m`, `powMod b e m` is `(b : ZMod m) ^ e`: the residue
    computation cast back equals the abstract power. -/
theorem powMod_cast (b e m : ℕ) : ((powMod b e m : ℕ) : ZMod m) = (b : ZMod m) ^ e := by
  rw [powMod, powModGo_cast m e (b % m) e (1 % m) Nat.lt_two_pow_self,
      ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_one, one_mul]

/-- The worker stays inside `[0, m)`: with a reduced accumulator, so is the output. -/
theorem powModGo_lt (m : ℕ) (hm : 0 < m) :
    ∀ (fuel base e acc : ℕ), acc < m → powModGo m fuel base e acc < m := by
  intro fuel
  induction fuel with
  | zero => intro base e acc h; simpa [powModGo]
  | succ fuel ih =>
      intro base e acc h
      rw [powModGo]
      by_cases h0 : e = 0
      · simp [h0, h]
      · simp only [h0, if_false]
        apply ih
        split
        · exact Nat.mod_lt _ hm
        · exact h

/-- `powMod b e m` is a residue: it lies in `[0, m)` for `1 < m`. -/
theorem powMod_lt (b e m : ℕ) (hm : 1 < m) : powMod b e m < m := by
  apply powModGo_lt m (by omega)
  exact Nat.mod_lt _ (by omega)

/-! ## Modular inverse via Fermat's little theorem -/

/-- Fermat's little theorem in inverse form: over a prime field, `a ^ (p - 2) = a⁻¹`. -/
theorem zmod_pow_sub_two (p : ℕ) [Fact p.Prime] (a : ZMod p) (h : a ≠ 0) :
    a ^ (p - 2) = a⁻¹ := by
  have hp : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have h1 : a ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h
  have key : a * a ^ (p - 2) = 1 := by
    rw [← pow_succ']
    have e : p - 2 + 1 = p - 1 := by omega
    rw [e, h1]
  exact (inv_eq_of_mul_eq_one_right key).symm

/-- Modular inverse of `a` modulo a prime `p`, computed as `a ^ (p - 2) mod p`. -/
def invMod (a p : ℕ) : ℕ := powMod a (p - 2) p

/-- **Correctness of `invMod`.** For a prime modulus and `a` not divisible by `p`,
    `invMod a p` casts to the field inverse `(a : ZMod p)⁻¹`. -/
theorem invMod_cast (p : ℕ) [Fact p.Prime] (a : ℕ) (ha : a % p ≠ 0) :
    ((invMod a p : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
  have hne : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]; exact ha
  rw [invMod, powMod_cast, zmod_pow_sub_two p _ hne]

/-! ## Quadratic residues via Euler's criterion -/

/-- **Euler-criterion quadratic-residue witness.** For a concrete nonzero `a : ZMod p`
    with `p` prime, a kernel `decide` on `powMod a.val (p / 2) p = 1` proves `IsSquare a`. -/
theorem isSquare_of_powMod (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0)
    (h : powMod a.val (p / 2) p = 1) : IsSquare a := by
  rw [ZMod.euler_criterion p ha]
  have hc := powMod_cast a.val (p / 2) p
  rw [h, ZMod.natCast_val, ZMod.cast_id] at hc
  simpa using hc.symm

/-- **Euler-criterion non-residue witness.** For a concrete nonzero `a : ZMod p` with `p`
    prime, a kernel `decide` on `powMod a.val (p / 2) p ≠ 1` proves `¬ IsSquare a`. -/
theorem not_isSquare_of_powMod (p : ℕ) [Fact p.Prime] (a : ZMod p) (ha : a ≠ 0)
    (h : powMod a.val (p / 2) p ≠ 1) : ¬ IsSquare a := by
  rw [ZMod.euler_criterion p ha]
  intro hsq
  apply h
  have hp : 1 < p := (Fact.out (p := p.Prime)).one_lt
  have hlt := powMod_lt a.val (p / 2) p hp
  have hc := powMod_cast a.val (p / 2) p
  rw [ZMod.natCast_val, ZMod.cast_id, hsq] at hc
  have hmod : powMod a.val (p / 2) p ≡ 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using hc)
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp] at hmod

/-! ## Examples -/

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

/-- `3 ^ 10 = 59049 ≡ 4 (mod 7)`. -/
example : powMod 3 10 7 = 4 := by decide

/-- `3 ^ (7 - 2) = 243 ≡ 5 (mod 7)`, and `3 * 5 = 15 ≡ 1`, so `5` is `3⁻¹` mod `7`. -/
example : invMod 3 7 = 5 := by decide

/-- `4 = 2²` is a quadratic residue mod `7`. -/
example : IsSquare (4 : ZMod 7) := isSquare_of_powMod 7 4 (by decide) (by decide)

/-- `3` is a quadratic non-residue mod `7`. -/
example : ¬ IsSquare (3 : ZMod 7) := not_isSquare_of_powMod 7 3 (by decide) (by decide)

/-- A larger prime: `2` is a quadratic residue mod `31` (`8² = 64 ≡ 2`). -/
example : IsSquare (2 : ZMod 31) := isSquare_of_powMod 31 2 (by decide) (by decide)

/-! ## Axiom audit -/

section AxiomAudit

theorem qr_example_audit : ¬ IsSquare (3 : ZMod 7) :=
  not_isSquare_of_powMod 7 3 (by decide) (by decide)

/-- info: 'Transfer.ZModPowMod.qr_example_audit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms qr_example_audit

end AxiomAudit

end Transfer.ZModPowMod
