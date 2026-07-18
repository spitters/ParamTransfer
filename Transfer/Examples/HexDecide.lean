/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import ReprTransfer
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Discharging a `hex` side condition by computation on the concrete rep

`leanprover/hex` discharges algorithm side conditions by kernel computation:
`HexLLL` closes its reduction-factor obligations with `by decide +kernel`, and
the fraction-free `HexBareiss` update relies on exact-divisibility facts. The
common shape is: an *abstract* equation (in the mathematical structure) is decided
by *computing on the concrete representation* and comparing. That is exactly the
minimal-level transfer `ReprTransfer` provides — a codomain embedding plus a
commuting square gives `BinOpRealization.eq_transfer`, turning the abstract
equation into a decidable comparison on the concrete side (`possibility 4`).

This module builds two realizations covering both hierarchy levels `ReprTransfer`
documents, in `hex`'s setting of **reduction modulo a pivot** (the residue
arithmetic Bareiss/LLL perform):

* `residueMulReal` — a `BinOpRealization` of multiplication in `ZMod m` by
  integer multiply-then-`%m`, along the injective encoding `ZMod m ↪ ℤ` (`val`).
  Its `eq_transfer` lets `by decide` on the integer residues *prove an abstract
  `ZMod` equation* — the `decide +kernel` discipline, justified by the commuting
  square rather than trusted.
* `reduceHom` — a `BinOpHomOn`: the reduction map `ℤ → ZMod m` is a homomorphism,
  the map-level (no-injectivity) transfer that `hex`'s fraction-free step uses
  when *decoding* a concrete result to the abstract value.

The encoding `ZMod m ↪ ℤ` is injective but not surjective (not every integer is a
canonical residue), so the realization sits at the *embedding* level — never the
equivalence/univalence level — exactly as `ReprTransfer`'s hierarchy note states.
-/

set_option autoImplicit false

open ReprTransfer

namespace Transfer.Param

/-! ## The residue embedding `ZMod m ↪ ℤ` -/

/-- The canonical-representative encoding `ZMod m → ℤ` (`val`, cast to `ℤ`) as a
    `ReprEmbedding`: injective (distinct residues have distinct canonical
    representatives), but not surjective — the embedding level, not equivalence. -/
def residueEmb (m : ℕ) [NeZero m] : ReprEmbedding (ZMod m) ℤ where
  enc := fun a => (a.val : ℤ)
  enc_inj := by
    intro a b h; simp only at h
    exact ZMod.val_injective m (by exact_mod_cast h)

/-! ## The residue-multiplication realization (embedding level) -/

/-- Multiplication in `ZMod m` realized by integer multiply-then-reduce
    (`fun x y => (x * y) % m`), along the residue encoding. The commuting square
    is `ZMod.val_mul` cast to `ℤ`. This is the structure `hex`'s modular side
    conditions have: an abstract residue product equals the reduced integer
    product of the canonical representatives. -/
def residueMulReal (m : ℕ) [NeZero m] :
    BinOpRealization (fun a b : ZMod m => a * b) (fun x y : ℤ => (x * y) % (m : ℤ)) where
  encA := fun a => (a.val : ℤ)
  encB := fun b => (b.val : ℤ)
  cod := residueEmb m
  commutes := fun a b => by
    show ((a * b).val : ℤ) = ((a.val : ℤ) * (b.val : ℤ)) % (m : ℤ)
    rw [ZMod.val_mul]; push_cast; ring

/-- **`decide +kernel`, justified by transfer.** An abstract `ZMod 5` equation is
    discharged purely by kernel computation on the integer residues: `eq_transfer`
    reduces `(2 * 3 : ZMod 5) = (1 * 1 : ZMod 5)` to the decidable integer
    comparison `(2 * 3) % 5 = (1 * 1) % 5`, closed by `decide`. The abstract fact
    is proved *by computing on the concrete representation* — `hex`'s discipline,
    with the reduction step underwritten by `residueMulReal`'s commuting square
    instead of trusted. -/
example : (2 * 3 : ZMod 5) = (1 * 1 : ZMod 5) :=
  (residueMulReal 5).eq_transfer_backward (by decide)

/-- The soundness direction: an abstract residue equation forces the concrete
    integer comparison to hold (the check never spuriously fails). -/
example (a a' b b' : ZMod 5) (h : a * b = a' * b') :
    ((a.val : ℤ) * (b.val : ℤ)) % 5 = ((a'.val : ℤ) * (b'.val : ℤ)) % 5 :=
  (residueMulReal 5).eq_transfer_forward h

/-! ## The reduction homomorphism (map level) -/

/-- The reduction map `ℤ → ZMod m` is a multiplication homomorphism: decoding the
    concrete integer product to `ZMod m` equals the abstract product of the
    decoded operands. This is `ReprTransfer`'s weaker, map-only level (no
    injectivity) — the shape of `hex`'s fraction-free step, where a concrete
    result is *decoded* to its abstract meaning on a canonical subdomain
    (here total: `dom = fun _ => True`). -/
def reduceHom (m : ℕ) :
    BinOpHomOn (fun x : ℤ => (x : ZMod m)) (fun _ => True)
      (fun a b => a * b) (fun a b => a * b) where
  app_eq := fun a b _ _ => by push_cast; ring

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.residueMulReal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms residueMulReal

end AxiomAudit

end Transfer.Param
