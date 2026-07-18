/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransferTac
import Transfer.Hierarchy.ParamEquiv
import Mathlib.Data.List.Basic

/-!
# `hex`'s dense polynomial storage: a non-injective refinement at `map2a`

`leanprover/hex`'s polynomial machinery (Berlekamp–Zassenhaus factoring, Hensel
lifting) stores a polynomial as a **dense coefficient list** — the CoqEAL
`seqpoly` representation. That storage is *not injective* as a refinement of the
mathematical polynomial: trailing zeros are redundant, so `[1,2]` and `[1,2,0]`
denote the same polynomial `2X + 1`. This module builds that refinement and
pins down the exact `Param` level it reaches (`possibility 2`): a genuinely
**non-bijective** refinement lands at forward/backward `map2a`, the graded
engine's sweet spot, and provably *cannot* reach `map2b`/`map3`/`map4` — the
levels an `Equiv`-based or univalent transfer would demand.

## The refinement relation

Two dense lists are related when their coefficient functions agree:

  `SameCoeff l l' := ∀ i, l.getD i 0 = l'.getD i 0`.

This is exactly the seqpoly refinement (agree as polynomials). It is reflexive,
symmetric, transitive, and *strictly coarser than equality* — the quotient by
trailing zeros. The abstract polynomial is the `SameCoeff`-class; the two carrier
types coincide (`List ℤ`) because the quotient lives in the relation, not the
type. Reaching Mathlib's `Polynomial ℤ` as the abstract side (via `Polynomial.coeff`)
is an orthogonal finite-support packaging and does not change the level analysis.

## Why the level is exactly `map2a`

`seqPolyParam : Param .map2a .map2a` carries `SameCoeff` with the identity map
each way: `map_in_R` (`map l = l' → SameCoeff l l'`) is reflexivity after `subst`,
so `map2a` holds in both directions. But `map2b`'s `R_in_map`
(`SameCoeff l l' → id l = l'`, i.e. `SameCoeff l l' → l = l'`) is **false**:
`seqPoly_not_injective` exhibits `SameCoeff [1,2] [1,2,0]` with `[1,2] ≠ [1,2,0]`.
So the refinement stops at `map2a`; `map3` (both inclusions) and `map4`
(univalent) are a fortiori unreachable. This is the structural reason the
graded hierarchy is the right tool for `hex`'s storage: a two-sided-equivalence
framework would reject this refinement outright; `map2a` is precisely what
`forallTransfer`/`TransferDom` consume.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Transfer.Param

open Transfer

/-! ## The dense polynomial carrier and its coefficient view -/

/-- `hex`'s dense polynomial storage: a coefficient list (low degree first). -/
abbrev HexPoly : Type := List ℤ

/-- The coefficient at degree `i` (out-of-range degrees are `0`). -/
def coeffOf (l : HexPoly) (i : ℕ) : ℤ := l.getD i 0

/-- The seqpoly refinement relation: two dense lists denote the same polynomial
    when all coefficients agree. Reflexive, and strictly coarser than equality
    (trailing zeros are identified). -/
def SameCoeff (l l' : HexPoly) : Prop := ∀ i, coeffOf l i = coeffOf l' i

theorem SameCoeff.refl (l : HexPoly) : SameCoeff l l := fun _ => rfl

/-! ## The refinement witness — forward/backward `map2a`, no higher -/

/-- The seqpoly refinement as a `Param .map2a .map2a HexPoly HexPoly`. Each
    direction uses the identity map with `map_in_R` discharged by reflexivity
    (`map l = l' → SameCoeff l l'` after `subst`). It reaches `map2a` both ways
    but *not* `map2b` (see `seqPoly_not_injective`). -/
def seqPolyParam : Param .map2a .map2a HexPoly HexPoly where
  R := SameCoeff
  fwd := ⟨id, fun l l' (h : id l = l') => by subst h; exact SameCoeff.refl l⟩
  bwd := ⟨id, fun l l' (h : id l = l') => by subst h; exact SameCoeff.refl l⟩

/-! ## The `map2a` boundary: non-injectivity refutes `map2b`/`map3` -/

/-- `[1,2]` and `[1,2,0]` have identical coefficients (`2X + 1`): the trailing
    zero is redundant. -/
theorem sameCoeff_snoc_zero_pair : SameCoeff [1, 2] [1, 2, 0] := by
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (n + 3) => simp [coeffOf, List.getD_eq_getElem?_getD]

/-- The refinement is non-injective: `SameCoeff` holds between distinct lists.
    This refutes `map2b`'s inclusion `R_in_map : SameCoeff l l' → l = l'` (with
    the identity map), so the witness cannot be promoted past `map2a`. The
    non-bijectivity is *forced by the representation* (trailing zeros), not an
    artefact of the proof. -/
theorem seqPoly_not_injective : ∃ l l' : HexPoly, SameCoeff l l' ∧ l ≠ l' :=
  ⟨[1, 2], [1, 2, 0], sameCoeff_snoc_zero_pair, by decide⟩

/-! ## Transferring a coefficient-invariant property across the quotient

The domain at the `∀`-rule level `(.map0, .map2a)` forgets the forward `map2a` of
`seqPolyParam`. `param_transfer` then moves any coefficient-invariant statement
across trailing-zero padding — a property proved for one dense representation
holds for every `SameCoeff`-equivalent one. -/

/-- The seqpoly refinement at the level `forallTransfer`/`TransferDom` consume. -/
def seqPolyDom : Param .map0 .map2a HexPoly HexPoly where
  R := SameCoeff
  fwd := ⟨⟩
  bwd := seqPolyParam.bwd

instance instTransferDomSeqPoly : TransferDom HexPoly HexPoly where
  dom := seqPolyDom

/-- A coefficient-invariant fact transfers across the quotient: the constant
    coefficient being `c` is preserved by trailing-zero padding, obtained by the
    engine from the `SameCoeff` relation at degree `0`. -/
example (c : ℤ) :
    (∀ l : HexPoly, coeffOf l 0 = c) → (∀ l' : HexPoly, coeffOf l' 0 = c) := by
  param_transfer
  intro l l' (h : SameCoeff l l') hc
  rw [← h 0]; exact hc

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.seqPolyParam' depends on axioms: [propext] -/
#guard_msgs in
#print axioms seqPolyParam

end AxiomAudit

end Transfer.Param
