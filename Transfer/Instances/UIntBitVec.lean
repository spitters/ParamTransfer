/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Statements.ParamTransferTac

/-!
# Fixed-width machine words and bit vectors

The types `UInt8`, `UInt16`, `UInt32` and `UInt64` are structures over `BitVec 8`, `BitVec 16`,
`BitVec 32` and `BitVec 64`, with projection `toBitVec` and constructor `ofBitVec`. Each pair is
related by the graph `x.toBitVec = y` of the projection, which is a `Param .map3 .map3`: the
forward map is `toBitVec`, the backward map is `ofBitVec`, and both inclusions hold because the
two maps are mutually inverse.

## Main definitions

* `paramOfInverses`: the graph of a map with a two-sided inverse, as a `Param .map3 .map3`.
* `paramUInt8BitVec`, `paramUInt16BitVec`, `paramUInt32BitVec`, `paramUInt64BitVec`: the four
  word-to-bit-vector relations.
* `TransferDom` instances for the four pairs in both directions, so that `param_transfer` moves a
  quantifier between a word type and its bit-vector type.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param

/-- The graph `f a = b` of a map `f : A → B` with a two-sided inverse `g`, as a
    `Param .map3 .map3 A B`: forward map `f`, backward map `g`. -/
def paramOfInverses {A B : Type u} (f : A → B) (g : B → A) (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) : Param .map3 .map3 A B where
  R := fun a b => f a = b
  fwd := ⟨f, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨g, fun b a (h : g b = a) => by subst h; exact hfg b,
    fun b a (h : f a = b) => by subst h; exact hgf a⟩

set_option linter.dupNamespace false in
/-- The `∀`-rule domain of a `Param .map3 .map3`: the relation with the backward map. -/
def Param.toDom {A B : Type u} (p : Param .map3 .map3 A B) : Param .map0 .map2a A B where
  R := p.R
  fwd := ⟨⟩
  bwd := p.bwd.toMap2a

/-- `UInt8` and `BitVec 8`, related by `x.toBitVec = y`. -/
def paramUInt8BitVec : Param .map3 .map3 UInt8 (BitVec 8) :=
  paramOfInverses UInt8.toBitVec UInt8.ofBitVec (fun _ => rfl) (fun _ => rfl)

/-- `UInt16` and `BitVec 16`, related by `x.toBitVec = y`. -/
def paramUInt16BitVec : Param .map3 .map3 UInt16 (BitVec 16) :=
  paramOfInverses UInt16.toBitVec UInt16.ofBitVec (fun _ => rfl) (fun _ => rfl)

/-- `UInt32` and `BitVec 32`, related by `x.toBitVec = y`. -/
def paramUInt32BitVec : Param .map3 .map3 UInt32 (BitVec 32) :=
  paramOfInverses UInt32.toBitVec UInt32.ofBitVec (fun _ => rfl) (fun _ => rfl)

/-- `UInt64` and `BitVec 64`, related by `x.toBitVec = y`. -/
def paramUInt64BitVec : Param .map3 .map3 UInt64 (BitVec 64) :=
  paramOfInverses UInt64.toBitVec UInt64.ofBitVec (fun _ => rfl) (fun _ => rfl)

/-- `∀`-transfer from `UInt8` to `BitVec 8`. -/
instance instTransferDomUInt8BitVec : TransferDom UInt8 (BitVec 8) where
  dom := paramUInt8BitVec.toDom

/-- `∀`-transfer from `BitVec 8` to `UInt8`. -/
instance instTransferDomBitVecUInt8 : TransferDom (BitVec 8) UInt8 where
  dom := paramUInt8BitVec.symm.toDom

/-- `∀`-transfer from `UInt16` to `BitVec 16`. -/
instance instTransferDomUInt16BitVec : TransferDom UInt16 (BitVec 16) where
  dom := paramUInt16BitVec.toDom

/-- `∀`-transfer from `BitVec 16` to `UInt16`. -/
instance instTransferDomBitVecUInt16 : TransferDom (BitVec 16) UInt16 where
  dom := paramUInt16BitVec.symm.toDom

/-- `∀`-transfer from `UInt32` to `BitVec 32`. -/
instance instTransferDomUInt32BitVec : TransferDom UInt32 (BitVec 32) where
  dom := paramUInt32BitVec.toDom

/-- `∀`-transfer from `BitVec 32` to `UInt32`. -/
instance instTransferDomBitVecUInt32 : TransferDom (BitVec 32) UInt32 where
  dom := paramUInt32BitVec.symm.toDom

/-- `∀`-transfer from `UInt64` to `BitVec 64`. -/
instance instTransferDomUInt64BitVec : TransferDom UInt64 (BitVec 64) where
  dom := paramUInt64BitVec.toDom

/-- `∀`-transfer from `BitVec 64` to `UInt64`. -/
instance instTransferDomBitVecUInt64 : TransferDom (BitVec 64) UInt64 where
  dom := paramUInt64BitVec.symm.toDom

/-- A statement about every `UInt32` through `toBitVec` holds for every `BitVec 32`. -/
example (P : BitVec 32 → Prop) : (∀ x : UInt32, P x.toBitVec) → ∀ y : BitVec 32, P y := by
  param_transfer
  intro x y (h : x.toBitVec = y) hx
  exact h ▸ hx

/-- A statement about every `BitVec 32` holds for every `UInt32` through `toBitVec`. -/
example (P : BitVec 32 → Prop) : (∀ y : BitVec 32, P y) → ∀ x : UInt32, P x.toBitVec := by
  param_transfer
  intro y x (h : x.toBitVec = y) hy
  exact h ▸ hy

end Transfer.Param
