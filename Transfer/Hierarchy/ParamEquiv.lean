/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy

/-!
# The equivalence bridge + `Param` weakening

Lifts the relation-hierarchy classes (`Trocq/Hierarchy.lean`) into the
`Param (m,n)` lattice (`ParamHierarchy.lean`) and provides the `Param`-level
weakening maps (forget structure in one direction).

## A precise observation about `ReprEquivClass`

`ReprEquivClass A α` carries `enc`, `enc_inj`, a decoder `dec : α → A`, and the
**left** inverse `dec_enc : dec (enc a) = a`. With the graph relation
`R a b := enc a = b`:

* forward is `map3` (the graph makes both inclusions identities);
* backward is `map2b` — the decoder `dec` plus `R_in_map` (`enc a = b → dec b = a`,
  proved from `dec_enc`). It is not `map2a`/`map3`, because that would need the
  right inverse `enc (dec b) = b`, which `ReprEquivClass` does not mandate (only
  the left inverse). A two-sided bijection would reach `map3`/`map4`.

So a left-inverse encoding is exactly a `Param map3 map2b` — the lattice pins down
the asymmetry that the coarse `map/embedding/equiv` view hides.
-/

set_option autoImplicit false
-- `Param.*` weakening defs live in the `Param` namespace by design (dot-notation
-- on the `Param` structure); the `Param.Param.*` shape is intentional.
set_option linter.dupNamespace false

universe u

namespace Transfer.Param

open Transfer

/-- A left-inverse encoding (`ReprEquivClass`) as a `Param map3 map2b`: forward
    `map3` (graph of `enc`), backward `map2b` (decoder `dec` + `R_in_map` from the
    left inverse `dec_enc`). -/
def paramOfEquiv {A α : Type u} [ReprEquivClass A α] : Param .map3 .map2b A α where
  R := fun a b => (ReprMapClass.enc a : α) = b
  fwd := ⟨ReprMapClass.enc, fun _ _ h => h, fun _ _ h => h⟩
  bwd :=
    -- backward: map = dec; `R_in_map : symRel R b a → dec b = a`, i.e.
    -- `enc a = b → dec b = a`, by rewriting along `enc a = b` into `dec (enc a) = a`.
    ⟨ReprEquivClass.dec, fun b a (h : (ReprMapClass.enc a : α) = b) =>
      h ▸ ReprEquivClass.dec_enc a⟩

/-! ## `Param`-level weakening (forget in the forward direction) -/

/-- Forget forward `map3` down to `map2a`. -/
def Param.fwdMap3ToMap2a {n : MapClass} {A B : Type u} (p : Param .map3 n A B) :
    Param .map2a n A B where
  R := p.R
  fwd := p.fwd.toMap2a
  bwd := p.bwd

/-- Forget forward `map3` down to `map1`. -/
def Param.fwdMap3ToMap1 {n : MapClass} {A B : Type u} (p : Param .map3 n A B) :
    Param .map1 n A B where
  R := p.R
  fwd := p.fwd.toMap2a.toMap1
  bwd := p.bwd

/-- Forget the backward structure entirely (`n → map0`). -/
def Param.bwdToMap0 {m n : MapClass} {A B : Type u} (p : Param m n A B) :
    Param m .map0 A B where
  R := p.R
  fwd := p.fwd
  bwd := ⟨⟩

/-- Demonstration: an embedding's `Param map3 map0` is the forgetful image of the
    equivalence's `Param map3 map2b` (drop the decoder). -/
example {A α : Type u} [ReprEquivClass A α] :
    Param .map3 .map0 A α := Param.bwdToMap0 paramOfEquiv

end Transfer.Param
