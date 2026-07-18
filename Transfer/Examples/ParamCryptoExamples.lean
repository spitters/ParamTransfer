/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Combinators.ParamCoherence
import Transfer.Examples.ParamCryptoDomains
import Transfer.Deriving.ParamDeriveHandler
import Transfer.Examples.PeanoBinNat

/-!
# Crypto/representation examples exercising the new pieces

This file maps the Trocq paper's worked examples onto CatCrypt's setting and
exercises the two pieces — the coherence-law suite
(`ParamCoherence`: `castViaParam`, `cast_trans`, `cast_id`, the combinator
functor laws) and the description-based `@[derive Param]` handler
(`ParamDeriveHandler`) — together with the term-level engine
(`param_transfer`/`TransferDom`, `ParamCryptoDomains`'s Baby Bear field domain,
and `PeanoBinNat`'s `Num ↔ ℕ` infrastructure).

Each section says which paper example it realizes and which piece it
exercises.

## §1 Composition-coherence chain (paper: bitvector chaining `bvR = vecR ∘ …`)

Exercises `ParamCoherence`'s `cast_trans` (AdapTT `AdaptComp`) and the
combinator functor laws on a concrete crypto carrier, the Baby Bear field
`F` (`= ZMod babyBearPrime`, the registered Poseidon2 field).

* `crypto_cast_trans_chain` — a 3-representation chain `F →[paramEqFull] F
  →[paramEqFull] F`: the composed cast equals the step-by-step cast. The paper's
  `bvR` (a bitvector relation built by *composing* two vector relations) realized
  on the field `F` — coercion through a composite relation factors as the composition
  of the two coercions.
* `crypto_cast_id` — coercion through the identity relation on `F` is the
  identity (`AdaptId`).
* `crypto_prod_trans` / `crypto_arrow_trans` — the combinator-distributes
  functor law on a *paired* (`SigPair F`-shaped `F × F`) and a *function-space*
  representation: the product/arrow of two composites equals the composite of the
  two products/arrows. This is the paper's "the cast commutes through every type
  former" coherence, on crypto carriers.

## §2 `@[derive Param]` on crypto-shaped data (paper: deriving the lift of a record)

Exercises the deriving handler: `deriving Param` on a non-dependent crypto
record/enum generates its constructor-wise relational lift `R_param`, which is
then used to relate two instances under a parameter relation.

* `ElGamalCt G` (a ciphertext pair) and `SigPair F` (a Schnorr-style `(r, s)`
  signature pair) get their `Param` lift mechanically via `deriving Param`; the
  examples relate two ciphertexts / two signatures under an element relation.
* `KeyEndo` (a key with a re-keying field `K → K`) is the mixed-variance
  non-example AdapTT rejects — `#guard_msgs`-pinned.

## §3 ℕ ↔ binary transfer (paper: `peano_bin_nat`, first-order slice)

Exercises `param_transfer`/`TransferDom` and `PeanoBinNat`'s `Num ↔ ℕ`
infrastructure: a `∀`-statement transfers across the `Num ↦ ℕ` change of
representation with the domain resolved automatically.

## §4 `Int ↔ ZMod p` retraction (paper: ring-quotient pattern) — documented

The retraction `ℤ → ZMod p` is a surjection with section `ZMod.val ∘ … : ZMod p
→ ℤ`. Building a `Param`/`TransferDom` witness for it is documented against the
annotation-inference gap rather than forced; see the section note.
-/

set_option autoImplicit false

universe u

namespace Transfer.ParamCryptoExamples

open Transfer.Param
open Transfer.ExampleField (F)

/-! ## §1 Composition-coherence chain — `cast_trans` on the Baby Bear field

The paper's bitvector example builds `bvR` by *composing* two representation
relations and relies on the cast through the composite agreeing with the
step-by-step cast. This is realized on the Baby Bear field `F`: `paramEqFull F`
is the diagonal `Param .map3 .map3 F F`, so a two-step chain
`F →[paramEqFull] F →[paramEqFull] F` is a `Param_trans_map3`, and
`cast_trans` says the composed coercion factors. -/

/-- Paper: `bvR = vecR ∘ vecR` chaining. Coercion through the
    composite field relation equals the step-by-step coercion. Exercises
    `ParamCoherence.cast_trans` (AdapTT `AdaptComp`) on the crypto carrier `F`. -/
theorem crypto_cast_trans_chain (a : F) :
    castViaParam (Param_trans_map3 (paramEqFull F) (paramEqFull F)) a
      = castViaParam (paramEqFull F) (castViaParam (paramEqFull F) a) :=
  cast_trans _ _ a

/-- `AdaptId` on `F`. Coercion through the identity field relation is the
    identity. Exercises `ParamCoherence.cast_id`. -/
theorem crypto_cast_id (a : F) : castViaParam (paramId F) a = a :=
  cast_id a

/-- Combinator functor law, product form (paper: cast commutes through `×`).
    On a paired field representation `F × F` (the carrier of a `SigPair`-shaped
    `(r, s)`), the product of two composite element relations has the same
    forward cast as the composite of the two product casts. Exercises
    `ParamCoherence.prod_trans_cast`. -/
theorem crypto_prod_trans (p : F × F) :
    (paramProd (Param_trans_map2a_map0 (paramIdElt F) (paramIdElt F))
        (Param_trans_map2a_map0 (paramIdElt F) (paramIdElt F))).fwd.map p
      = (paramProd (paramIdElt F) (paramIdElt F)).fwd.map
          ((paramProd (paramIdElt F) (paramIdElt F)).fwd.map p) :=
  prod_trans_cast _ _ _ _ p

/-- Combinator functor law, arrow form (paper: cast commutes through `→`,
    contravariantly). On the function space `F → F` (a field endomorphism, e.g.
    a key-schedule round) the arrow of two composites equals the composite of the
    two arrows — the domain composed contravariantly. Exercises
    `ParamCoherence.arrow_trans_cast`. -/
theorem crypto_arrow_trans (f : F → F) (c : F) :
    (paramArrow (Param_trans_map1 (paramId1 F) (paramId1 F))
        (Param_trans_map1 (paramId1 F) (paramId1 F))).fwd.map f c
      = (paramArrow (paramId1 F) (paramId1 F)).fwd.map
          ((paramArrow (paramId1 F) (paramId1 F)).fwd.map f) c :=
  arrow_trans_cast _ _ _ _ f c

/-! ## §2 `@[derive Param]` on crypto-shaped data types

The deriving handler (`ParamDeriveHandler`) is registered in an imported module,
so `deriving Param` here routes to it and emits the constructor-wise relational
lift `<T>.R_param`. We define crypto-shaped non-dependent carriers and use the
generated relations. -/

/-- An ElGamal-style ciphertext: a pair of group elements `(c₁, c₂)`. A
    non-dependent two-parameter record — the crypto analogue of the paper's
    "derive the lift of a record". -/
structure ElGamalCt (G : Type) where
  c1 : G
  c2 : G
  deriving Param

/-- A Schnorr-style signature pair `(r, s)` over a field/scalar carrier. -/
structure SigPair (Fr : Type) where
  r : Fr
  s : Fr
  deriving Param

/-- A parameter-free protocol-role enum (base case: the relation collapses to a
    tag match). -/
inductive Role where
  | prover | verifier
  deriving Param

/-- Generated `ElGamalCt.R_param` used. Two ciphertexts are related iff their
    components are related by the supplied element relation — the mechanically
    derived constructor-wise congruence. -/
theorem elgamal_ct_related {G G' : Type} (P : G → G' → Prop)
    (a1 a2 : G) (b1 b2 : G') (h1 : P a1 b1) (h2 : P a2 b2) :
    ElGamalCt.R_param P (ElGamalCt.mk a1 a2) (ElGamalCt.mk b1 b2) :=
  ElGamalCt.R_param.mk h1 h2

/-- Generated `SigPair.R_param` used. Two signature pairs are related from
    related `r` and `s` components. -/
theorem sigpair_related {Fr Fr' : Type} (P : Fr → Fr' → Prop)
    (r s : Fr) (r' s' : Fr') (hr : P r r') (hs : P s s') :
    SigPair.R_param P (SigPair.mk r s) (SigPair.mk r' s') :=
  SigPair.R_param.mk hr hs

/-- Generated `Role.R_param` (parameter-free). The relation collapses to a
    per-tag match. -/
theorem role_related : Role.R_param Role.prover Role.prover :=
  Role.R_param.prover

/-- Signature-check: the derived relation has the expected element-relation shape
    `(G → G' → Prop) → ElGamalCt G → ElGamalCt G' → Prop`. -/
example {G G' : Type} :
    (G → G' → Prop) → ElGamalCt G → ElGamalCt G' → Prop :=
  ElGamalCt.R_param

/-! ### Mixed-variance crypto non-example, rejected

A key carrier with a re-keying field `K → K` makes `K` mixed-variance — AdapTT's
`NonExample`. The handler rejects it; the `toIndDesc` extraction (the body of the
registered handler) raises the diagnostic, pinned with `#guard_msgs`. -/

/-- A key with a re-keying endomorphism `K → K`: `K` occurs both co- and
    contravariantly. -/
inductive KeyEndo (K : Type) where
  | mk : K → (K → K) → KeyEndo K

-- The deriving handler rejects `KeyEndo` for mixed variance: running the
-- generator's extraction (`toIndDesc`) on it raises AdapTT's `NonExample`.
/-- error: @[derive Param]: NonExample (Mixed variance) -/
#guard_msgs in
run_cmd Lean.Elab.Command.liftTermElabM do
  let _ ← toIndDesc ``KeyEndo
  pure ()

/-! ## §3 ℕ ↔ binary transfer (paper: `peano_bin_nat`, first-order slice)

`param_transfer` resolves the domain via `TransferDom`; `PeanoBinNat` registers
the `Num ↔ ℕ` embedding/equivalence and the first-order arithmetic transfer. -/

/-- Same-type `∀`-transfer (paper's univalence-free slice). A
    universally-quantified `ℕ` statement transfers with the diagonal domain
    resolved automatically by `TransferDom`; only the pointwise step is written.
    Exercises `param_transfer`/`TransferDom`. -/
theorem nat_forall_transfer (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) :
    (∀ n : ℕ, P n) → (∀ n : ℕ, Q n) := by
  param_transfer
  intro a a' (haa' : a = a') hPa
  exact haa' ▸ h a hPa

/-- Change-of-representation `∀`-transfer (`Num ↦ ℕ`, the binary-vs-unary
    flagship). The domain `Param` is the `Num → ℕ` cast graph, resolved
    automatically by `TransferDom Num ℕ`; the binary representation is invisible
    at the call site. Exercises `param_transfer` + `PeanoBinNat`'s `Num ↪ ℕ`. -/
theorem num_to_nat_forall_transfer : (∀ n : Num, 0 ≤ n) → (∀ k : ℕ, 0 ≤ k) := by
  param_transfer
  intro _ _ _ _
  exact Nat.zero_le _

/-- First-order arithmetic on the binary naturals, transferred from `ℕ`. No
    `Num` algebra is done by hand: `PeanoBinNat.num_mul_add` is the transferred
    `Nat.mul_add`. The paper's first-order `peano_bin_nat` fact. -/
theorem num_distrib_transferred (a b c : Num) : a * (b + c) = a * b + a * c :=
  PeanoBinNat.num_mul_add a b c

/-! ## §4 `Int ↔ ZMod p` retraction — documented, not fabricated

The ring-quotient `ℤ ↠ ZMod p` is the paper's retraction pattern: `Int.cast :
ℤ → ZMod p` is surjective with section `(ZMod.val · : ZMod p → ℤ)` (for `p`
positive), and `ZMod.intCast_zmod_cast`/`ZMod.natCast_val` give the round-trip
on one side only (`Int.cast ∘ section = id` on `ZMod p`, but `section ∘ Int.cast`
is reduction-mod-`p`, *not* the identity on `ℤ`).

This is therefore a retraction, not an equivalence: it sits at the
`map2a`/`map0` (section + `map_in_R`) level a `TransferDom` consumes only in the
`ZMod p → ℤ` direction. A `TransferDom (ZMod p) ℤ` would deliver a pointwise
obligation phrased against the *integer* predicate, which — exactly as
`ParamCryptoDomains`'s "non-diagonal case" note records for the field↔limb
decoder — the caller must currently supply by hand; the engine cannot yet infer
it. The missing capability is the annotation inference described in
`ParamTrocq`'s module docstring (full `⟦t⟧` with per-subterm levels), not a
missing Mathlib primitive. The witness shape is documented here rather than
providing a `TransferDom` whose pointwise obligation is trivial/vacuous.

§5 (the `Summable`/`SPComp` transfer) is the heavy-crypto analogue of the same
pattern and is likewise not handled here.
-/

/-! ## Axiom audit

The coherence and engine demos. `cast_trans`/`cast_id`-backed results
are `rfl`-clean; the `param_transfer` demos use `propext`/`funext` only through
the abstraction-theorem combinator. -/

section AxiomAudit

/-- info: 'Transfer.ParamCryptoExamples.crypto_cast_trans_chain' does not depend on any axioms -/
#guard_msgs in
#print axioms crypto_cast_trans_chain

/-- info: 'Transfer.ParamCryptoExamples.crypto_cast_id' does not depend on any axioms -/
#guard_msgs in
#print axioms crypto_cast_id

end AxiomAudit

end Transfer.ParamCryptoExamples
