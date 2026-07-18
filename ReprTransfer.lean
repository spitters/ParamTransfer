/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Representation transfer for emit-realization bridges

A small, protocol-agnostic proof-transfer layer for a recurring CatCrypt
pattern: a security proof quantifies over an abstract (often `noncomputable`,
classical) operation, while the emitted/compiled artifact computes a
computational (byte-level) operation, and a chosen encoding ties the two. Each
such bridge — KZG's byte↔group pairing
(`Bridges/ArkLibKZGDemo/ByteGroupRealization.lean`), and the analogous
ML-KEM/ML-DSA/STARK emit-realization ties — is written by hand as a bespoke
`structure` + `iff`. This module factors out the shared content: the relation
structure and the generic transfer theorem.

## Lineage

This layer follows Kaliszyk & O'Connor, *Computing with Classical Real
Numbers* (JFR 2009, arXiv:0809.1644), who transfer theorems across an
isomorphism between Coq's classical reals and CoRN's computational reals, and
forms a hand-built, fixed-relation instance of Trocq (Cohen–Crance–Mahboubi,
ESOP 2024 / TOPLAS 2025, arXiv:2310.14022), whose hierarchy of relation
structures performs "a fine-grained analysis of the properties required for a
given proof of relatedness." This file identifies the minimal level for
transferring a decidable equation: the domains need only a map, and the codomain
needs an embedding (an equality-reflecting, i.e. injective, encoding) — no
equivalence, no univalence. Mathlib's `@[to_additive]` is the only built-in Lean
transfer mechanism, but it is single-axis (multiplicative↔additive); this layer
handles an arbitrary user-supplied representation relation, which the
emit-realization bridges require.

## Main definitions

* `ReprEmbedding C γ` — an equality-reflecting encoding `C → γ`.
* `BinOpRealization op bop` — `op : A → B → C` realized by `bop : α → β → γ`
  along domain maps + a codomain embedding + a commuting square.
* `BinOpRealization.eq_transfer` — the transfer theorem: an abstract equation
  `op a b = op a' b'` holds iff `bop` agrees on the encoded operands.
-/

set_option autoImplicit false

namespace ReprTransfer

universe u

/-! ## Representation embedding (the codomain level) -/

/-- A representation embedding: a map `C → γ` that reflects equality
    (injective). This is the minimal relatedness needed to transfer a decidable
    equation across the representation in both directions: forward needs only
    a map, backward needs injectivity. -/
structure ReprEmbedding (C : Type u) (γ : Type u) where
  /-- The encoding of abstract values as computational ones. -/
  enc : C → γ
  /-- Distinct abstract values encode distinctly (equality reflection). -/
  enc_inj : Function.Injective enc

namespace ReprEmbedding
variable {C : Type u} {γ : Type u}

/-- Equality reflects across the embedding. -/
@[simp] theorem eq_iff (e : ReprEmbedding C γ) (a a' : C) :
    e.enc a = e.enc a' ↔ a = a' :=
  e.enc_inj.eq_iff

end ReprEmbedding

/-! ## Binary-operation realization -/

/-- A binary-operation realization: the abstract operation `op : A → B → C`
    is realized by the computational operation `bop : α → β → γ` along domain
    encodings `encA`/`encB` (plain maps) and a codomain embedding `cod`, via the
    commuting square `cod.enc (op a b) = bop (encA a) (encB b)`.

    The asymmetry — maps on the domains, an embedding on the codomain — is
    the structure that transfers a decidable equation between `op`
    applications (`eq_transfer`). It is the Trocq-hierarchy level for this goal:
    weaker than an equivalence, requiring neither surjectivity of the encodings
    nor univalence. -/
structure BinOpRealization {A B C : Type u} {α β γ : Type u}
    (op : A → B → C) (bop : α → β → γ) where
  /-- Encoding of the first operand. -/
  encA : A → α
  /-- Encoding of the second operand. -/
  encB : B → β
  /-- Equality-reflecting encoding of the result. -/
  cod  : ReprEmbedding C γ
  /-- The commuting square tying `op` to `bop` through the encodings. -/
  commutes : ∀ (a : A) (b : B), cod.enc (op a b) = bop (encA a) (encB b)

namespace BinOpRealization
variable {A B C : Type u} {α β γ : Type u} {op : A → B → C} {bop : α → β → γ}

/-- The transfer theorem. An abstract equation between two applications of
    `op` holds iff the computational `bop` agrees on the encoded operands.

    A verification predicate phrased as `op a b = op a' b'` (e.g. a pairing-check
    `e(X,Y) = e(X',Y')`) is decided, equivalently, by the byte-level comparison the
    emitted code computes. -/
theorem eq_transfer (R : BinOpRealization op bop) (a a' : A) (b b' : B) :
    op a b = op a' b' ↔
      bop (R.encA a) (R.encB b) = bop (R.encA a') (R.encB b') := by
  rw [← R.commutes, ← R.commutes]
  exact ⟨fun h => by rw [h], fun h => R.cod.enc_inj h⟩

/-- The forward (soundness) direction: an abstract equality implies the byte
    comparison succeeds. Needs only the commuting square, not injectivity. -/
theorem eq_transfer_forward (R : BinOpRealization op bop) {a a' : A} {b b' : B}
    (h : op a b = op a' b') :
    bop (R.encA a) (R.encB b) = bop (R.encA a') (R.encB b') :=
  (R.eq_transfer a a' b b').mp h

/-- The backward (completeness) direction: the byte comparison succeeding
    implies the abstract equality. Uses codomain injectivity. -/
theorem eq_transfer_backward (R : BinOpRealization op bop) {a a' : A} {b b' : B}
    (h : bop (R.encA a) (R.encB b) = bop (R.encA a') (R.encB b')) :
    op a b = op a' b' :=
  (R.eq_transfer a a' b b').mpr h

end BinOpRealization

/-! ## The relation hierarchy (Trocq's "fine-grained analysis", made explicit)

Which transfer needs which structure:
* a plain map (`enc : C → γ`) transfers an op-application forward
  (a homomorphism) — `BinOpHomOn`;
* an embedding (`+ enc_inj`) additionally reflects equality, so it transfers
  a decidable equation in both directions — `ReprEmbedding` / `BinOpRealization.eq_transfer`;
* an equivalence (a bijection) is the top level the univalence / SIP route
  requires — which the crypto encodings (point/`Fp¹²` serialization is injective
  but not surjective: most byte strings aren't valid) do not reach, so this
  layer never requires it and never incurs univalence. -/

/-- Top of the hierarchy: a representation equivalence (bijection). Refines
    to an embedding. Recorded for completeness; the emit-realization bridges do
    not use this level (their encodings are embeddings, not bijections),
    which is why they stay univalence-free. -/
abbrev ReprEquiv (C : Type u) (γ : Type u) := C ≃ γ

/-- An equivalence forgets to an embedding (a bijection is injective). -/
def ReprEquiv.toReprEmbedding {C γ : Type u} (e : ReprEquiv C γ) : ReprEmbedding C γ :=
  ⟨e.toFun, e.injective⟩

/-! ## Domain-restricted operation homomorphism (the map-level transfer)

The emitted-field-arithmetic realizations (STARK / ML-KEM Baby Bear / `Fp`
kernels) are not codomain-embedding equality transfers; they are homomorphisms
along a decoding map `φ`, valid on a canonical sub-domain (e.g. words `< p`).
This is a strictly weaker hierarchy level than `BinOpRealization` — map-only, no
injectivity — and packaging it here lets those bridges share the layer. -/

/-- A domain-restricted binary-operation homomorphism: along a map
    `φ : α → A`, the concrete `src` maps through `φ` to the abstract `tgt`, on
    a canonical sub-domain `dom` (the `< p` canonical-range condition the field
    kernels carry). Map-level: no injectivity required. -/
structure BinOpHomOn {α A : Type u} (φ : α → A) (dom : α → Prop)
    (src : α → α → α) (tgt : A → A → A) where
  /-- The homomorphism square, on the canonical sub-domain. -/
  app_eq : ∀ a b, dom a → dom b → φ (src a b) = tgt (φ a) (φ b)

namespace BinOpHomOn
variable {α A : Type u} {φ : α → A} {dom : α → Prop}
variable {src : α → α → α} {tgt : A → A → A}

/-- The realization equation: on canonical inputs, decoding the concrete result
    equals the abstract operation on the decoded inputs. -/
theorem realizes (H : BinOpHomOn φ dom src tgt) {a b : α} (ha : dom a) (hb : dom b) :
    φ (src a b) = tgt (φ a) (φ b) := H.app_eq a b ha hb

end BinOpHomOn

end ReprTransfer
