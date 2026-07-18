/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import ReprTransferExpr

/-!
# The relation hierarchy as classes

Trocq keeps a hierarchy of relation structures and picks, per subterm, the
weakest level a transfer needs. This module promotes the `ReprTransfer`
structures into a univalence-free class hierarchy:

  `ReprMapClass` (a map, transfers `=` forward)
    ⊂ `ReprEmbeddingClass` (+ injective, reflects `=`, so transfers `=` both ways)
    ⊂ `ReprEquivClass` (a bijection — the top level the SIP/univalence route needs).

The hierarchy bottoms out below equivalence: the crypto encodings are embeddings
(point/`Fp¹²`/word serializations are injective, not surjective), so the
equality-transfer level is `ReprEmbeddingClass`, and the layer never requires —
nor incurs the TCB cost of — univalence. The per-operation realizations
(`BinOpRealization` / `EndoOpRealization` / `BinOpHomOn` in `ReprTransfer`) are
the op-level instances built over these levels; the `repr` registry (`Trocq/Core`)
indexes them.
-/

set_option autoImplicit false

namespace Transfer

open ReprTransfer

universe u

/-- Level 0: a representation map `A → α`. Transfers an equality forward
    (`a = a' → enc a = enc a'`). -/
class ReprMapClass (A : Type u) (α : Type u) where
  /-- The encoding. -/
  enc : A → α

/-- Level 1: a representation embedding — a map that reflects equality
    (injective). Transfers a decidable equality in both directions. -/
class ReprEmbeddingClass (A : Type u) (α : Type u) extends ReprMapClass A α where
  /-- The encoding reflects equality. -/
  enc_inj : Function.Injective (enc : A → α)

/-- Equality transfers across an embedding (both directions). -/
theorem ReprEmbeddingClass.eq_iff {A α : Type u} [ReprEmbeddingClass A α] (a a' : A) :
    (ReprMapClass.enc a : α) = ReprMapClass.enc a' ↔ a = a' :=
  ReprEmbeddingClass.enc_inj.eq_iff

/-- Level 2 (top): a representation equivalence — a bijective encoding. The
    level the univalence / structure-identity route requires; the crypto
    encodings do not reach it (they are embeddings, not bijections), which is why
    the transfer layer stays univalence-free. -/
class ReprEquivClass (A : Type u) (α : Type u) extends ReprEmbeddingClass A α where
  /-- The inverse decoding. -/
  dec : α → A
  /-- `dec` is a left inverse of `enc` (hence `enc` is a bijection onto its range
      with `dec`; with `enc_inj` this is an equivalence on the image). -/
  dec_enc : ∀ a, dec (enc a) = a

/-- An `EndoOpRealization` (from `ReprTransfer`) supplies an embedding level: its
    `enc`/`enc_inj` are exactly a `ReprEmbeddingClass`. Bridges the op-level
    realizations to the relation hierarchy. -/
@[reducible] def endoOpRealizationToEmbeddingClass {A α : Type u} {op : A → A → A}
    {bop : α → α → α} (R : EndoOpRealization op bop) : ReprEmbeddingClass A α where
  enc := R.enc
  enc_inj := R.enc_inj

end Transfer
