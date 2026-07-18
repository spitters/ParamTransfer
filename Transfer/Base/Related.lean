/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Examples.ExampleField

/-!
# `Related` — transfer by instance resolution

A foundational kernel of a Trocq-style relatedness layer whose typeclass
instance resolution composes a transfer automatically for closed first-order
op-trees. The relation is an encoding: `Related enc a b` means `b` is the
encoding `enc a` of the abstract value `a`.

Given:

* a leaf fact "the encoding of a value is related to it" (`leaf`/`leafId`), and
* per-operation **commuting squares** (`RelatedBinOp`: `enc (op x y) =
  bop (enc x) (enc y)`), each a *registered witness* (never invented here —
  the soundness lives entirely in the supplied `RelatedBinOp` instance),

the composition instance `composeBinOp` lets instance resolution synthesize a
`Related enc t (T)` for any closed term `t` built from registered binary ops,
where `T` is the corresponding emitted op-tree. The corollary `transferRel`
then extracts the underlying equation `enc t = T`.

## Demonstration

The emitted Baby Bear field arithmetic
(`Bridges.ReprTransferInstances.bbFieldMul`/`bbFieldAdd`, proved equal to the
abstract `*`/`+` via `bbFieldMul_eq`/`bbFieldAdd_eq`) is registered as
`RelatedBinOp` instances with the identity encoding. Instance resolution then
composes the transfer of a composite expression with no manual proof:

```
a * b + c  =  bbFieldAdd (bbFieldMul a b) c
```

is closed purely by `(inferInstance : Related id _ _).rel`.

## Scope and limits

* Closed first-order only. The composition handles op-trees over registered
  binary operations on a single carrier `A` with a single encoding `enc`. There
  is no support for binders, parametric/higher-order operations, mixed
  carriers, or relation polymorphism (the full Trocq hierarchy of relation
  classes). This is a small kernel.
* Encoding-correctness is the `RelatedBinOp` witness. The commuting square
  for each operation must be supplied as a proved instance; this file does not
  supply it. The transfer is only as sound as the registered witnesses.
* The `id` encoding needs its own leaf. Instance resolution keys on
  syntactic heads and does not reduce `id a` to `a` while matching, so the
  generic `leaf` (head `Related enc a (enc a)`) cannot serve the identity
  encoding in the demonstration. A dedicated low-priority `leafId` (head
  `Related id a a`) supplies it. Both leaves are `priority := low` so the
  structural `composeBinOp` is preferred and resolution does not loop on a leaf.
-/

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField

universe u

/-- `Related enc a b`: the value `b` is the encoding `enc a` of the abstract
    value `a`. The relation is the encoding — its single field is the
    equation `enc a = b`. -/
class Related {A α : Type u} (enc : A → α) (a : A) (b : α) : Prop where
  /-- `b` is exactly the encoding of `a`. -/
  rel : enc a = b

/-- A registered realization of a binary operation: the commuting square
    `enc (op x y) = bop (enc x) (enc y)`. This is the witness that the
    emitted operation `bop` realizes the abstract operation `op` along `enc`.
    It is always supplied; the transfer is sound exactly to the extent this
    square is. -/
class RelatedBinOp {A α : Type u} (enc : A → α) (op : A → A → A) (bop : α → α → α) :
    Prop where
  /-- The commuting square for this operation. -/
  comm : ∀ x y, enc (op x y) = bop (enc x) (enc y)

/-- Composition. If `bop` realizes `op` (a registered `RelatedBinOp`) and
    `a'`, `b'` are the encodings of `a`, `b`, then `bop a' b'` is the encoding
    of `op a b`. This is the instance that makes resolution compose the
    transfer through an op-tree. -/
instance composeBinOp {A α : Type u} (enc : A → α) (op : A → A → A) (bop : α → α → α)
    (a b : A) (a' b' : α)
    [hop : RelatedBinOp enc op bop] [ha : Related enc a a'] [hb : Related enc b b'] :
    Related enc (op a b) (bop a' b') where
  rel := (hop.comm a b).trans (by rw [ha.rel, hb.rel])

/-- Leaf (generic encoding). The encoding of a value is related to it.
    Low priority so the structural `composeBinOp` is tried first and resolution
    terminates at leaves rather than looping. -/
instance (priority := low) leaf {A α : Type u} (enc : A → α) (a : A) :
    Related enc a (enc a) where
  rel := rfl

/-- Leaf for the identity encoding. Needed because instance resolution
    keys on syntactic heads and will not reduce `id a` to `a`; this gives the
    head `Related id a a` directly. -/
instance (priority := low) leafId {α : Type u} (a : α) : Related (id : α → α) a a where
  rel := rfl

/-- Transfer corollary. A synthesized `Related enc a b` yields the
    underlying equation `enc a = b`. -/
theorem transferRel {A α : Type u} {enc : A → α} {a : A} {b : α}
    (h : Related enc a b) : enc a = b := h.rel

/-! ## Demonstration: the emitted Baby Bear field as registered operations -/

/-- The emitted Baby Bear field multiply realizes abstract `*` (identity
    encoding). Witness: `bbFieldMul_eq`. -/
instance bbMulRelated : RelatedBinOp (id : F → F) (· * ·) bbFieldMul where
  comm a b := (bbFieldMul_eq a b).symm

/-- The emitted Baby Bear field add realizes abstract `+` (identity encoding).
    Witness: `bbFieldAdd_eq`. -/
instance bbAddRelated : RelatedBinOp (id : F → F) (· + ·) bbFieldAdd where
  comm a b := (bbFieldAdd_eq a b).symm

/-- Resolution finds the identity leaf. -/
example (a : F) : Related (id : F → F) a a := inferInstance

/-- Resolution composes a single registered operation. -/
example (a b : F) : Related (id : F → F) (a * b) (bbFieldMul a b) := inferInstance

/-- Instance resolution synthesizes the transfer of the composite expression
    `a * b + c` to its emitted op-tree `bbFieldAdd (bbFieldMul a b) c` — with no
    manual proof. The equation is extracted by `.rel` (equivalently
    `transferRel inferInstance`). -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c :=
  (inferInstance : Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c)).rel

/-- Same payoff, routed through the `transferRel` corollary. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c :=
  transferRel (a := a * b + c)
    (inferInstance :
      Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c))

end Transfer
