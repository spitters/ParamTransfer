/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransferTac
import Transfer.Translate.ParamTranslateFull
import Transfer.Base.Related
import Transfer.Base.FieldRegistry
import Transfer.Integrations.ParamRelatedBridge

/-!
# The Baby Bear field as a first-class transfer domain (stack fusion)

The other `Param`-engine domains are small: the diagonal `Eq` and the
`Num ↦ ℕ` change-of-representation (`ParamTrocq.instTransferDomNumNat`). This
module promotes a crypto carrier — the
emitted Baby Bear field kernels (`bbFieldMul`/`bbFieldAdd`, proved equal to the
abstract `*`/`+` via `bbFieldMul_eq`/`bbFieldAdd_eq`) — into first-class
transfer data, and fuses the two transfer stacks over the same field:

* Stack B (`Related`). `Related.lean` registers the field ops as
  `RelatedBinOp` instances (`bbMulRelated`/`bbAddRelated`) and composes a
  transfer of a closed op-tree by instance resolution (`composeBinOp`),
  extracted by `transferRel`/`.rel`. Driven by `rcongr`/`param_solve`.
* Stack A (`Param`). `ParamDB` resolves `@[param]`-registered
  `RArrow PA PB c c'` witnesses for the term-level translation `⟦·⟧`
  (`#transfer`/`translateAll`); `ParamTrocq.TransferDom` resolves the domain for
  the `∀`-rule (`param_transfer`/`forallTransferAuto`).

Without this file these two stacks share a field but not a registry: the Baby
Bear ops live only in Stack B. This file registers the *same* operations into
Stack A as `@[param]` `RArrow` witnesses and adds a Baby Bear `TransferDom`, so a
single field operation is usable by both engines.

## What is registered

1. `@[param]` field witnesses (Stack A). `bbMulParam`/`bbAddParam` prove
   `RArrow Eq (RArrow Eq Eq) (· * ·) bbFieldMul` (resp. `+`/`bbFieldAdd`) from
   `bbFieldMul_eq`/`bbFieldAdd_eq`. `@[param]` keys them under the abstract
   operator heads (`HMul.hMul`/`HAdd.hAdd`), so `getParamDB`/`translateAll`
   resolve the field ops by the *same* witness that proves Stack B's square.
2. A Baby Bear `TransferDom`. `instTransferDomBabyBear : TransferDom F F` so
   `param_transfer` transfers `∀ (x : F), P x`-style statements over the field.
   It is the diagonal domain (graph `Eq` on `F`) — see the *non-diagonal
   case* below for why a field↔limb domain needs more than the
   current `TransferDom` shape can express.

## The non-diagonal case

`TransferDom A A'` carries a `Param .map0 .map2a A A'`: a backward section
`A' → A` with `map_in_R`. The Baby Bear *representation change* is
`F ↔ BitVec`-style limbs through `bbEncode`/`bbToF`; a non-diagonal
`TransferDom F BitVec`-style domain would need that backward decoder packaged at
`map2a` (it exists — `bbToF_bbEncode` is the round-trip), but the `∀`-rule then
delivers a *pointwise* obligation phrased against the *limb* predicate `P'`,
which the caller must supply by hand. The annotation-inference gap (`ParamTrocq`
module docstring's note on the full `⟦t⟧` over arbitrary terms with
per-subterm levels) is exactly what would let the engine infer that limb
predicate instead. So this file registers the diagonal field domain (complete
for same-representation field transfer) and the op-level
representation change lives in the `@[param]`/`RelatedBinOp` op witnesses, which
carry the `F ↔ bbField*` change.
-/

set_option autoImplicit false

namespace Transfer

open Transfer.ExampleField
open Transfer.Param

/-! ## Stack-A registration: the field ops as `@[param]` `RArrow` witnesses

These are the *same* field realizations that Stack B carries as
`RelatedBinOp` (`bbMulRelated`/`bbAddRelated`). Rather than a second proof, the
Stack-A `RArrow` witnesses are *derived* from those squares by the single source
of truth `paramWitnessOfRelatedBinOp` (`Integrations/ParamRelatedBridge.lean`):
register the `RelatedBinOp` once, and the `@[param]` witness is a one-liner
citing it — the `bbFieldMul_eq`/`bbFieldAdd_eq` proof lives in exactly one place. -/

/-- Baby Bear multiply, Stack-A witness. `RArrow Eq (RArrow Eq Eq)` is the
    curried function relation for a binary op: on `Eq`-related arguments the
    abstract `*` and the emitted `bbFieldMul` agree. Registered with `@[param]`
    (keyed under `HMul.hMul`). Derived from the `RelatedBinOp` square
    `bbMulRelated` — one registration, both engines. -/
@[param] theorem bbMulParam :
    RArrow Eq (RArrow Eq Eq) (HMul.hMul : F → F → F) bbFieldMul :=
  paramWitnessOfRelatedBinOp (enc := id) (op := (· * ·)) (bop := bbFieldMul)

/-- Baby Bear add, Stack-A witness. As `bbMulParam`, for `+`/`bbFieldAdd`,
    keyed under `HAdd.hAdd`. Derived from the `RelatedBinOp` square
    `bbAddRelated`. -/
@[param] theorem bbAddParam :
    RArrow Eq (RArrow Eq Eq) (HAdd.hAdd : F → F → F) bbFieldAdd :=
  paramWitnessOfRelatedBinOp (enc := id) (op := (· + ·)) (bop := bbFieldAdd)

/-! ## Stack-A domain: the Baby Bear field as a `TransferDom`

A `TransferDom F F` (the diagonal field domain) so `param_transfer` /
`forallTransferAuto` transfer `∀ (x : F), P x`-style statements over the field
with the domain `Param` resolved by instance — the field plays the role `Num`
played, but as a crypto carrier. -/

/-- Baby Bear `TransferDom`. Resolves the domain `Param .map0 .map2a F F`
    (the diagonal, graph `Eq` on the field) for `param_transfer`. Definitionally
    `paramDiag`, so the pointwise obligation on related pairs `(x, x')` is
    `x = x'`. This is the same-representation field domain; the op-level
    representation change is carried by `bbMulParam`/`bbAddParam` and the
    `RelatedBinOp` squares. -/
instance instTransferDomBabyBear : TransferDom F F where
  dom := paramDiag

/-- The Baby Bear field domain resolved by `TransferDom` is exactly `paramDiag`,
    so field `∀`-transfer runs on the diagonal with no caller input. -/
example : (TransferDom.dom (A := F) (A' := F)) = paramDiag := rfl

/-! ## Doc-tests: both stacks close Baby Bear field goals

These pinned `example`s back the README's prose snippets.
They exercise, on the *same* field operations:
Stack B (`Related`/`transferRel`), Stack A `@[param]` witnesses, and the
`param_transfer` `∀`-rule over the field `TransferDom`. -/

/-- Stack B (Related). Instance resolution synthesizes the transfer of the
    composite `a * b + c` to its emitted op-tree, extracted by `.rel`. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c :=
  (inferInstance :
    Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c)).rel

/-- Stack A (`@[param]` multiply witness). The registered `RArrow` witness
    `bbMulParam` is the transfer of `*` to `bbFieldMul`; applied at reflexive
    arguments it yields the field equation directly. -/
example (a b : F) : a * b = bbFieldMul a b := bbMulParam a a rfl b b rfl

/-- Stack A (`@[param]` add witness). Likewise for `+`/`bbFieldAdd`. -/
example (a b : F) : a + b = bbFieldAdd a b := bbAddParam a a rfl b b rfl

/-- Stacks fused — one goal, both registries. The composite is closed by
    the Stack-A `RArrow` witnesses composed by hand, matching the Stack-B
    `Related` result above bit for bit (`bbFieldAdd (bbFieldMul a b) c`). -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c :=
  bbAddParam (a * b) (bbFieldMul a b) (bbMulParam a a rfl b b rfl) c c rfl

/-- `param_transfer` over the field `TransferDom`. A universally-quantified
    field statement transfers across the diagonal field domain, resolved
    automatically — the caller names nothing structural, as for the
    `Num`/`ℕ` example, but over a crypto carrier. -/
example (P Q : F → Prop) (h : ∀ x, P x → Q x) :
    (∀ x : F, P x) → (∀ x : F, Q x) := by
  param_transfer
  intro a a' (haa' : a = a') hPa
  exact haa' ▸ h a hPa

/-- A `∀`-quantified field equation transferred across the resolved field
    domain: `(∀ x : F, x * 1 = x) → (∀ x : F, x * 1 = x)`, the field analogue of
    the `Num`/`ℕ` flagship demo, domain auto-resolved. -/
example : (∀ x : F, x * 1 = x) → (∀ x : F, x * 1 = x) := by
  param_transfer
  intro a a' (haa' : a = a') hPa
  exact haa' ▸ hPa

/-- The fusion fact. `param_solve`-style Stack-B resolution and the
    Stack-A `@[param]` witness produce the *same* equation `a * b = bbFieldMul a b`
    — proof of one operation living in both registries. -/
example (a b : F) :
    (transferRel (inferInstance : Related (id : F → F) (a * b) (bbFieldMul a b)))
      = bbMulParam a a rfl b b rfl := by
  rfl

/-! ## Next domains (documented)

Two further representations in the repo would slot in as additional
`@[param]`/`TransferDom` registrations, both diagonal-only under the current
`TransferDom` shape (the same non-diagonal limitation as above):

* `ZMod p ↔ canonical-`Nat` limbs. `bbEncode`/`bbToF` already give the
  `F ↔ BitVec` round-trip; a `TransferDom F BitVec`-style domain needs the
  decoder at `map2a` (have it: `bbToF_bbEncode`) and the caller-supplied
  limb predicate — blocked on the annotation-inference gap, not on a
  missing primitive.
* group `↔` bytes. Any `ReprEmbeddingClass A α` is already a
  `Param .map3 .map0` (`Param.paramOfEmbedding`); registering it as a
  `TransferDom` needs a backward section, which an embedding lacks by
  construction (it is `map0` backward) — so this stays a forward-only op
  witness, not a `∀`-domain, until a decoder is registered.

No new primitives are introduced here: only the already-proven Baby Bear field
realizations are registered.
-/

/-! ## Pinned fusion doc-test: the field ops live in the Param-engine registry

This `#guard_msgs`-checked probe materialises the ambient `@[param]` registry
(`getParamDB`, the database the term-level translator `translate`/`translateAll`
consumes) and confirms the abstract field operators `HMul.hMul`/`HAdd.hAdd`
resolve to the emitted Baby Bear kernels via the *same* witnesses that back
Stack B's `RelatedBinOp` squares — i.e. the two stacks share one registry. -/

open Lean Param in
/-- info: HMul.hMul ↦ bbFieldMul (via bbMulParam); HAdd.hAdd ↦ bbFieldAdd (via bbAddParam) -/
#guard_msgs in
run_meta do
  let db ← getParamDB
  match db.find? ``HMul.hMul, db.find? ``HAdd.hAdd with
  | some (c', l), some (c2', l2) =>
      logInfo m!"HMul.hMul ↦ {c'} (via {l}); HAdd.hAdd ↦ {c2'} (via {l2})"
  | _, _ => logInfo "field ops NOT in getParamDB"

end Transfer
