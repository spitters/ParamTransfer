/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Related
import Transfer.Base.TransferTactic
import Transfer.Base.FieldRegistry
import Lean.Elab.Tactic.Conv

/-!
# `conv`-mode transfer

The whole-goal `transfer` tactic (`TransferTactic.lean`) closes an *equation*
goal `a = b` by the `Related` registry. This module lifts the same relatedness
machinery into **`conv` mode**, so a representation change can happen *inside a
context* — on a focused sub-term — alongside `rw`/`simp`/`gcongr` in an ordinary
proof.

Inside `conv => …` (or `conv in (pattern) => …`) the focused sub-term `t` is
rewritten to its transferred form `t'`, leaving the surrounding goal otherwise
untouched. Concretely: given a goal `P (a * b + c)`, navigating to the argument
and running `transferConv` rewrites it to `P (bbFieldAdd (bbFieldMul a b) c)` — the
transfer happens under the context `P ·`.

## The two tactics

* **`transferConv`** — the `Related`-instance-driven version. On the focused
  term `t`:
  1. it *discovers* the transferred shape `t'` by the `@[transfer]` equational set
     (the realization simp lemmas of `FieldRegistry.lean`);
  2. it then *proves* `t = t'` through the `Related` typeclass registry —
     `synthInstance (Related id t t')` composes the registered `RelatedBinOp`
     commuting squares via `composeBinOp`, and `transferGround` extracts the
     equation. The installed rewrite proof is therefore the
     typeclass-synthesized commuting-square composite, not the simp proof;
  3. `Conv.updateLhs t' proof` installs it.

  The representation change is carried by the registered squares; no square is
  invented (the non-fabrication invariant). Step 1 only *finds the shape*; the
  *trust* lives in the `Related`/`RelatedBinOp` instances of step 2.

* **`transferSimpConv`** — the simp-set-driven complement: a thin `conv` wrapper
  for `simp only [transfer]`. This rewrites the focused term using the `@[transfer]`
  equational realization set directly (the simp proof). It is the `conv`-mode
  form of `repr_transfer`.

## Mechanism (the `conv` API)

A `conv` tactic is `syntax … : conv` + `elab_rules : conv`. Inside the elab:

* `Conv.getLhs : TacticM Expr` returns the focused sub-term `t`;
* `Conv.updateLhs (t' h : Expr) : TacticM Unit` installs the rewrite, where the
  proof obligation is `h : t = t'` (exactly the orientation `transferGround`
  produces).

`transferConv` builds the `Related id t t'` goal by elaborating it from source
syntax (splicing `t` and `t'` back via `Expr.toSyntax`) rather than by raw
`mkApp`: instance resolution keys `composeBinOp` on the *source-elaborated* `id`
encoding, and a hand-assembled application is defeq but not the shape resolution
matches on.

## Scope

`conv => simp only [transfer]` (here packaged as `transferSimpConv`) already gives the
simp-based sub-term transfer for the registered *equational* set. `transferConv` is
the `Related`-instance-driven version: the *proof* it installs is the typeclass
composite of the registered commuting squares, so the conv step is justified by
the `RelatedBinOp` witnesses rather than by simp rewriting. Both compose with
`rw`/`simp`/`gcongr` in a normal proof — they are ordinary `conv` steps. The
scope is the closed first-order, identity-encoding op-tree fragment that
`Related.lean` covers; binder traversal and richer encodings remain the
whole-goal `transfer`'s job.
-/

set_option autoImplicit false

namespace Transfer

open Lean Lean.Elab Lean.Elab.Tactic Lean.Elab.Tactic.Conv Lean.Meta
open Transfer.ExampleField

/-- **`conv`-mode transfer (instance-driven).** On the focused sub-term `t : α`,
    discover the transferred form `t'` via the `@[transfer]` realization set, then
    prove `t = t'` through the `Related` typeclass registry (`transferGround`
    over the composed `RelatedBinOp` squares) and rewrite the focus to `t'`. The
    installed proof is the typeclass composite, not the simp proof; no commuting
    square is invented. -/
syntax "transferConv" : conv

elab_rules : conv
  | `(conv| transferConv) => do
    let lhs ← getLhs
    let α ← inferType lhs
    -- 1. Discover the transferred form via the `@[transfer]` equational set.
    let some ext ← Lean.Meta.getSimpExtension? `transfer
      | throwError "transferConv: no `transfer` simp set in scope"
    let ctx ← Simp.mkContext (simpTheorems := #[← ext.getTheorems])
    let (res, _) ← simp lhs ctx
    let tgt := res.expr
    -- 2. Build `Related id lhs tgt` from source syntax so `composeBinOp` keys on
    --    the source-elaborated `id` encoding, then synthesize it.
    let lhsStx ← lhs.toSyntax
    let tgtStx ← tgt.toSyntax
    let relTy ← Term.elabTerm (← `(Related (id) $lhsStx $tgtStx)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let inst ← synthInstance relTy
    -- 3. Extract the equation `lhs = tgt` via `transferGround` and install it.
    let lvlPlus1 ← Meta.getLevel α
    let some u := lvlPlus1.dec
      | throwError "transferConv: focus type {α} is not in a `Type u` universe"
    let proof := mkApp4 (mkConst ``transferGround [u]) α lhs tgt inst
    updateLhs tgt proof

/-- **`conv`-mode transfer (simp-set-driven).** A thin `conv` wrapper for
    `simp only [transfer]` — the equational `@[transfer]` realization set applied to the
    focused sub-term, with the simp proof. This is the `conv`-mode form of
    `repr_transfer`; it composes with `rw`/`simp` like any other `conv` step. -/
syntax "transferSimpConv" : conv

macro_rules
  | `(conv| transferSimpConv) => `(conv| simp only [transfer])

/-! ## Demonstration — transfer a sub-term inside a larger goal

The registered Baby Bear field squares (`bbMulRelated`/`bbAddRelated` from
`Related.lean`, plus the `@[transfer]` `mul_repr`/`add_repr` of `FieldRegistry.lean`)
let the tactic transfer the op-tree `a * b + c` to its emitted form
`bbFieldAdd (bbFieldMul a b) c`. Here that happens on a *sub-term*, in the middle
of a larger goal, via `conv`. The caller names nothing — instance resolution
finds the squares. -/

/-- A goal `P (a * b + c)` whose argument is rewritten to the
    emitted op-tree by `conv in (pattern) => transferConv`, then discharged from the
    transferred hypothesis. The transfer happened *inside the context* `P ·`. -/
example (a b c : F) (P : F → Prop) (h : P (bbFieldAdd (bbFieldMul a b) c)) :
    P (a * b + c) := by
  conv in (a * b + c) => transferConv
  exact h

/-- The same, navigating with `conv_lhs` on an equation goal: `transferConv`
    rewrites the LHS focus, leaving the trivial `t' = t'`. -/
example (a b c : F) : (a * b + c) = bbFieldAdd (bbFieldMul a b) c := by
  conv_lhs => transferConv

/-- Transfer of the focus while the surrounding goal carries an *additional*
    argument `k`: `transferConv` is an ordinary `conv` step that touches only the
    focused sub-term, leaving the context `P k ·` intact. -/
example (a b c : F) (k : F) (P : F → F → Prop)
    (h : P k (bbFieldAdd (bbFieldMul a b) c)) :
    P k (a * b + c) := by
  conv in (a * b + c) => transferConv
  exact h

/-- The simp-set-driven complement on the same sub-term: `transferSimpConv` rewrites
    the focus via the `@[transfer]` equational set (the simp proof) rather than
    typeclass synthesis. -/
example (a b c : F) (P : F → Prop) (h : P (bbFieldAdd (bbFieldMul a b) c)) :
    P (a * b + c) := by
  conv in (a * b + c) => transferSimpConv
  exact h

end Transfer
