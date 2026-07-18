/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Tactic.GCongr

/-!
# Probe: whether `@[gcongr]` accepts cross-head realization lemmas

This file records a design finding for the Trocq proof-transfer combinators:
whether a binary realization/relatedness combinator — whose conclusion relates two
*different* head symbols, `R (op a b) (bop a' b')` — can be registered as a
`@[gcongr]` lemma.

## Result

`@[gcongr]` accepts only same-head monotonicity lemmas: the conclusion must
have the shape `f x₁ … xₙ ∼ f x₁' … xₙ'`, i.e. the same head function `f` and
the same arity on both sides of the relation, with the varying arguments related
pairwise by the side goals.

The constraint is enforced in `Mathlib.Tactic.GCongr.Core` (`makeGCongrLemma`):

```
let some (head,  lhsArgs) := getCongrAppFnArgs lhs | fail "LHS is not suitable …"
let some (head', rhsArgs) := getCongrAppFnArgs rhs | fail "RHS is not suitable …"
unless head == head' && lhsArgs.size == rhsArgs.size do
  fail "LHS and RHS do not have the same head function and arity"
```

A cross-head lemma is therefore rejected at attribute-application time, with:

```
@[gcongr] attribute only applies to lemmas proving f x₁ ... xₙ ∼ f x₁' ... xₙ'.
 LHS and RHS do not have the same head function and arity in R (op a b) (bop a' b')
```

## Implication for Trocq

The Trocq combinators relate distinct heads (a source operation and its target
realization), so they cannot be `@[gcongr]` lemmas. `gcongr` is the right *mental
model* — peel a relation by descending into matching argument positions — but it
is not the available hook. A cross-head transfer needs a dedicated congruence
driver (a custom `Simp`/`Tactic` extension or an explicit relation-respecting
combinator set), not the `@[gcongr]` attribute.
-/

set_option autoImplicit false

/-! ## Same-head control (accepted, fires) -/

/-- Same-head monotonicity lemma for `+` on `Nat`. Registering this with
`@[gcongr]` succeeds and `gcongr` applies it (see `add_mono_probe_fires`). -/
@[gcongr]
theorem add_mono_probe {a₁ b₁ a₂ b₂ : Nat} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    a₁ + a₂ ≤ b₁ + b₂ :=
  Nat.add_le_add h₁ h₂

/-- `gcongr` discharges a same-head `+` goal using the control lemma. -/
example {a₁ b₁ a₂ b₂ : Nat} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) :
    a₁ + a₂ ≤ b₁ + b₂ := by
  gcongr

/-! ## Cross-head record (rejected — kept untagged)

The lemma below is the shape a Trocq binary realization combinator would have:
its conclusion relates two different head symbols (`op` versus `bop`) under a
custom relation `R`. It is deliberately left without `@[gcongr]`, because
tagging it raises the attribute-application error quoted in the module docstring.
The lemma itself is a perfectly valid proposition; only the `@[gcongr]`
registration is rejected. -/

/-- An abstract binary relation, standing in for a Trocq realization relation. -/
def CrossR (_a _b : Nat) : Prop := True

/-- A source operation. -/
def srcOp (_a _b : Nat) : Nat := 0

/-- A target operation with a *different* head symbol. -/
def tgtOp (_a _b : Nat) : Nat := 0

/-- Cross-head realization lemma (the Trocq combinator shape). Provable, but
must not carry `@[gcongr]`: the attribute rejects it because the LHS head
`srcOp` and RHS head `tgtOp` differ. -/
theorem cross_head_realization {a a' b b' : Nat}
    (_h₁ : CrossR a a') (_h₂ : CrossR b b') :
    CrossR (srcOp a b) (tgtOp a' b') :=
  trivial
