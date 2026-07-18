/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.TransferTactic
import Transfer.Integrations.AesopRuleSet
import Aesop

/-!
# The `Trocq` aesop rule set

This module declares a dedicated `Trocq` aesop rule set bundling the
transfer machinery (`Related`/`composeBinOp` leaf dispatch via `transferGround`,
and the binder-traversing `transfer` tactic) as aesop rules. The set is
opt-in: it is never part of aesop's default rule set, so a plain `aesop`
call carries none of these rules.

## What the set contains

* `transferGround` registered as a safe apply rule. It is the ground leaf
  closer: it discharges `a = b` whenever instance resolution synthesizes a
  `Related id a b` from the registered `RelatedBinOp` commuting squares. As a
  safe rule it applies whenever possible and never needs to be retracted.
* `transfer` (exposed through the `transferTac` wrapper) registered as an
  unsafe 50% tactic rule. It performs the automatic binder traversal
  (`∀`/`λ`/`Iff`-of-`∀`) and re-dispatches each leaf to the registry, so the
  `Trocq` set closes the quantified and function-equality transfer shapes in
  addition to the ground composite.

## The aesop cross-file rule (an API constraint)

A rule set declared by `declare_aesop_rule_sets` is not visible in the file
that declares it — it becomes visible only in files that *import* the
declaring file (aesop's frontend enforces this; the same reason Mathlib
keeps every rule set in a tiny `Init.lean`/`Attr.lean` that the main module
imports). Consequently:

* The registration of the `Trocq` rules and any `aesop (rule_sets := [Transfer])`
  invocation must live in a client file that imports this one — see the
  importer recipe below.
* The in-file demonstrations therefore use the equivalent `aesop (add …)`
  forms, which add the *same* rules ad hoc without going through the named set.
  They demonstrate that aesop closes the transfer-shaped goals with this
  machinery; the named-set form is the importer-facing packaging of these
  rules.

### Importer recipe (for a file that imports this module)

```
import Transfer.Integrations.AesopIntegration

attribute [aesop safe apply (rule_sets := [Transfer])]
  Transfer.transferGround

@[aesop unsafe 50% tactic (rule_sets := [Transfer])]
def myTransferTac : Lean.Elab.Tactic.TacticM Unit := ...   -- or wrap `transfer`

example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by
  aesop (rule_sets := [Transfer])
```

## Why the set is off by default (the non-fabrication invariant)

aesop *fails open*: it runs an open-ended best-first search and only reports
failure when the whole search is exhausted. Adding the transfer rules to the
default set would let any `aesop` call search the registry for a
commuting square, which could mask a missing square — the
failure mode the Trocq layer surfaces (see `Related.lean`'s
"Scope and limits": the transfer is only as sound as the *registered* witnesses,
and a missing witness must remain a visible residual goal). Keeping the set
opt-in (`rule_sets := [Transfer]`) preserves fail-closed behavior everywhere else:
elsewhere `aesop` neither sees nor silently consumes the transfer rules, so an
absent square stays an honest open goal rather than being masked by search.
-/

set_option autoImplicit false

namespace Transfer.AesopIntegration

open Transfer
open Transfer.ExampleField

/-! ## Registering the rules into the `Trocq` set

The set is declared in `AesopRuleSet` (imported), so it is visible here and the
registrations + the named-set form both work. `transferGround` (the ground leaf
closer) is a safe apply rule; `transferCore` — the `transfer` elab's
`TacticM` driver, a global constant — is registered directly as an
unsafe tactic rule (no `by`-block wrapper needed, since the `elab` exposed a
constant). -/

attribute [aesop safe apply (rule_sets := [Transfer])] transferGround
attribute [aesop unsafe 50% tactic (rule_sets := [Transfer])] transferCore

/-! ## Demonstrations via the named set `aesop (rule_sets := [Transfer])`

These run the *named* `Trocq` set directly (usable here because this file imports
the declaring `AesopRuleSet` module), and engine-wide in any further importer. -/

/-- Ground composite — `transferGround` (safe) closes it via the registry. -/
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by
  aesop (rule_sets := [Transfer])

/-- Under a binder — the unsafe `transferCore` tactic rule strips the `∀` and
    dispatches the leaf. -/
example (b c : F) : ∀ a : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by
  aesop (rule_sets := [Transfer])

/-- Two binders. -/
example (c : F) : ∀ a b : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by
  aesop (rule_sets := [Transfer])

end Transfer.AesopIntegration
