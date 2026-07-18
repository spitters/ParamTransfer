/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.FieldRegistry

/-!
# `grind` as a transfer leaf discharger

The foundation realization lemmas of `FieldRegistry.lean` are equational
(`Eq`-shaped) commuting squares between an abstract field operation and its
emitted Baby Bear kernel:

* `mul_repr : a * b = bbFieldMul a b`
* `add_repr : a + b = bbFieldAdd a b`

They are already tagged `@[transfer]` (the `simp`-set used by `transfer`'s leaf
cascade). This file dual-tags them for `grind` via `attribute [grind =]`,
turning them into automatic rewrite candidates in the `grind` database, and
demonstrates that `grind` then discharges transfer *leaf* equations — the
closed first-order composites that `transfer`'s leaf cascade produces — by
composing the registered squares through `grind`'s congruence closure.

## Scope

This validates two design points from the Trocq tactic-interactions design:

1. **`grind` as a final leaf-discharger in `transfer`'s cascade.** Once the
   foundation realization lemmas are in the `grind` database, a single `grind`
   closes a leaf equation `a * b + c = bbFieldAdd (bbFieldMul a b) c` and
   nested composites of it — `grind`'s congruence closure composes the
   per-operation squares automatically, no positional `rw` chain required.
2. **`@[transfer, grind =]` dual-tagging of foundation lemmas.** `attribute
   [grind =] mul_repr add_repr` is accepted on the imported `@[transfer]`
   lemmas; the same equation serves both the `simp`-based discovery path and
   the `grind`-based leaf-closing path.

**Carrier caveat.** `grind` times out on
ENNReal/BitVec arithmetic chaining. The Baby Bear field carrier `F` here is
fine: the realization lemmas are pure first-order equations and the composites
close instantly — `grind` never needs to chase the underlying `BitVec 64`
kernel arithmetic, because the `bbField*` operations are opaque on the right of
each square. The dual-tag pattern is therefore safe for any carrier whose
realization lemmas keep the emitted kernel opaque.
-/

namespace Transfer.GrindIntegration

open Transfer
open Transfer.ExampleField

-- Dual-tag the foundation realization lemmas for `grind`. These imported
-- lemmas are already `@[transfer]`; `attribute [grind =]` adds them as automatic
-- rewrite candidates in the `grind` database (the `@[transfer, grind =]`
-- dual-tagging design point).
attribute [grind =] mul_repr add_repr

/-- A transfer **leaf**: `grind` rewrites the abstract composite into its emitted
    form by composing `mul_repr` and `add_repr` from the database. This is what
    `transfer`'s leaf cascade would close — discharged here in one `grind`. -/
theorem grind_leaf (a b c : F) :
    a * b + c = bbFieldAdd (bbFieldMul a b) c := by
  grind

/-- A slightly larger composite: `grind`'s congruence closure composes the two
    squares through an outer multiply. -/
theorem grind_composite (a b c d : F) :
    (a * b + c) * d = bbFieldMul (bbFieldAdd (bbFieldMul a b) c) d := by
  grind

/-- A nested composite (two products under a sum, multiplied by a sum):
    demonstrates `grind` scaling the square-composition without any positional
    rewrite control. -/
theorem grind_nested (a b c d e f : F) :
    (a * b + c * d) * (e + f)
      = bbFieldMul (bbFieldAdd (bbFieldMul a b) (bbFieldMul c d)) (bbFieldAdd e f) := by
  grind

end Transfer.GrindIntegration
