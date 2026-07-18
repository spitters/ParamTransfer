/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Examples.PeanoBinNat
import Transfer.Examples.ExampleField
import Transfer.Examples.ParamRetraction
import Transfer.Examples.Trocq.Summable

/-!
# The Trocq example suite

The engine ports Trocq (`rocq-community/trocq`), and this file indexes the worked
examples that mirror Trocq's own example set. Unlike the `CoqEAL` suite, these need
only Mathlib, so they live in the core `Transfer` library.

Members (Trocq upstream example → module):

* `peano_bin_nat` → `Examples/PeanoBinNat` — binary/unary naturals (`Num ≃ ℕ`), the
  flagship equivalence transfer.
* the paper example → `Examples/ExampleField` — one relation, three uses (build,
  transfer, decide) over a registered field realization.
* retraction → `Examples/ParamRetraction` — the non-diagonal `ℤ ↠ ZMod p` domain,
  reaching `map2a` (a retraction, not an equivalence).
* `summable` → `Examples/Trocq/Summable` — summability transferred across an
  equivalence.

Three further Trocq examples are exercised inside the engine rather than as separate
files: `nat_ind` by `Base/TransferInduction` (`natEquivInduction`), `list_option` by
`Combinators/ParamData` (`R_list`/`R_option`), and `setoid_rewrite` by `param_cc`
(the relational congruence closure, shown in `Examples/ExampleField`).
-/
