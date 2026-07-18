/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer

/-!
# Axiom ledger — a build-time hygiene tripwire

`#guard_msgs`-pinned `#print axioms` for a curated set of load-bearing public
results. Building this module fails if any of them gains an unexpected axiom —
in particular `sorryAx` (a `sorry`) or a `native_decide` axiom (`Lean.ofReduceBool`).
CI builds this module (`lake build Transfer.Audit`), so such drift breaks the build.

The pinned set spans the three claims the library rests on: the univalence
boundary, a genuine cross-representation encoding law, and heterogeneous
congruence over distinct fiber types. The expected axiom set is Lean's standard
`propext` / `Quot.sound` / `Classical.choice` and nothing else.
-/

/-- info: 'Transfer.UnivalenceStatus.univalence_inconsistent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Transfer.UnivalenceStatus.univalence_inconsistent

/-- info: 'Transfer.Param.limbVal_toLimbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Transfer.Param.limbVal_toLimbs

/-- info: 'Transfer.Param.limbVal_hcongr_field' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Transfer.Param.limbVal_hcongr_field
