/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Aesop

/-!
# The `Trocq` aesop rule set — declaration module

A rule set declared with `declare_aesop_rule_sets` is not visible in the file
that declares it (aesop's frontend only exposes it to *importing* files — the
reason Mathlib keeps each set in a tiny `Init.lean`). This module only
declares the set, so that `Trocq/AesopIntegration.lean` (which imports it) can
register rules into it *and* invoke `aesop (rule_sets := [Transfer])`, and so the
named set is usable engine-wide by any downstream file.
-/

declare_aesop_rule_sets [Transfer]
