/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Init

/-!
# The leaf hook of the guarded descent

The tactic syntax `transfer_guard_leaf`, the extension point through which the
guarded descents `param_guard`, `param_solve` and `rcongr` close a `Related` goal
by a registered leaf rule. The rules are added by `macro_rules` in the modules
that state them: reading a related container (`Transfer.Base.RelatedFamily`) and
the carrier-changing squares and conditionals (`Transfer.Base.RelatedFun`).
-/

@[expose] public section

namespace Transfer

/-- The leaf rules of the guarded descent. Each alternative closes a goal
    `Related enc t t'` up to its operand goals and one guard goal, the last goal
    it leaves. Extensible: a `macro_rules` for `transfer_guard_leaf` adds an
    alternative tried before the earlier ones. -/
syntax "transfer_guard_leaf" : tactic

end Transfer
