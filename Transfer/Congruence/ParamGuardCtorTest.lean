/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedFunTest

/-!
# Tests of the constructor split of `param_guard`

Equation goals whose left-hand side is a constructor application, over the record
encoding of `Transfer.Base.RelatedFunTest`. `param_guard` splits such an equation
into the equations of the fields: by constructor congruence when the right-hand
side is an application of the same constructor, by structure eta when it is not a
constructor application. Each field equation `enc t = t'` is then reshaped into
`Related enc t t'` and descended.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.ParamGuardCtorTest

open Transfer Transfer.RelatedFunTest

/-- A pair against a pair. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    (enc8 r.x, enc8 r.y) = (w.x, w.y) := by
  param_guard

/-- A pair against a right-hand side that is not a constructor application. -/
example (q : ℕ × ℕ) (p : BitVec 8 × BitVec 8) [Related (Prod.map enc8 enc8) q p] :
    (enc8 q.1, enc8 q.2) = p := by
  param_guard

/-- `Except.ok` against `Except.ok`. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    (Except.ok (enc8 r.x) : Except String (BitVec 8)) = Except.ok w.x := by
  param_guard

/-- A nested pair against a nested pair. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    ((enc8 r.x, enc8 r.y), enc8 r.x) = ((w.x, w.y), w.x) := by
  param_guard

/-- A nested pair whose inner right-hand side is not a constructor application. -/
example (r : Rec) (w : RecW) (q : ℕ × ℕ) (p : BitVec 8 × BitVec 8) [Related encRec r w]
    [Related (Prod.map enc8 enc8) q p] :
    ((enc8 q.1, enc8 q.2), enc8 r.y) = (p, w.y) := by
  param_guard

end Transfer.ParamGuardCtorTest
