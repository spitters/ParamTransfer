/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.Basic

/-!
# A self-contained example field for the Trocq engine demos

The Trocq parametricity engine in this directory (`Related`/`RelatedBinOp`,
the `transfer`/`rcongr`/`param_*` tactics, the `@[transfer]`/`@[param]` databases)
is field-agnostic: it transfers any registered commuting square `enc (op x y)
= bop (enc x) (enc y)` regardless of what the carrier is.

The demos need one concrete field with two registered operations. This module
provides them — `F`, `bbFieldMul`, `bbFieldAdd`, `bbFieldMul_eq`,
`bbFieldAdd_eq` — built only from `Mathlib`. `F` is `ZMod p` for the Baby Bear prime `p = 2^31 - 2^27 + 1`,
and the two example operations are named op-tree heads distinct from the abstract
`*`/`+`, each *proved equal* to the abstract operation — exactly the shape the
transfer engine consumes.

The operations here are an illustrative instance of a registered
`RelatedBinOp`. A realization by compiled machine-word arithmetic, where
`bbFieldMul_eq` is an encode/compute/decode theorem, has the same shape, and the
engine treats it in the same way.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.ExampleField

/-- The Baby Bear prime `2^31 - 2^27 + 1`. -/
def exampleFieldPrime : ℕ := 2013265921

instance : NeZero exampleFieldPrime := ⟨by unfold exampleFieldPrime; decide⟩

-- The demos register only the commutative-ring operations `bbFieldMul`/`bbFieldAdd`
-- (`· * ·`/`· + ·` on `ZMod p`). `F` is used purely as a commutative ring, so no
-- `Fact (Nat.Prime exampleFieldPrime)` instance is provided — proving primality of a
-- 31-bit number needs `native_decide`, which would put `Lean.ofReduceBool` in the
-- axiom set of the default `import Transfer`.

/-- The example carrier `F = ZMod p` (a commutative ring; primality is not asserted,
    see the note above). Built from `Mathlib` alone. -/
abbrev F : Type := ZMod exampleFieldPrime

/-- An example binary operation registered as realizing abstract `*`. It is a
    distinct op-tree head from `HMul.hMul`, proved equal to `*` by
    `bbFieldMul_eq`. -/
def bbFieldMul (a b : F) : F := a * b

/-- An example binary operation registered as realizing abstract `+`. Distinct
    op-tree head from `HAdd.hAdd`, proved equal to `+` by `bbFieldAdd_eq`. -/
def bbFieldAdd (a b : F) : F := a + b

/-- `bbFieldMul` realizes the abstract field product. -/
theorem bbFieldMul_eq (a b : F) : bbFieldMul a b = a * b := rfl

/-- `bbFieldAdd` realizes the abstract field sum. -/
theorem bbFieldAdd_eq (a b : F) : bbFieldAdd a b = a + b := rfl

end Transfer.ExampleField
