/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Base.Core
import Transfer.Examples.ExampleField

/-!
# The emitted Baby Bear field kernels

Registers the proven field realizations (`bbFieldMul_eq` / `bbFieldAdd_eq`, the
emitted Baby Bear kernels) into the `repr` set, in the transfer direction
(abstract `*`/`+` → emitted `bbFieldMul`/`bbFieldAdd`). After this import,
`repr_transfer` auto-derives the emitted-kernel form of any Baby Bear field
expression — the registry-driven replacement for hand-written field-layer
connections (sum-check / Spartan / Lasso / STARK / Jolt / Fiat-Shamir all share
this field).
-/

namespace Transfer

open Transfer.ExampleField

/-- Registry entry: Baby Bear field multiply is the emitted `bbFieldMul` kernel. -/
@[transfer] theorem mul_repr (a b : F) : a * b = bbFieldMul a b := (bbFieldMul_eq a b).symm

/-- Registry entry: Baby Bear field add is the emitted `bbFieldAdd` kernel. -/
@[transfer] theorem add_repr (a b : F) : a + b = bbFieldAdd a b := (bbFieldAdd_eq a b).symm

end Transfer
