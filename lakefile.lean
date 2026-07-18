import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"

-- CompPoly provides a computable (array-backed `Raw`) univariate polynomial with a
-- `RingEquiv` to Mathlib's noncomputable `Polynomial`. The `Examples/CoqEAL/` suite
-- uses it to *compute* with `Polynomial` through the refinement — the CoqEAL /
-- Kaliszyk–O'Connor "refinements for free" pattern. Same toolchain (v4.30.0).
require CompPoly from git
  "https://github.com/Verified-zkEVM/CompPoly.git" @ "v4.30.0"

-- Documentation lives in separate packages: the verso manual in `docs/`, the
-- doc-gen4 API reference in `docbuild/`. This lakefile needs only mathlib + CompPoly.

package paramTransfer where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib Transfer where

lean_lib ReprTransfer where
lean_lib ReprTransferExpr where

-- The CoqEAL/Trocq example suite. A separate library so its CompPoly dependency
-- stays out of the core `Transfer` graph — a consumer of the engine does not build
-- CompPoly. Build with `lake build TransferCoqEAL`.
lean_lib TransferCoqEAL where
  roots := #[`Transfer.Examples.CoqEAL]
