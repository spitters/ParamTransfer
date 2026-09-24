/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Examples.ParamCryptoExamples
public import Transfer.Examples.StrongExamples
public import Transfer.Examples.Trocq
public import Transfer.Examples.EffectfulTransfer
public import Transfer.Examples.RCompOkExamples
public import Transfer.Examples.HexMatrixCorrespondence
public import Transfer.Examples.HexEffectful
public import Transfer.Examples.HexDecide
public import Transfer.Examples.HexArrayCompute

/-!
# Example suites

The root of the `TransferExamples` library: worked examples and demonstrations of the
transfer tactics, kept out of `import Transfer`. The library code under
`Transfer/Examples/` that other developments use (`ParamCryptoDomains`,
`ParamRetraction`, `MachineLimbField`, `ZModDecide`, `ZModPolyDecide`, `ZModPowMod`
and their dependencies) stays imported by `Transfer`.

* `ParamCryptoExamples`: `cast_trans`, deriving and transfer over the Baby Bear domains.
* `StrongExamples`: transfer over non-diagonal domains, compared with the native tactics.
* `Trocq`: the Trocq example suite.
* `EffectfulTransfer`: an effectful triple transferred across `ℕ ↔ ℤ` with `mvcgen`.
* `RCompOkExamples`: `RCompOk` over a test monad with failure.
* `HexMatrixCorrespondence`, `HexEffectful`, `HexDecide`, `HexArrayCompute`: instances
  over the verified computational algebra of `hex`.
-/
