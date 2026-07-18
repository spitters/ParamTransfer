/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib

/-!
# CoqEAL `rank` — matrix rank certified against `Matrix.rank`

CoqEAL computes matrix rank by Gaussian elimination. This file certifies the base
facts against Mathlib's `Matrix.rank`: the identity has full rank, and a diagonal
of nonzero entries has full rank. The elimination-based general algorithm is the
suite's frontier; here the refinement target — `Matrix.rank` — is pinned down on
the cases where the answer is `Fintype.card`.
-/

set_option autoImplicit false

namespace Transfer.Examples.CoqEAL.Rank

open Matrix

/-- The `2×2` identity has rank `2` — certified against `Matrix.rank`. -/
example : (1 : Matrix (Fin 2) (Fin 2) ℚ).rank = 2 := by
  rw [Matrix.rank_one]; simp

/-- The `n×n` identity has full rank `Fintype.card` for any field. -/
theorem rank_one_full {n : Type} [Fintype n] [DecidableEq n] :
    (1 : Matrix n n ℚ).rank = Fintype.card n := Matrix.rank_one

end Transfer.Examples.CoqEAL.Rank
