/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib

/-!
# Trocq `summable` — summability transfers across an equivalence

Trocq's `summable` example transfers summability across a change of index type. The
paradigm case: a type equivalence `e : α ≃ β` transfers `Summable` in both
directions (`Equiv.summable_iff`), because reindexing a sum by a bijection preserves
it. This is the analytic counterpart of the engine's representation transfers — a
statement moved across an equivalence — for a `noncomputable`, topological predicate.
-/

set_option autoImplicit false

namespace Transfer.Examples.Trocq.Summable

/-- **Summability transfers across a reindexing bijection.** For any equivalence of
    index types, a family is summable after reindexing iff it was summable. -/
theorem summable_transfer {α β M : Type} [AddCommMonoid M] [TopologicalSpace M]
    (e : α ≃ β) (f : β → M) : Summable (f ∘ e) ↔ Summable f :=
  e.summable_iff

end Transfer.Examples.Trocq.Summable
