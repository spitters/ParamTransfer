/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import ReprTransfer

/-!
# The `repr` registry + `repr_transfer` tactic

A relation-generic transfer driver over the `ReprTransfer` layer: a registry of
realization lemmas (the `repr` simp set) and a tactic that composes them. Tag a
realization lemma `enc-side = byte-side` (abstract op → emitted kernel) with
`@[repr]`; then `repr_transfer` rewrites any composite of registered ops to its
emitted-kernel form automatically — deriving what the per-protocol bridges
(`groth16_full_verifier_transfer`, `pedersen_commitment_transfer`, the field-
layer connections, …) otherwise derive by hand.

`register_simp_attr` must live in its own module (the attribute is only usable in
*importing* files), so the tagged lemmas live in `Trocq/FieldRegistry.lean` etc.
-/

/-- The Trocq realization registry: a simp set of `abstract-op = emitted-kernel`
    lemmas. Tag each realization (e.g. `a * b = bbFieldMul a b`) with `@[transfer]`.
    (Named `transfer`, not `repr`, to avoid clashing with the `Repr.repr` function.) -/
register_simp_attr transfer

/-- Transfer tactic. Rewrites the goal's abstract operations into their
    registered emitted kernels (the compile-to-emitted-leaf direction),
    composing the registered realizations structurally. -/
macro "repr_transfer" : tactic => `(tactic| simp only [transfer])

/-- Variant that also closes the resulting goal by reflexivity / hypotheses. -/
macro "repr_transfer!" : tactic => `(tactic| simp only [transfer] <;> rfl)
