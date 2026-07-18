/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Mathlib.Logic.Equiv.Basic

/-!
# Univalence in Lean 4 and the Trocq `map4` cap

The Univalence Axiom is inconsistent in Lean 4 (`univalence_inconsistent`). The
`map4` / universe-relation cap in this Trocq port — `ParamForall`'s `Map2a_forall`
requiring `Param04`, and `LevelRefusal` refusing `equiv` — is therefore a boundary of
Lean's type theory, not a configurable limit.

## The axiom landscape

Lean 4's kernel and standard axioms:
* `propext` — propositional extensionality `(a ↔ b) → a = b`, i.e. univalence
  restricted to `Prop`. It is consistent because `Prop` is proof-irrelevant:
  propositions are subsingletons, so equivalence of propositions is itself a
  subsingleton.
* `Quot.sound` — quotient soundness; it gives `funext` as a theorem and effective
  quotients. Consistent.
* `Classical.choice` — global choice; with `propext` it yields excluded middle
  (Diaconescu). Consistent. These three form the entire standard axiom set.
* Definitional proof irrelevance for `Prop`, built into the kernel: any two proofs of
  a `p : Prop` are definitionally equal. Since `Eq : α → α → Prop`, all equality is
  proof-irrelevant, so Lean validates UIP / Axiom K — a set-level (0-truncated) type
  theory rather than Homotopy Type Theory.

Univalence contradicts this. It states `(A = B) ≃ (A ≃ B)` for `A B : Type`. Here
`A = B : Prop` is a subsingleton, whereas `A ≃ B` need not be: `Bool ≃ Bool` contains
the distinct elements `id` and `not`. Univalence forces `Bool ≃ Bool` to be a
subsingleton, identifying `id` with `not`; evaluation at `true` then gives
`true = false`.

The `Prop`-level form of univalence is consistent and coincides with `propext`. The
inconsistency is specific to the `Type`-level statement: the proof irrelevance that
makes `propext` safe makes `Type`-level univalence contradictory.

## Consequences for the Param engine

* The univalence-free fragment `map0`–`map3` is the entire consistent space in Lean;
  the `map4` universe relation has no sound inhabitant.
* The port is `Prop`-valued. It relates values by `Prop` relations, whose univalence
  analogue is `propext`, and never relates types by equivalence-as-equality, so the
  inconsistency does not arise in proof transfer.
* No additional axiom completes `Map2a_forall` or the `Type`-valued motive. The cap is
  forced, and `LevelRefusal` refusing `equiv` follows from it.
-/

set_option autoImplicit false

namespace Transfer.UnivalenceStatus

/-- The negation equivalence on `Bool` (`not` is involutive). A second, distinct
    element of `Bool ≃ Bool` besides the identity. -/
def notEquiv : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- `not` is not the identity equivalence: they disagree at `true`. -/
theorem notEquiv_ne_refl : notEquiv ≠ Equiv.refl Bool := by
  intro h
  have : (notEquiv : Bool → Bool) true = (Equiv.refl Bool : Bool → Bool) true :=
    congrArg (fun e : Bool ≃ Bool => e true) h
  simp [notEquiv] at this

/-- The Univalence Axiom (`Type`-level): the canonical comparison map
    `(A = B) → (A ≃ B)` is an equivalence; equivalently, `A = B` and `A ≃ B` are
    equivalent types. Stated here as the existence of the equivalence. -/
def Univalence : Prop := ∀ (A B : Type), Nonempty ((A = B) ≃ (A ≃ B))

/-- Univalence is inconsistent in Lean 4. `A = B` is a subsingleton (`Eq` targets
    the definitionally proof-irrelevant `Prop`), so `id` and `not` in `Bool ≃ Bool`,
    having equal images under the injective `e.symm`, are equal — contradicting
    `notEquiv_ne_refl`. The `map4` universe cap follows. -/
theorem univalence_inconsistent (ua : Univalence) : False := by
  obtain ⟨e⟩ := ua Bool Bool
  -- `e.symm : (Bool ≃ Bool) → (Bool = Bool)` is injective (half of an equivalence).
  -- Its two inputs map into the subsingleton `Bool = Bool`, hence to equal proofs.
  have hsub : e.symm (Equiv.refl Bool) = e.symm notEquiv := Subsingleton.elim _ _
  have : Equiv.refl Bool = notEquiv := e.symm.injective hsub
  exact notEquiv_ne_refl this.symm

/-- The `Prop`-level analogue of univalence is `propext`: equivalent propositions
    are equal. It is consistent, and is the fragment the `Prop`-valued Param port
    operates in. -/
theorem prop_univalence {p q : Prop} (h : p ↔ q) : p = q := propext h

end Transfer.UnivalenceStatus
