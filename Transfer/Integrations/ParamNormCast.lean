/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Translate.ParamTranslateFull
import Mathlib.Data.Int.Cast.Lemmas

/-!
# `norm_cast` move-lemmas are `Param` relatedness witnesses

Mathlib's `norm_cast` machinery rewrites across a coercion `↑ : A → A'` using
*move lemmas* of the shape

```
↑(a ⋄ b) = ↑a ⋄ ↑b        -- e.g. `Nat.cast_add`, `Nat.cast_mul`
```

This module shows that such a move lemma is exactly a Trocq `Param` binary
relatedness witness for the *cast graph* relation `R a a' := (↑a = a')`. Read
the coercion as a registered change-of-representation `A ~ A'`; then a move
lemma `↑(op a b) = op' ↑a ↑b` is precisely

```
RArrow R (RArrow R R) op op'
```

— the statement that `op` and its `A'`-side counterpart `op'` send
`R`-related arguments to `R`-related results. So the term-level translator
(`translateAll`, `ParamTranslateFull`) can transport a whole `A`-term to its
`A'`-counterpart across the coercion, *using the `norm_cast` lemmas as the
operator witnesses*. Trocq generalizes `norm_cast` from coercions to arbitrary
registered representations: `norm_cast` is the special case where `R` is a
coercion graph and the witnesses are move lemmas.

## The cast graph and its operator witnesses

The relation is `NatIntR n i := (↑n = i)` (the graph of `ℕ → ℤ`, already
defined in `ParamTranslateTy`). Two `norm_cast` lemmas are repackaged as
`Param` binary witnesses:

* `addCastWit` from `Nat.cast_add` (`↑(a + b) = ↑a + ↑b`);
* `mulCastWit` from `Nat.cast_mul` (`↑(a * b) = ↑a * ↑b`).

Each proof intros the relatedness hypotheses `↑a = a'`, `↑b = b'`, substitutes,
and discharges the remaining `↑(a ⋄ b) = ↑a ⋄ ↑b` with the move lemma.

## The correspondence

`paramWitOfCastHom` is the generic statement: any homomorphism property
`∀ a a', R a a' → ∀ b b', R b b' → R (op a b) (op' a' b')` *is* the curried
`RArrow R (RArrow R R) op op'` witness — the two are definitionally the same
proposition (one is the `RArrow`-unfolding of the other). The converse holds
too: a `Param` witness for an injective encoding `R` (such as a coercion graph)
yields a cast-style rewrite `↑(op a b) = op' ↑a ↑b` by reading `R` back as
`↑a = a'`. This two-way correspondence is why Trocq subsumes `norm_cast`: the
move-lemma database and the `@[param]` operator database are the same data,
and the translator's operator/arity rule is the structural recursion that
`norm_cast` performs on the syntax of a casted term.

## Scope

The binary case is treated over the concrete coercion `ℕ → ℤ`, with `+` and `*`.
The `n`-ary generalisation is the same spine-stripping the operator rule
already supports (`ParamTranslateOp`); the same construction applies to any
registered coercion graph with `@[norm_cast]` move lemmas for its operators.
-/

set_option autoImplicit false

open Lean Meta Elab

namespace Transfer.Param

/-! ## `norm_cast` move lemmas as `Param` binary witnesses

`NatIntR n i := (↑n = i)` is the graph of the coercion `ℕ → ℤ` (defined in
`ParamTranslateTy`). The two witnesses below are the `norm_cast` lemmas
`Nat.cast_add` / `Nat.cast_mul` repackaged through the function relation
`RArrow`: `op` and its `ℤ`-side counterpart `op'` send `NatIntR`-related
arguments to `NatIntR`-related results. -/

/-- `Nat.cast_add` as a `Param` binary witness: `(· + ·)` on `ℕ` and `(· + ·)`
    on `ℤ` are related at `RArrow NatIntR (RArrow NatIntR NatIntR)`. This is the
    `norm_cast` move lemma `↑(a + b) = ↑a + ↑b` read as relatedness across the
    coercion graph. -/
theorem addCastWit :
    RArrow NatIntR (RArrow NatIntR NatIntR)
      (· + · : Nat → Nat → Nat) (· + · : Int → Int → Int) := by
  intro a a' ha b b' hb
  simp only [NatIntR] at *
  subst ha; subst hb
  exact Nat.cast_add a b

/-- `Nat.cast_mul` as a `Param` binary witness: `(· * ·)` on `ℕ` and `(· * ·)`
    on `ℤ` are related at `RArrow NatIntR (RArrow NatIntR NatIntR)`. The
    `norm_cast` move lemma `↑(a * b) = ↑a * ↑b` read as relatedness. -/
theorem mulCastWit :
    RArrow NatIntR (RArrow NatIntR NatIntR)
      (· * · : Nat → Nat → Nat) (· * · : Int → Int → Int) := by
  intro a a' ha b b' hb
  simp only [NatIntR] at *
  subst ha; subst hb
  exact Nat.cast_mul a b

/-- **The correspondence, generically.** A cast-homomorphism property
    `∀ a a', R a a' → ∀ b b', R b b' → R (op a b) (op' a' b')` — the shape of a
    `@[norm_cast]` move lemma `↑(op a b) = op' ↑a ↑b` once `R a a'` is read as
    `↑a = a'` — *is* the curried `Param` binary witness
    `RArrow R (RArrow R R) op op'`. The two are the same proposition up to
    unfolding `RArrow`; this lemma exhibits the conversion. Specialising
    `R := NatIntR`, `op := (·+·)`, `op' := (·+·)` recovers `addCastWit`. -/
theorem paramWitOfCastHom {A A' : Type} (R : A → A' → Prop)
    (op : A → A → A) (op' : A' → A' → A')
    (h : ∀ a a', R a a' → ∀ b b', R b b' → R (op a b) (op' a' b')) :
    RArrow R (RArrow R R) op op' :=
  fun a a' ha b b' hb => h a a' ha b b' hb

/-- Round-trip sanity check: `addCastWit` arises from `paramWitOfCastHom`
    applied to the coercion-graph homomorphism property of `+`, which is
    `Nat.cast_add` after unfolding `NatIntR`. Demonstrates that the move lemma
    and the `Param` witness are interchangeable. -/
theorem addCastWit' :
    RArrow NatIntR (RArrow NatIntR NatIntR)
      (· + · : Nat → Nat → Nat) (· + · : Int → Int → Int) :=
  paramWitOfCastHom NatIntR _ _ <| by
    intro a a' ha b b' hb
    simp only [NatIntR] at *
    subst ha; subst hb
    exact Nat.cast_add a b

/-! ## Databases registering the cast graph and its witnesses with the translator

`castTyDB` registers `ℕ ↦ (ℤ, NatIntR)` (the type-level coercion). `castOpDB`
registers the operators `+`, `*` (head consts `HAdd.hAdd`, `HMul.hMul`, each
with `numLeadingArgs = 4`: three type args plus one instance) to their `ℤ`-side
op and the `norm_cast`-derived witness. -/

/-- Type database: `ℕ` transfers to `ℤ` at the coercion graph `NatIntR`. -/
def castTyDB : NameMap (Expr × Expr) :=
  (∅ : NameMap (Expr × Expr)).insert ``Nat (.const ``Int [], .const ``NatIntR [])

/-- Operator database: `+` and `*` mapped to their `ℤ` counterparts with the
    `norm_cast`-derived `Param` witnesses `addCastWit` / `mulCastWit`. -/
def castOpDB : OpDB :=
  ((∅ : OpDB)
    |>.insert ``HAdd.hAdd (4, .const ``Int.add [], .const ``addCastWit []))
    |>.insert ``HMul.hMul (4, .const ``Int.mul [], .const ``mulCastWit [])

/-! ## Demonstration — transferring a term across the coercion

`translateAll castOpDB castTyDB {} {}` on `fun n : ℕ => n + n * n` produces the
`ℤ`-term `fun n' => n'.add (n'.mul n')` together with a relatedness proof of
type

```
∀ (n : ℕ) (n' : ℤ), NatIntR n n' → NatIntR (n + n * n) (n'.add (n'.mul n'))
```

i.e., unfolding `NatIntR`, `∀ n n', ↑n = n' → ↑(n + n * n) = n' + n' * n'`. The
binder changes representation `ℕ ↦ ℤ`, and the operator witnesses are
the `norm_cast` move lemmas. `inferType` kernel-checks the synthesized proof, so
this validates the construction. -/
run_meta do
  let t ← Term.TermElabM.run' (Term.elabTerm (← `(fun n : Nat => n + n * n)) none)
  let t ← instantiateMVars t
  let (t', pf) ← translateAll castOpDB castTyDB {} {} t
  logInfo m!"⟦fun n : ℕ => n + n * n⟧ across (ℕ ↦ ℤ):"
  logInfo m!"  transferred term  = {t'}"
  logInfo m!"  transferred term  : {← inferType t'}"
  logInfo m!"  relatedness proof : {← inferType pf}"

end Transfer.Param
