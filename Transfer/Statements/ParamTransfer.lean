/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Combinators.ParamForall
import Transfer.Examples.PeanoBinNat

/-!
# `∀`-transfer through the `Param` engine (`Map1_forall`)

This module turns the dependent-Π combinator `Map1_forall` (from
`ParamForall.lean`) into a proof-transfer principle for
universally-quantified statements.

## The construction

`Map1_forall PA PB` produces a `Map1Has (R_forall PA PB)`, whose `.map` field is
a *function*

  `(∀ a, B a) → (∀ a', B' a')`.

The `Param` hierarchy is `Type u`-valued (`Map1Has {A B : Type u}`), so a
`Prop`-valued motive `P : A → Prop` does not fit `B` directly (`Prop : Sort 0`,
not `Type u`). Bridge it with `ULift (PLift _)`: take the codomain family
`B a := ULift.{u} (PLift (P a)) : Type u`. `PLift` reflects a `Prop` into
`Type 0`, `ULift` raises it to `Type u`. The reflection
`(∀ a, P a) ≃ (∀ a, ULift (PLift (P a)))` is definitional-up-to-`⟨·⟩`/`.down`,
so transporting a proof through the engine and reflecting back is the
transfer

  `(∀ a, P a) → (∀ a', P' a')`.

This is the abstraction-theorem `∀`-rule at the `Prop` level,
univalence-free: it only consumes the domain `Param`'s backward structure at
level `map2a` (a map `A' → A` plus `map_in_R`), exactly what `Map1_forall`
requires — no `map4`/univalence.

The codomain family member `Map1_forall` expects is a
`Param .map1 .map0 (ULift (PLift (P a))) (ULift (PLift (P' a')))`. Its forward
`map1` structure is *just a function* lifting `P a → P' a'` — precisely the
pointwise implication the caller supplies. So packaging the pointwise
implications `P a → P' a'` into the family is the whole content of the
principle: a forward `map1` on a trivial (`fun _ _ => True`) relation.

## What this subsumes

`forallTransfer` below subsumes the hand-written
`HigherOrderTransfer.forall_transfer` (which used `forall_congr'` directly): the
`Param` engine produces the `∀`-rule generically from the domain `Param` +
the pointwise implications, rather than appealing to `forall_congr'` by hand.

Not implemented here:
* the full abstraction theorem `⟦t⟧ : R_T t (⟦t⟧)` for arbitrary terms `t`
  — the `MetaM` synthesizer's job (Trocq's `param`/`trocq` tactic), which infers
  the `Param` witnesses and the `(m,n)` levels per subterm;
* the `Type`-valued motive — transferring `∀ a, B a` with `B : A → Type`
  (not `Prop`) needs `Map2a_forall`, whose domain `Param` must be at `map4`
  (`Param04` = a genuine equivalence), i.e. **univalence**. That step is already
  localized and named in `ParamForall.lean`; here we stay at the `Prop` motive,
  which is univalence-free.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

open Transfer

/-! ## Packaging a pointwise implication as a `Param .map1 .map0` family member

A pointwise implication `P a → P' a'` is exactly the forward `map1` structure on
the trivial relation `fun _ _ => True`. It is wrapped so the codomain family that
`Map1_forall` expects can be built from the caller's implications alone. -/

/-- A function `f : C → C'` packaged as the (forward-`map1`, backward-`map0`)
    `Param` carrying the trivial relation `fun _ _ => True`. Its `.fwd.map` is
    `f`. This is the codomain-family shape `Map1_forall` consumes. -/
def paramOfImpl {C C' : Type u} (f : C → C') : Param .map1 .map0 C C' where
  R := fun _ _ => True
  fwd := ⟨f⟩
  bwd := ⟨⟩

/-! ## The `∀`-transfer principle, derived from `Map1_forall`

Instantiate `Map1_forall` at the reflected `Prop`-valued families
`B a := ULift (PLift (P a))`, `B' a' := ULift (PLift (P' a'))`, with the codomain
family built by `paramOfImpl` from the *lifted* pointwise implications. The
resulting `Map1Has.map : (∀ a, ULift (PLift (P a))) → (∀ a', ULift (PLift (P' a')))`,
pre/post-composed with the (definitional) reflection `∀ a, P a ↔ ∀ a, ULift (PLift (P a))`,
is exactly the transfer `(∀ a, P a) → (∀ a', P' a')`. -/

/-- The abstraction-theorem `∀`-rule at the `Prop` level (univalence-free).

    Given a domain `Param .map0 .map2a A A'` and, for every `PA`-related pair
    `(a, a')`, a pointwise implication `P a → P' a'`, transfer a universally
    quantified proof `∀ a, P a` to `∀ a', P' a'`.

    This is `(Map1_forall PA <family>).map` at the reflected motives
    `ULift (PLift (P ·))`, with the codomain family packaged from the (lifted)
    pointwise implications via `paramOfImpl`, then reflected back through
    `ULift`/`PLift`. It is univalence-free: only the domain backward `map2a`
    (a section `A' → A` + `map_in_R`) is used. -/
def forallTransfer {A A' : Type u} (PA : Param .map0 .map2a A A')
    {P : A → Prop} {P' : A' → Prop}
    (PB : ∀ a a', PA.R a a' → (P a → P' a')) :
    (∀ a, P a) → (∀ a', P' a') :=
  fun hP a' =>
    ((Map1_forall (B := fun a => ULift.{u} (PLift (P a)))
        (B' := fun a' => ULift.{u} (PLift (P' a'))) PA
        (fun a a' aR =>
          paramOfImpl (fun x : ULift.{u} (PLift (P a)) =>
            (ULift.up (PLift.up (PB a a' aR x.down.down)))))).map
      (fun a => ULift.up (PLift.up (hP a))) a').down.down

/-! ## Re-deriving `forall_transfer` through the `Param` engine

`HigherOrderTransfer.forall_transfer` proved `(∀ i, P i) ↔ (∀ i, Q i)` from
pointwise `P i ↔ Q i` via `forall_congr'`. Both implications of
that biconditional are re-derived through `forallTransfer`, showing the `Param`
engine subsumes the hand-written rule. The domain `Param` is the diagonal on `ι` (the
identity relation, backward-`map2a` with `map := id`). -/

/-- The diagonal `Param` on any type: `R = Eq`, forward `map0`, backward `map2a`
    with section `id` and `map_in_R` reading the equality. The domain `Param`
    `forallTransfer` consumes when transferring over a *single* type (no change
    of representation), i.e. the `forall_congr'` use-case. -/
def paramDiag {ι : Type u} : Param .map0 .map2a ι ι where
  R := fun i j => i = j
  fwd := ⟨⟩
  bwd := ⟨id, fun b a (h : id b = a) => h.symm⟩

/-- Re-derivation of `forall_transfer`'s forward direction through the engine.
    From pointwise `P i → Q i`, the `Param` engine produces
    `(∀ i, P i) → (∀ i, Q i)` — no `forall_congr'`. -/
theorem forall_transfer_engine {ι : Type u} (P Q : ι → Prop) (h : ∀ i, P i → Q i) :
    (∀ i, P i) → (∀ i, Q i) :=
  forallTransfer paramDiag (fun i j (hij : i = j) => hij ▸ h i)

/-- The full biconditional, re-derived through the engine (both directions
    via `forallTransfer`). Subsumes `HigherOrderTransfer.forall_transfer`. -/
theorem forall_iff_transfer_engine {ι : Type u} (P Q : ι → Prop)
    (h : ∀ i, P i ↔ Q i) :
    (∀ i, P i) ↔ (∀ i, Q i) :=
  ⟨forall_transfer_engine P Q (fun i => (h i).mp),
   forall_transfer_engine Q P (fun i => (h i).mpr)⟩

/-- A small concrete `example`: a decidable predicate transferred across the
    diagonal. `(∀ n : ℕ, 0 ≤ n) → (∀ n : ℕ, 0 ≤ n)` produced by the engine. -/
example : (∀ n : ℕ, 0 ≤ n) → (∀ n : ℕ, 0 ≤ n) :=
  forall_transfer_engine _ _ (fun _ h => h)

/-! ## The `Num ≃ ℕ` flagship demo: transfer `∀ n : Num, …` to `∀ k : ℕ, …`

The `peano_bin_nat` flagship (`PeanoBinNat.lean`) transfers facts across the
binary↔unary natural-number equivalence. This expresses that equivalence as a domain
`Param .map0 .map2a Num ℕ` and uses `forallTransfer`
to transfer a `∀ n : Num`-statement to a `∀ k : ℕ`-statement.

The domain `Param` carries the graph relation `R n k := (n : ℕ) = k`. Its
backward `map2a` is the decoder `Num.ofNat' : ℕ → Num` together with
`map_in_R : Num.ofNat' k = n → (n : ℕ) = k`, which holds because `Num.ofNat'` is
the *right* inverse of the cast (`Num.ofNat'_eq` + the cast round-trip).
Note: `paramOfEquiv` only delivers backward `map2b` (left inverse), which is
*incomparable* to the `map2a` `Map1_forall` needs; the two-sided
bijection allows building the `map2a` domain `Param` directly here. -/

/-- The binary↔unary naturals as a domain `Param .map0 .map2a Num ℕ`: graph of
    the cast `Num → ℕ` forward (`map0`), decoder `Num.ofNat'` backward (`map2a`).
    Backward `map_in_R` uses the right inverse `(Num.ofNat' k : ℕ) = k`. -/
def paramNumNat : Param .map0 .map2a Num ℕ where
  R := fun n k => (n : ℕ) = k
  fwd := ⟨⟩
  bwd := ⟨Num.ofNat', fun k n (h : Num.ofNat' k = n) => by
    subst h; exact Num.to_of_nat k⟩

/-- `Num`-flavoured `∀`-transfer demo. A `∀ n : Num`-statement transfers to
    the corresponding `∀ k : ℕ`-statement through the `Param` engine, given the
    pointwise implication on related pairs `(n, k)` with `(n : ℕ) = k`.

    Concretely: any property of `Num` that, on related pairs, implies the `ℕ`
    property, lifts from `∀ n : Num` to `∀ k : ℕ`. -/
def numForallTransfer {P : Num → Prop} {P' : ℕ → Prop}
    (PB : ∀ (n : Num) (k : ℕ), (n : ℕ) = k → (P n → P' k)) :
    (∀ n : Num, P n) → (∀ k : ℕ, P' k) :=
  forallTransfer paramNumNat PB

/-- A concrete instance of the `Num` flagship demo: transfer
    `∀ n : Num, 0 ≤ n` to `∀ k : ℕ, 0 ≤ k`. On a related pair `(n, k)` with
    `(n : ℕ) = k`, `0 ≤ k` holds outright, so the pointwise implication is
    trivial — the engine assembles the `∀`-transfer. -/
example : (∀ n : Num, 0 ≤ n) → (∀ k : ℕ, 0 ≤ k) :=
  numForallTransfer (fun _ _ _ _ => Nat.zero_le _)

end Transfer.Param
