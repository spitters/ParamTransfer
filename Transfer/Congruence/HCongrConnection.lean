/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Combinators.ParamForall
import Transfer.Base.UnivalenceStatus

/-!
# A set-level analogue of cubical heterogeneous congruence (`hcongr`)

Emil Holm Gjørup and Bas Spitters, *Congruence Closure in Cubical Type Theory*
(2020; Cubical Agda implementation: `github.com/limemloh/cubical-congruence`)
close the *ideal congruence lemma* — heterogeneous congruence for dependent
functions — without UIP, in Cubical Type Theory. Their core lemma, with the
function/family paths written as `PathP`:

```
hcongr_ideal :
  (fg : PathP (λ i → (a : A i) → C i a) f g) →
  (ab : PathP A a b) →
  PathP (λ i → C i (ab i)) (f a) (g b)
```

This file makes the structural correspondence to the CatCrypt Trocq port
(`ParamForall.lean`) concrete: `hcongr_ideal` is exactly Trocq's dependent-Π
relational combinator `R_forall` with the relation taken to be a `PathP`
(identity/equivalence) instead of a general `(m, n)` Param relation. Lining up
the three slots:

| `hcongr_ideal` (cubical)              | Trocq `R_forall` (relational)            |
|---------------------------------------|------------------------------------------|
| `fg : PathP (λ i → (a:A i)→C i a) f g`| `f`, `g` related by `R_forall PA PB`     |
| `ab : PathP A a b` (argument path)    | argument witness `aR : PA.R a a'`        |
| `PathP (λ i → C i (ab i)) (f a)(g b)` | result `(PB a a' aR).R (f a) (g a')`     |

`R_forall PA PB f g := ∀ a a' (aR : PA.R a a'), (PB a a' aR).R (f a) (f' a')`
is, slot-for-slot, "given an argument relation `aR`, the results are related by
the family `PB` indexed at that witness" — precisely `hcongr_ideal` with `PathP`
substituted for `PA.R` and `(PB …).R`.

## The UA-free fragment realized in Lean

The *full* `hcongr_ideal` over `PathP` needs cubical/computational univalence:
its `PathP A a b` is the **univalent** identity, and a varying type-family path
(`A i`, `C i` genuinely depending on the interval `i`) requires transporting the
motive along an equivalence-as-equality. Lean's built-in `Eq` cannot be that
identity — `univalence_inconsistent` (`UnivalenceStatus.lean`) shows UA stated
via `Eq` is `False`, because `Eq`'s definitional proof irrelevance makes type
equality a subsingleton. This is the same boundary that caps the Param port at
`map3` and forces `Map2a_forall` to require `map4`.

But the constant type-family-path fragment of `hcongr_ideal` — where the
ambient path `A i ≡ A`, `C i ≡ C` is reflexivity, so the only motion is in the
argument and the fibers — is UA-free, and it is *exactly* `R_forall` /
`paramForall` instantiated at the diagonal `Eq` relation:

* `congr_of_R_forall` — the non-dependent shadow: `R_forall` at the diagonal
  gives `f = g → a = b → f a = g b` (Lean's plain `congr`).
* `hcongr_of_R_forall` — the dependent shadow over a
  dependent codomain `C : T → Type`: `R_forall` at the diagonal gives
  `a = b → HEq (f a) (g b)`. This is the UA-free instance of `hcongr_ideal`
  with constant type-family path, with Lean's `HEq` standing in for the fiber
  `PathP (λ i → C i (ab i))` over the reflexive ambient.

## The diagonal is the degenerate case; the general rule is UA-free heterogeneous congruence

The two shadows above take the fiber relation to be `Eq`/`HEq` — a type *equality*
between the fibers — which is why they collapse to Lean's native `congr`/`hcongr`.
But that `HEq` presentation is what makes `hcongr_ideal` look UA-gated: forcing
the fibers to be *equal types* is the object-level-univalence framing.

Trocq's own move is to reason with an equivalence's *data* instead of a type
*equality* — that is what makes transfer free below the universe. Applied here:
replace the fiber `HEq` with a graded `Param`, and the block disappears. The
engine's *general* dependent-Π relation `R_forall PA PB` (`ParamForall.lean`)
already relates fibers `B a`, `B' a'` that are **genuinely different types**, tied
by an arbitrary `Param mB nB (B a) (B' a')` rather than by `HEq`. That plays the
role of heterogeneous congruence across a change of representation, with
equivalence data in place of a type equality — and it needs no univalence.
`hcongr_hetero` below states it; the diagonal shadows are its `PB := Eq/HEq`
specialization.

The only residual univalence is the **universe-valued fiber** — heterogeneous
congruence over a family whose fibers are `Type` itself, i.e. `map4`
(`Param_Type`). That is the same `map3`-reachable / `map4`-capped boundary the
whole engine lives on (`univalence_inconsistent`), not a boundary special to
`hcongr`. So the honest reading is coverage, not impossibility: the UA-free
fragment of `hcongr` is `R_forall` at a graded `Param`; only the universe-valued
case is out of reach, and for the same reason as everything else.

`R_forall` at a graded `Param` discharges congruence over genuinely different
fiber types without univalence — the set-level counterpart of the shape
`hcongr_ideal` discharges with `PathP`. This analogy motivates the design. The
lemmas below stand on their own; the cubical lemma is cited for context.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param.HCongrConnection

/-! ## The diagonal domain `Param` at the levels the dependent-Π forward map needs

`Map1_forall`/`paramForall` consume a domain `Param .map0 .map2a` (forward
trivial, backward map plus graph inclusion). The diagonal — `R := Eq`, backward
`map := id`, `map_in_R := Eq.symm` — is the canonical such relation and the
Lean-side instance of the cubical *reflexive ambient path* `A i ≡ A`. -/

/-- The diagonal on `T` as the dependent-Π domain input: forward `map0`,
    backward `map2a` (`map := id`, `map_in_R := Eq.symm`). This is the
    set-level shadow of the cubical constant ambient path `A i ≡ A`. -/
def paramEqDom (T : Type u) : Param .map0 .map2a T T where
  R := Eq
  fwd := ⟨⟩
  bwd := ⟨id, fun _ _ h => h.symm⟩

/-! ## Non-dependent shadow: `R_forall` at the diagonal = `congr` -/

/-- Constant-codomain family at the diagonal: each fiber relation is `Eq`,
    forward map `id`. The set-level shadow of a constant fiber path `C i ≡ C`. -/
def paramEqFam {T : Type u} (C : Type u) :
    ∀ a a', (paramEqDom T).R a a' → Param .map1 .map0 C C :=
  fun _ _ _ => { R := Eq, fwd := ⟨id⟩, bwd := ⟨⟩ }

/-- `R_forall` at the diagonal is pointwise equality. The dependent-Π
    relation, specialised to `Eq` in both the argument and the fibers, says two
    functions agree on equal inputs — i.e. they are pointwise equal. This is the
    relation slot of `hcongr_ideal` collapsed to the set level. -/
theorem R_forall_diag_iff {T C : Type u} (f g : T → C) :
    R_forall (B := fun _ => C) (B' := fun _ => C) (paramEqDom T) (paramEqFam C) f g
      ↔ ∀ a, f a = g a := by
  constructor
  · intro h a; exact h a a rfl
  · intro h a a' (haa' : a = a'); subst haa'; exact h a

/-- The non-dependent `hcongr_ideal` shadow. From `R_forall`-relatedness at
    the diagonal (the data of `fg : PathP … f g` at the set level) and an
    argument equality `a = b` (the data of `ab : PathP A a b` at the set level),
    conclude `f a = g b` — Lean's plain congruence. This is `hcongr_ideal` with
    constant ambient path, constant fiber, and `Eq` for `PathP`. -/
theorem congr_of_R_forall {T C : Type u} {f g : T → C}
    (hfg : R_forall (B := fun _ => C) (B' := fun _ => C)
      (paramEqDom T) (paramEqFam C) f g)
    {a b : T} (hab : a = b) : f a = g b := by
  subst hab; exact hfg a a rfl

/-- The forward dependent-Π map `Map1_forall` at the diagonal is the identity on
    functions: the engine's combinator computes to plain application, confirming
    the combinator (not just its relation) degenerates to `congr`. -/
theorem Map1_forall_diag_map {T C : Type u} (f : T → C) :
    (Map1_forall (B := fun _ => C) (B' := fun _ => C)
      (paramEqDom T) (paramEqFam C)).map f = f := rfl

/-! ## Dependent shadow: `R_forall` at the diagonal = dependent `HEq` congruence

The dependent case. The codomain is a dependent family
`C : T → Type`; fibers `C a` and `C a'` are distinct types, equal only once an
argument equality `a = a'` is in hand. Lean's `HEq` is the set-level stand-in
for the fiber `PathP (λ i → C i (ab i))` over a *reflexive ambient* path: with
`A i ≡ A`, `C i ≡ C`, the fiber path degenerates to a heterogeneous equality
between `C a` and `C b` justified by `a = b`. -/

/-- The dependent codomain family at the diagonal, fibers related by `HEq`.
    The forward map transports `C a → C a'` along the argument equality. This is
    the set-level shadow of a constant *fiber* path `C i ≡ C` over a varying
    base index. -/
def paramHEqFam {T : Type u} (C : T → Type u) :
    ∀ a a', (paramEqDom T).R a a' → Param .map1 .map0 (C a) (C a') :=
  fun _ _ (h : _ = _) => { R := fun x y => HEq x y, fwd := ⟨fun x => h ▸ x⟩, bwd := ⟨⟩ }

/-- The dependent `hcongr_ideal` shadow (constant type-family path). Over a
    genuine dependent codomain `C : T → Type`, `R_forall`-relatedness at the
    diagonal plus an argument equality `a = b` give `HEq (f a) (g b)`. This is
    `hcongr_ideal` with the ambient and fiber paths reflexive (`A i ≡ A`,
    `C i ≡ C`), `Eq` for the argument `PathP`, and `HEq` for the result
    `PathP (λ i → C i (ab i))` — the UA-free fragment, expressible because no
    type-equivalence transport is required (only `Eq`/`HEq`, both set-level). -/
theorem hcongr_of_R_forall {T : Type u} {C : T → Type u} {f g : ∀ a, C a}
    (hfg : R_forall (paramEqDom T) (paramHEqFam C) f g)
    {a b : T} (hab : a = b) : HEq (f a) (g b) := by
  subst hab; exact hfg a a rfl

/-! ## Off the diagonal: the UA-free heterogeneous fragment (the general rule)

The theorems above run at the diagonal (`Eq`/`HEq` fibers) and reduce to native
congruence. The general dependent-Π relation `R_forall PA PB` already relates
fibers `B a`, `B' a'` of *different types* through an arbitrary graded `Param`
`PB a a' aR : Param mB nB (B a) (B' a')`. Extracting the fiber relatedness of a
single applied pair from an `R_forall` witness is heterogeneous congruence across
a representation change — the object the diagonal shadows are shadows of.

Both directions of `PA` and both fiber levels stay polymorphic: the amount of
structure you get out is graded exactly like the rest of the engine. At `map0`
fibers you only *relate* `f a` and `g a'`; at `map2b`+ (a forward map with
`R_in_map`) you can *transport* — actually move `f a` onto the `B' a'` side, the
constructive analogue of `coe` along the cubical `PathP`. No univalence is used
below the universe-valued (`map4`) fiber. -/

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u}

/-- **Heterogeneous congruence, UA-free.** From an `R_forall` witness relating
    `f` and `g`, and a domain witness `aR : PA.R a a'`, the applied outputs
    `f a : B a` and `g a' : B' a'` — living in *different* types — are related by
    the fiber `Param`. This is `R_forall`'s defining clause read as a congruence
    rule; unlike `hcongr_of_R_forall` it does not force the fibers equal, so it is
    genuine cross-representation congruence, not native `congr`. All levels are
    polymorphic; axiom-free. -/
theorem hcongr_hetero {mA nA mB nB : MapClass} (PA : Param mA nA A A')
    (PB : ∀ a a', PA.R a a' → Param mB nB (B a) (B' a'))
    {f : ∀ a, B a} {g : ∀ a', B' a'}
    (hfg : R_forall PA PB f g) {a a'} (aR : PA.R a a') :
    (PB a a' aR).R (f a) (g a') :=
  hfg a a' aR

/-- **Transport form.** When the fiber sits at level `map2b`+ (a forward map whose
    graph includes `R`), heterogeneous congruence yields an *equation*: the fiber's
    forward map carries `f a` onto `g a'`. This is the value-level transport the
    cubical `PathP` computes, here delivered by the graded map rather than by a
    univalent path. Axiom-free. -/
theorem hcongr_hetero_transport {mA nA nB : MapClass} (PA : Param mA nA A A')
    (PB : ∀ a a', PA.R a a' → Param .map2b nB (B a) (B' a'))
    {f : ∀ a, B a} {g : ∀ a', B' a'}
    (hfg : R_forall PA PB f g) {a a'} (aR : PA.R a a') :
    (PB a a' aR).fwd.map (f a) = g a' :=
  (PB a a' aR).fwd.R_in_map (f a) (g a') (hfg a a' aR)

/-! ### Demo: genuinely different fiber types (`Fin (n+1)` ↔ ℕ)

The fibers on the two sides are *distinct types* — `Fin (a+1)` and `ℕ` — related
by the forward map `Fin.val`. Native `congr` cannot relate `f a : Fin (a+1)` to
`g b : ℕ` (no `Fin.val` is inserted); the heterogeneous rule does, and its
transport form recovers the `Fin.val` equation. -/

/-- The zero of `Fin (n+1)`. -/
def finZero (n : ℕ) : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩

/-- The fiber family `Fin (a+1) ↦ ℕ` at level `map2b`: forward map `Fin.val`,
    relation its graph. A genuine change of representation (different types). -/
def finValFam : ∀ a a', (paramEqDom ℕ).R a a' → Param .map2b .map0 (Fin (a + 1)) ℕ :=
  fun _ _ _ => { R := fun x y => x.val = y, fwd := ⟨Fin.val, fun _ _ h => h⟩, bwd := ⟨⟩ }

/-- Heterogeneous congruence across `Fin (a+1) ↔ ℕ`: from `a = b`, the left output
    `finZero a : Fin (a+1)` and the right output `0 : ℕ` are related by `Fin.val`. -/
example (a b : ℕ) (h : a = b) : (finZero a).val = (fun _ : ℕ => (0 : ℕ)) b :=
  hcongr_hetero (B := fun n => Fin (n + 1)) (B' := fun _ => ℕ)
    (paramEqDom ℕ) finValFam (f := finZero) (g := fun _ => 0) (fun _ _ _ => rfl) h

/-- The transport form recovers the same `Fin.val` equation through the fiber map. -/
example (a b : ℕ) (h : a = b) : Fin.val (finZero a) = (fun _ : ℕ => (0 : ℕ)) b :=
  hcongr_hetero_transport (B := fun n => Fin (n + 1)) (B' := fun _ => ℕ)
    (paramEqDom ℕ) finValFam (f := finZero) (g := fun _ => 0) (fun _ _ _ => rfl) h

/-! ## The dependent-congruence tactics

Where `rcongr` (`RCongr.lean`) descends a *cross-head* op-tree and `hgcongr`
descends a cross-head goal keyed by a registered head pair, these descend a
*dependent* application across a representation change. Given the function
relatedness witness `h : R_forall PA PB f g`, the tactic reduces an applied-output
goal to just the domain witness `PA.R a a'` — the dependent, heterogeneous
generalization of the congruence step (`gcongr`/`congr` reduce an application to
its argument goals; these do the same when the two sides live in *different*
fiber types). Passing `h` explicitly pins `PA`, `PB`, `f`, `g`, so no
higher-order unification is needed; the residual domain-witness goal composes with
`param_solve`/`rcongr`/`assumption`. -/

/-- `hcongr_dep h` — relation form: reduce `(PB a a' aR).R (f a) (g a')` to the
    domain witness `PA.R a a'`, given `h : R_forall PA PB f g`. -/
macro "hcongr_dep " h:term : tactic => `(tactic| refine hcongr_hetero _ _ $h ?_)

/-- `hcongr_transport h` — transport form: reduce a transport equation
    `(PB a a' aR).fwd.map (f a) = g a'` (fiber `map2b`+) to the domain witness. -/
macro "hcongr_transport " h:term : tactic => `(tactic| refine hcongr_hetero_transport _ _ $h ?_)

/-! ### Demo: closing a heterogeneous goal with the tactic

`fLast n := Fin.last n : Fin (n+1)` on the left, `gId n := n : ℕ` on the right
(non-constant, so the argument is pinned), related pointwise by `Fin.val`. -/

/-- Pointwise relatedness of `Fin.last` and the identity through `Fin.val`. -/
theorem finLastWitness :
    R_forall (paramEqDom ℕ) finValFam (fun n => Fin.last n) (fun n => n) :=
  fun a a' (h : a = a') => (Fin.val_last a).trans h

/-- The transport goal `Fin.val (Fin.last a) = b`, closed by `hcongr_transport`
    down to the domain witness `a = b`. -/
example (a b : ℕ) (h : a = b) : Fin.val (Fin.last a) = (fun n => n) b := by
  hcongr_transport finLastWitness
  exact h

/-- The relation form, closed by `hcongr_dep`. -/
example (a b : ℕ) (h : a = b) : (Fin.last a).val = (fun n => n) b := by
  hcongr_dep finLastWitness
  exact h

end Transfer.Param.HCongrConnection
