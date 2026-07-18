/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Combinators.ParamTrans

/-!
# The dependent-pair (`Σ`) parametricity rule

The container rules of `ParamData.lean` (`×`, `Option`, `List`) lift a relation
through *non-dependent* type formers. This file adds the **dependent** pair
`Σ a, B a`: the type of the second component depends on the value of the first.
It is the dependent generalization of the product `×` combinator, and the
value-level companion of the dependent-Π rule in `ParamForall.lean`.

A dependent pair is related when the *bases* are related by `PA` and, at the
induced witness, the *fibers* are related by the family `PB` — exactly the shape
of the heterogeneous congruence `hcongr_hetero` (`Congruence/HCongrConnection`):
the second projection of a related pair is a heterogeneous-congruence instance.

## The AdapTT functor law

AdapTT (Adjedj–Lennon-Bertrand–Benjamin–Maillard, POPL 2026) makes type-cast
adapters *functorial* over type formers: `Adapt (F X) = F (Adapt X)`. For the
dependent pair that law is `sigma_cast_eq` below — the Σ-cast is the pair of the
base cast and the fiber cast. In AdapTT it holds definitionally (a cast
calculus); here the forward map is *built* as that pair, so the law is `rfl`.

Unlike the non-dependent `×` (`ParamData`), the Σ-cast's second component depends
on the witness produced by casting the first — so it needs the base relation at
forward level `map2a` (a map whose graph is included in `R`, giving the witness),
which is the univalence-free level. No `map4`/univalence is used: this is the
value-level dependent former, below the universe.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A A' : Type u} {B : A → Type u} {B' : A' → Type u}

/-! ## The dependent-pair relation `R_sigma` -/

/-- Two dependent pairs are related when their bases are `PA`-related (by some
    witness `aR`) and, at that witness, their fibers are `(PB … aR)`-related. The
    fiber relation is a *family* indexed by the base witness — the dependent
    analogue of the product relation `R_prod`. Only `R` fields are touched, so the
    base levels stay polymorphic. -/
def R_sigma {mA nA : MapClass} (PA : Param mA nA A A')
    (PB : ∀ a a', PA.R a a' → Param .map2a .map0 (B a) (B' a')) :
    (Σ a, B a) → (Σ a', B' a') → Prop :=
  fun p q => ∃ (aR : PA.R p.1 q.1), (PB p.1 q.1 aR).R p.2 q.2

/-! ## The univalence-free forward map

Cast the base with `PA.fwd.map`, take the witness its graph provides
(`PA.fwd.map_in_R … rfl`), and cast the fiber with the family's forward map at
that witness. Needs the base forward at `map2a` (map + `map_in_R`) and the fiber
forward at `map2a` (a map). No `map4`/univalence. -/
def Map1_sigma {nA : MapClass} (PA : Param .map2a nA A A')
    (PB : ∀ a a', PA.R a a' → Param .map2a .map0 (B a) (B' a')) :
    Map1Has (R_sigma PA PB) :=
  ⟨fun p => ⟨PA.fwd.map p.1,
    (PB p.1 (PA.fwd.map p.1) (PA.fwd.map_in_R p.1 (PA.fwd.map p.1) rfl)).fwd.map p.2⟩⟩

/-! ## `Param`-level assembly at `(map1, map0)` -/

/-- The dependent-pair `Param`: forward structure `map1` (via `Map1_sigma`),
    backward structure `map0`. This is the level the univalence-free forward map
    supports — the value-level dependent former, mirroring `paramForall` on the
    Π side. -/
def paramSigma {nA : MapClass} (PA : Param .map2a nA A A')
    (PB : ∀ a a', PA.R a a' → Param .map2a .map0 (B a) (B' a')) :
    Param .map1 .map0 (Σ a, B a) (Σ a', B' a') where
  R := R_sigma PA PB
  fwd := Map1_sigma PA PB
  bwd := ⟨⟩

/-! ## The AdapTT functor law (cast form): `Adapt (Σ) = Σ (Adapt)` -/

/-- **Functoriality of the dependent pair over the adapters.** The Σ-cast is the
    pair of the base cast and the fiber cast: casting `⟨a, b⟩` yields
    `⟨cast a, cast b⟩` with the fiber cast taken at the witness the base cast
    induces. This is AdapTT's `Adapt (Σ F) = Σ (Adapt F)` in cast form — here `rfl`,
    because `Map1_sigma` is built as exactly that pair (in AdapTT it is a
    definitional cast-reduction rule). Univalence-free. -/
theorem sigma_cast_eq {nA : MapClass} (PA : Param .map2a nA A A')
    (PB : ∀ a a', PA.R a a' → Param .map2a .map0 (B a) (B' a')) (p : Σ a, B a) :
    (paramSigma PA PB).fwd.map p
      = ⟨PA.fwd.map p.1,
         (PB p.1 (PA.fwd.map p.1) (PA.fwd.map_in_R p.1 (PA.fwd.map p.1) rfl)).fwd.map p.2⟩ :=
  rfl

/-! ## Demo: a genuinely dependent cast (`Σ n, Fin (n+1)` → `Σ n, ℕ`)

The fiber type `Fin (n+1)` depends on the base `n`, and the two sides' fibers are
*different types* (`Fin (n+1)` vs `ℕ`), bridged by `Fin.val`. The Σ-cast carries
the base unchanged and the fiber through `Fin.val`. -/

/-- Diagonal base on `Nat` at `map2a` (`map := id`, graph `Eq`). -/
def natDomSigma : Param .map2a .map0 Nat Nat := ⟨Eq, ⟨id, fun _ _ h => h⟩, ⟨⟩⟩

/-- Fiber family `Fin (a+1) ↦ Nat` at `map2a`, forward map `Fin.val`. -/
def finValFib : ∀ a a', natDomSigma.R a a' → Param .map2a .map0 (Fin (a + 1)) Nat :=
  fun _ _ _ => ⟨fun x y => x.val = y, ⟨Fin.val, fun _ _ h => h⟩, ⟨⟩⟩

/-- The dependent cast sends `⟨3, 0⟩ : Σ n, Fin (n+1)` to `⟨3, 0⟩ : Σ n, Nat`,
    carrying the fiber through `Fin.val`. Different fiber types on the two sides. -/
example :
    (paramSigma (B := fun n => Fin (n + 1)) (B' := fun _ => Nat) natDomSigma finValFib).fwd.map
        ⟨3, ⟨0, by decide⟩⟩ = ⟨3, 0⟩ :=
  rfl

/-! ## Composition (AdapTT `AdaptComp` for Σ)

Two Σ-transfers compose through the generic `Param_trans` machinery — no bespoke
Σ-composition rule is needed. The composite Σ-cast is the composition of the two
Σ-casts, so `AdaptComp` holds for the dependent pair as it does for `→`/`×`. -/

variable {X Y Z : Type u}

/-- Compose two dependent-pair transfers at `(map1, map0)` — the generic relation
    composition specialized to the level `paramSigma` produces. -/
def paramSigmaTrans (S₁ : Param .map1 .map0 X Y) (S₂ : Param .map1 .map0 Y Z) :
    Param .map1 .map0 X Z where
  R := R_trans S₁ S₂
  fwd := Map1_trans S₁ S₂
  bwd := ⟨⟩

/-- **AdapTT `AdaptComp` for Σ.** Casting through the composite of two dependent
    pairs equals casting through each in turn — the Σ-cast composes. `rfl`, because
    `Map1_trans`'s forward map is the composition of the two forward maps. -/
theorem sigma_compose_cast {A B C : Type u}
    {BA : A → Type u} {BB : B → Type u} {BC : C → Type u}
    (PA : Param .map2a .map0 A B) (QA : Param .map2a .map0 B C)
    (PB : ∀ a b, PA.R a b → Param .map2a .map0 (BA a) (BB b))
    (QB : ∀ b c, QA.R b c → Param .map2a .map0 (BB b) (BC c))
    (p : Σ a, BA a) :
    (paramSigmaTrans (paramSigma PA PB) (paramSigma QA QB)).fwd.map p
      = (paramSigma QA QB).fwd.map ((paramSigma PA PB).fwd.map p) :=
  rfl

/-!
## Why composition goes through the *maps*, not a composed fiber *family*

The non-dependent product has a relational functor law
`ParamCoherence.prod_trans_rel`: the composite relation equals the composite of the
relations. Its dependent analogue would ask for a composed fiber *family*
`∀ a c, (R_trans PA QA).R a c → Param .map2a .map0 (BA a) (BC c)` — a `Type`-valued
`Param` produced from the base's composed relation. But that relation is the
existential glue `∃ b, PA.R a b ∧ QA.R b c`, a `Prop`, and producing a `Type` from
it is large elimination of `Exists`, which Lean forbids. So the dependent
composition genuinely *cannot* be phrased as a composed fiber family over the glued
base relation — it must compose the `Param`s (which carry the fibers as data), as
`paramSigmaTrans` does. This is a shadow of the same `Prop`/`Type` boundary that
caps the universe fiber (`map4`) by `UnivalenceStatus.univalence_inconsistent`.
-/

end Transfer.Param
