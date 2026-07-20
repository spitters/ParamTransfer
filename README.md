# Transfer — relational proof transfer in Lean

A self-contained Lean 4 + Mathlib library for **reasoning up to a registered
relation**. A relation is declared once, stating how an abstract value relates to a
concrete representation of it; the library then *synthesizes* witnesses of that relation,
*transfers* statements and terms across it, and *decides* it structurally by
congruence — emitting kernel-checked proof terms throughout.

It draws on modular parametricity (**Trocq**'s lattice and combinators), relational
congruence closure, functorial type-casts (the **AdapTT** functor laws +
description-based deriving), heterogeneous congruence (the set-level form of cubical
`hcongr`), and data refinement (**CoqEAL**), and reuses Lean's own relational
automation (`grind`, `gcongr`, `simp`/`norm_cast`, type classes, `conv`, `aesop`,
`mvcgen`). These are one inference rule seen from different sides — the unifying rule
below. **Trocq** is the largest single influence; the synthesis and the single auto
tactic (`param_auto`) that dispatches to all of the surfaces above are the
library's contribution.

**Applications.** **Compiler verification** — the CatCrypt compiler, relating emitted
low-level code to its clean algebraic spec — and **program verification**: `mvcgen` /
`Std.Do` triple transfer, and reasoning about hax-extracted code up to its
representation.

Single entry point: `import Transfer`. Released under **LGPL-3.0** (see `LICENSE`).

## Documentation

- **[Manual](https://spitters.github.io/ParamTransfer/)** — concepts, tactics, and worked examples
- **[API reference](https://spitters.github.io/ParamTransfer/api/)** — per-declaration signatures and docstrings, no proof bodies

CI publishes both from `main` to GitHub Pages. To build them locally, see the
manual and API-reference subsections under [Building](#building).

## Building

See [BUILDING.md](BUILDING.md) for the full instructions — the library, use as a
dependency, the manual, and the API reference. The short form:

```sh
lake exe cache get            # fetch prebuilt Mathlib oleans — run this FIRST
LAKE_JOBS=6 lake build Transfer
```

## One relation, three uses

The whole library is operations on a single object: a **relation `R`** between a
value and a representation of it — `Related enc a b` (`enc a = b`, the encoding
view) or, graded, `Param (m n) A B` (relation + maps). The relation `R` is registered
once, via attributes (`@[param]`, `@[transfer]`, `RelatedBinOp` instances, `deriving
Param`). Three operations then act on it.

**1 — Build `R a b` (synthesis).** Find or compose a witness. *This is type-class
resolution*: `HasParam`/`Related` instance search composes registered witnesses
through the structure of a term (the Lean analogue of Trocq's Elpi search).

```lean
example (a b c : F) : Related (id : F → F) (a * b + c) (radd (rmul a b) c) :=
  inferInstance        -- composed from the registered RelatedBinOp squares
```

**2 — Transfer a goal along `R` (parametricity).** Move a `∀`-statement to the
other representation with `param_transfer`, or emit a term's `⟦·⟧` translation
with `#transfer`.

```lean
-- ℤ ↠ ZMod p: an integer fact transfers to its modular image.
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) + 0 = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, x + 0 = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) h
  rw [← hix]; exact h

#transfer (fun x : Nat => Nat.succ x * x)   -- ⟦·⟧ : the term + its relatedness proof
```

**3 — Decide `R a b` structurally (congruence).** Relate two structurally similar
terms — relational congruence closure.

```lean
example (a b c : F) : a * b + c = radd (rmul a b) c := by param_solve
```

## The unifying inference rule

All three uses run on one inference rule:

> **related arguments give related applications** — from `R aᵢ bᵢ` infer
> `R (f a…) (g b…)`  (`R_arrow` / `R_forall`).

This single rule is, simultaneously:

* the **application/λ rule** of the parametricity translation (use 2),
* the **congruence step** of the closure tactics (use 3),
* **AdapTT's functoriality** of type formers — what lets `R` compose through
  `→`, `×`, and inductive types,
* and **heterogeneous congruence** — the general `R_forall` relates outputs of
  *different* fiber types across a representation change (`hcongr_hetero`,
  `HCongrConnection`).

Trocq, the congruence tactics, AdapTT, and cubical `hcongr` are four views of
the same rule. The rest of the library is *where each use bottoms out*: type
classes discharge synthesis, `grind` discharges the equational congruence-closure
core, and `simp`/`norm_cast`/`gcongr`/`conv`/`aesop`/`mvcgen` are native surfaces
it plugs into.

Two axes: a **vertical** one — transfer *across* representations (parametricity)
— and a **horizontal** one — congruence *within* a representation, meeting at the
functoriality rule above.

## The one tactic — `param_auto`

One coordinator dispatches to every surface above, so a single call site closes
goals living in *different* relations — it routes each to the tactic that closes
it (`param_solve`, `rcongr`, `norm_cast`, `gcongr`, `grind`):

```lean
example (a : Nat) : a + 0 = a := by param_auto                    -- Eq
example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by param_auto  -- ≤, via gcongr
example (a b : Nat) :                                             -- cast graph, via norm_cast
    ((a + b : Nat) : Int) = (a : Int) + b := by param_auto
example (a b c : F) :                                             -- registered rep. change, via rcongr
    a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_auto
```

The call site is stable: the dispatch strategy underneath can be reordered or
made goal-directed without touching any proof. The specialized tactics below
stay available when a proof wants one strategy by name.

## The relation, graded

A relation can carry different amounts of structure, and a transfer needs only as
much as the goal demands. `Param (m n) A B` grades this:

| What `R` carries | Use it for |
|---|---|
| a bare relation | relate values that share no maps |
| a forward map (a **cast** `A → B`) | push a value/computation to its representation |
| a backward **decoder** (`B → A`) | a **retraction** — pull a representation back (e.g. `ℤ ↠ ZMod p`) |
| both, coherent | an **equivalence** (e.g. `ℕ ↔ binary`) |

Register the relation at the provable strength, and the level solver (`ParamInfer`)
picks the *minimum* a given goal needs, weakening down the lattice (`ParamWeaken`,
`auto_weaken`). Worked examples: `ParamRetraction` (`ℤ↠ZMod p` / `ℕ↠ZMod p`),
`ParamCryptoExamples` (ℕ↔binary, `Num↦ℕ`), `ExampleField` (a registered-op /
identity demo — pedagogical, *not* a cross-type encoding; see `MachineLimbField`
for the genuine `BitVec 64 ↠ ZMod p` field retraction).

## Composition & derivation (functoriality)

What makes transfer *compositional* and *extensible*:

* **The relation `R` composes** — `Param_trans` glues `A↔B` and `B↔C` into `A↔C`.
* **casts compose and preserve identity** — `cast_trans` (= AdapTT's `AdaptComp`:
  `cast (R∘S) = cast S ∘ cast R`) and `cast_id` (`AdaptId`); the
  combinators distribute over composition (`ParamCoherence`). These *certify* the
  functor laws: in Lean the composite's forward map is already function
  composition, so the laws hold by `rfl` and composition through nested type
  formers is automatic — where AdapTT needs a definitional cast calculus, Lean's
  defeq suffices. They are cited explicitly where a chain is built by hand
  (e.g. CatCrypt's dialect-chain transport). The **dependent** formers extend the
  non-dependent `→`/`×`/`List` laws: `paramForall` (Π) and `paramSigma` (Σ,
  `sigma_cast_eq` = `Adapt Σ = Σ Adapt`) carry the same functoriality into the
  dependent world.
* **inductive `R` is derived** — `deriving Param` reads an inductive's
  constructor signature (AdapTT's `IndDesc`), generates its constructor-wise
  relation and a full `Param` instance, and rejects mixed-variance inductives
  (AdapTT's Non-example). Covers records, enums, and uniform-recursive
  (`List`/`Tree`-shape) types.

```lean
inductive Pair (A B : Type) | mk : A → B → Pair A B
  deriving Param
```

## The congruence layer

Four tactics, one relation, two strategies plus their union (full reference:
[`TACTICS.md`](TACTICS.md)):

| Tactic | Strategy | Closes |
|---|---|---|
| `rcongr` / `hgcongr` | top-down **descent** | a registered cross-head op-tree, leaving per-argument relatedness subgoals |
| `param_cc` | bottom-up **closure** (via `grind`) | transitivity / context-hypothesis chains |
| `param_solve` | **descent + closure-leaf** | the union of the above — the default |

The `hgcongr` tactic is the **heterogeneous generalization of `gcongr`**: an attribute-driven
(`@[hgcongr]`), head-*pair*-keyed congruence that relates *different* head
functions `f ≠ g` — the case `gcongr` structurally rejects. It carries the exact
upstream `Mathlib.Tactic.GCongr.Core` patch that would lift this (`HGCongr.lean`).

## Plugging into Lean

The library cooperates with native machinery and reuses it. A standing
invariant: transfer is only as sound as the *registered*
witnesses, so a missing witness stays a **visible residual goal** (hence the
`aesop` set is opt-in — it never silently searches for a square).

| Mechanism | Role |
|---|---|
| **type classes** | the synthesis engine (`HasParam`/`Related` resolution) |
| **`grind`** | the equational congruence-closure backend for `param_cc` (foundation squares dual-tagged `@[grind =]`) |
| **`gcongr`** | homogeneous congruence; `hgcongr` is its cross-head generalization |
| **`simp` / `norm_cast`** | the closed-equation fast path; a `@[norm_cast]` move-lemma *is* a transfer witness over the cast graph (`ParamNormCast`) |
| **`conv`** | focused sub-term transfer (`transferConv`) |
| **`aesop`** | an opt-in `Transfer` rule set bundling the transfer rules |
| **`Std.Do` / `mvcgen`** | Hoare-triple transfer via the Kleisli relation `RComp` (`ParamTripleTransfer`) |
| **coercions** | a `Coe`/`CoeTC` derived from a forward map (`ParamCoe`) |

## Quick start

```lean
import Transfer
open Transfer.Param

-- register a witness
@[param] theorem fooR : RArrow Eq Eq foo foo := fun _ _ h => congrArg foo h

-- transfer a ∀-statement across ℤ ↠ ZMod p (domain relation auto-resolved)
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) + 0 = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, x + 0 = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) h
  rw [← hix]; exact h

-- derive the relation for a data type
inductive Pair (A B : Type) | mk : A → B → Pair A B deriving Param

-- close a representation-change equation by congruence
example (a b c : F) : a * b + c = radd (rmul a b) c := by param_solve
```

Full per-tactic / per-attribute reference: [`TACTICS.md`](TACTICS.md).

## File map (reference)

The source under `Transfer/` is organized into concept subdirectories:

| `Transfer/` subdir | Modules |
|---|---|
| `Hierarchy/` | `ParamHierarchy`, `ParamLevel`, `ParamWeaken`, `ParamEquiv` |
| `Combinators/` | `ParamArrow`, `ParamForall`, `ParamData`, `ParamTrans`, `ParamCoherence` |
| `Synthesis/` | `ParamSynth(Ext)`, `ParamResolve`, `ParamInfer` |
| `Translate/` | `ParamTranslate(Ty/Op/Full)`, `ParamDB` |
| `Statements/` | `ParamTransfer` (`∀`-transfer), `ParamForallNested`, `ParamTransferTac` (`param_transfer`) |
| `Congruence/` | `RCongr`, `HGCongr(Init)`, `ParamCongrClosure`, `ParamSolve`, `GCongrProbe`, `HCongrConnection` |
| `Deriving/` | `ParamDeriveHandler`, `ParamDerive` |
| `Integrations/` | `ParamNormCast`, `ParamCoe`, `ParamConv`, `GrindIntegration`, `AesopIntegration`(`+RuleSet`), `ParamTripleTransfer`, `ParamAutoWeaken` |
| `Examples/` | `ExampleField`, `ParamRetraction`, `ParamCryptoDomains`, `ParamCryptoExamples`, `PeanoBinNat` |
| `Base/` | `Core`, `Related`, `RelatedAt`, `FieldRegistry`, `UnivalenceStatus` (the `Related`/`RelatedBinOp` substrate); `Hierarchy`, `Levels`, `TransferTactic`, `HigherOrderTransfer` (the class-hierarchy / level / tactic substrate the engine reuses) |

The root `Transfer.lean` is the single entry point.

## Provenance

Builds on the work credited in
[`ATTRIBUTION.md`](ATTRIBUTION.md): **Trocq** (Cohen–Crance–Mahboubi — the
parametricity lattice and combinators the engine's core adapts), **AdapTT**
(functorial casts + description-based deriving), **CoqEAL** (data refinement), the
**cubical congruence** of Gjørup–Spitters, and **Lean 4 / Mathlib**.
