# Transfer — relational proof transfer in Lean

Transfer is a Lean 4 + Mathlib library for reasoning up to a registered relation.
A user declares once how an abstract value relates to a concrete representation of
it. The library then synthesizes witnesses of that relation, transfers statements
and terms across it, and decides it structurally by congruence. Every step
produces a kernel-checked proof term.

The design follows **Trocq**'s modular parametricity: its lattice of relation
strengths and its combinators. It also draws on relational congruence closure, on
functorial type casts and description-based deriving from **AdapTT**, on
heterogeneous congruence (the set-level form of cubical `hcongr`), and on data
refinement from **CoqEAL**. It builds on Lean's relational automation: `grind`,
`gcongr`, `simp`/`norm_cast`, type classes, `conv`, `aesop` and `mvcgen`. The
library adds the witness synthesis, the transfer tactics, and one
coordinating tactic, `param_auto`, that dispatches to all of these surfaces.

The library is used in compiler verification, to relate emitted low-level code to
its algebraic specification, and in program verification, to transfer `mvcgen` /
`Std.Do` triples and to reason about code extracted from Rust by hax up to its
representation.

Single entry point: `import Transfer`. Released under **LGPL-3.0** (see `LICENSE`).

## Documentation

- **[Manual](https://spitters.github.io/ParamTransfer/)** — concepts, tactics, and worked examples
- **[API reference](https://spitters.github.io/ParamTransfer/api/)** — per-declaration signatures and docstrings, no proof bodies

CI publishes both from `main` to GitHub Pages. To build them locally, see the
manual and API-reference subsections under [Building](#building).

The Lean code blocks in this README are verbatim excerpts of
[`Transfer/Examples/Readme.lean`](Transfer/Examples/Readme.lean), which compiles
them against the library.

## Building

See [BUILDING.md](BUILDING.md) for the full instructions: the library, use as a
dependency, the manual, and the API reference. The short form:

```sh
lake exe cache get            # fetch prebuilt Mathlib oleans — run this FIRST
LEAN_NUM_THREADS=6 lake build Transfer
```

## One relation, three uses

The library operates on a single object: a **relation `R`** between a value and a
representation of it. The relation takes one of two forms: `Related enc a b`
(`enc a = b`, the encoding view) or, graded, `Param (m n) A B` (relation + maps).
It is registered once through attributes (`@[param]`, `@[transfer]`,
`RelatedBinOp` instances, `deriving Param`). Three operations then act on it.

**1 — Build `R a b` (synthesis).** Type-class resolution finds or composes a
witness. `HasParam`/`Related` instance search composes registered witnesses
through the structure of a term, as Trocq's Elpi search does in Coq.

```lean
example (a b c : F) : Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c) :=
  inferInstance        -- composed from the registered RelatedBinOp squares
```

**2 — Transfer a goal along `R` (parametricity).** `param_transfer` moves a
`∀`-statement to the other representation, and `#transfer` emits the `⟦·⟧`
translation of a term.

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

**3 — Decide `R a b` structurally (congruence).** Relational congruence closure
relates two structurally similar terms.

```lean
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_solve
```

In these examples `F` is `ZMod p` for the prime `p = 2^31 - 2^27 + 1`, and
`bbFieldMul`/`bbFieldAdd` are two operations (`Transfer/Examples/ExampleField.lean`)
registered as realizations of `*` and `+` (`Transfer/Base/Related.lean`).

## The unifying inference rule

All three uses run on one inference rule:

> **related arguments give related applications** — from `R aᵢ bᵢ` infer
> `R (f a…) (g b…)`  (`R_arrow` / `R_forall`).

The same rule appears in four places:

* as the **application/λ rule** of the parametricity translation (use 2),
* as the **congruence step** of the closure tactics (use 3),
* as **AdapTT's functoriality** of type formers, which lets `R` compose through
  `→`, `×`, and inductive types,
* and as **heterogeneous congruence**: the general `R_forall` relates outputs of
  *different* fiber types across a representation change (`hcongr_hetero`,
  `HCongrConnection`).

Each use bottoms out in existing Lean machinery. Type classes discharge synthesis,
`grind` discharges the equational congruence-closure core, and
`simp`/`norm_cast`/`gcongr`/`conv`/`aesop`/`mvcgen` are native surfaces the
library connects to.

The library has two axes. The vertical axis is transfer *across* representations
(parametricity). The horizontal axis is congruence *within* a representation. The
functoriality rule above connects them.

## The coordinating tactic — `param_auto`

`param_auto` dispatches to every surface above, so one call site closes goals in
*different* relations. It routes each goal to the tactic that closes it
(`param_solve`, `rcongr`, `norm_cast`, `gcongr`, `grind`):

```lean
example (a : Nat) : a + 0 = a := by param_auto                    -- Eq
example (a b : Nat) (h : a ≤ b) : a + 1 ≤ b + 1 := by param_auto  -- ≤, via gcongr
example (a b : Nat) :                                             -- cast graph, via norm_cast
    ((a + b : Nat) : Int) = (a : Int) + b := by param_auto
example (a b c : F) :                                             -- registered rep. change, via rcongr
    a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_auto
```

The dispatch strategy can be reordered or made goal-directed without changing any
proof that calls `param_auto`. The specialized tactics below remain available for
a proof that names one strategy.

## The relation, graded

A relation carries more or less structure, and a transfer uses only as much as
the goal requires. `Param (m n) A B` grades this:

| What `R` carries | Use it for |
|---|---|
| a bare relation | relate values that share no maps |
| a forward map (a **cast** `A → B`) | push a value/computation to its representation |
| a backward **decoder** (`B → A`) | a **retraction** — pull a representation back (e.g. `ℤ ↠ ZMod p`) |
| both, coherent | an **equivalence** (e.g. `ℕ ↔ binary`) |

A relation is registered at the strength that can be proved. The level solver
(`ParamInfer`) then picks the *minimum* strength a given goal needs and weakens
down the lattice (`ParamWeaken`, `auto_weaken`). Worked examples: `ParamRetraction`
(`ℤ↠ZMod p` / `ℕ↠ZMod p`), `ParamCryptoExamples` (ℕ↔binary, `Num↦ℕ`), and
`ExampleField`, a registered-operation demo with the identity encoding. The
cross-type field retraction `BitVec 64 ↠ ZMod p` is in `MachineLimbField`.

## Composition & derivation (functoriality)

Transfer composes and extends through three mechanisms:

* **The relation `R` composes.** `Param_trans` glues `A↔B` and `B↔C` into `A↔C`.
* **Casts compose and preserve identity.** `cast_trans` is AdapTT's `AdaptComp`
  (`cast (R∘S) = cast S ∘ cast R`) and `cast_id` is `AdaptId`; the combinators
  distribute over composition (`ParamCoherence`). These theorems certify the
  functor laws. In Lean the composite's forward map is function composition, so
  the laws hold by `rfl`, and composition through nested type formers needs no
  further proof. AdapTT obtains the same laws from a definitional cast calculus.
  The laws are cited explicitly where a proof builds a chain of casts by hand.
  The dependent formers extend the non-dependent `→`/`×`/`List` laws:
  `paramForall` (Π) and `paramSigma` (Σ, `sigma_cast_eq` = `Adapt Σ = Σ Adapt`)
  carry the same functoriality to dependent types.
* **Inductive `R` is derived.** `deriving Param` reads an inductive's constructor
  signature (AdapTT's `IndDesc`) and generates its constructor-wise relation and a
  full `Param` instance. It rejects mixed-variance inductives (AdapTT's
  Non-example). It covers records, enums, and uniform-recursive
  (`List`/`Tree`-shape) types.

```lean
inductive Pair (A B : Type) | mk : A → B → Pair A B
  deriving Param
```

## The congruence layer

Four tactics act on one relation with two strategies and their union (full
reference: [`TACTICS.md`](TACTICS.md)):

| Tactic | Strategy | Closes |
|---|---|---|
| `rcongr` / `hgcongr` | top-down **descent** | a registered cross-head op-tree, leaving per-argument relatedness subgoals |
| `param_cc` | bottom-up **closure** (via `grind`) | transitivity / context-hypothesis chains |
| `param_solve` | **descent + closure-leaf** | the union of the above — the default |

`hgcongr` is the **heterogeneous generalization of `gcongr`**. It is
attribute-driven (`@[hgcongr]`) and keyed on a *pair* of heads, so it relates
*different* head functions `f ≠ g`, a case `gcongr` rejects by construction.
`HGCongr.lean` carries the upstream `Mathlib.Tactic.GCongr.Core` patch that would
add this to `gcongr`.

## Plugging into Lean

The library reuses native Lean machinery. Transfer is only as sound as the
*registered* witnesses, so a missing witness remains a **visible residual goal**.
For the same reason the `aesop` rule set is opt-in: it never searches for a square
on its own.

| Mechanism | Role |
|---|---|
| **type classes** | the synthesis engine (`HasParam`/`Related` resolution) |
| **`grind`** | the equational congruence-closure backend for `param_cc` (foundation squares dual-tagged `@[grind =]`) |
| **`gcongr`** | homogeneous congruence; `hgcongr` is its cross-head generalization |
| **`simp` / `norm_cast`** | the closed-equation fast path; a `@[norm_cast]` move-lemma *is* a transfer witness over the cast graph (`ParamNormCast`) |
| **`conv`** | focused sub-term transfer (`transferConv`) |
| **`aesop`** | an opt-in `Transfer` rule set bundling the transfer rules |
| **`Std.Do` / `mvcgen`** | Hoare-triple transfer via the Kleisli relation `RComp` (`ParamTripleTransfer`); `rcomp` (folded into `param_transfer`) assembles the witness |
| **coercions** | a `Coe`/`CoeTC` derived from a forward map (`ParamCoe`) |

`RComp Rα c c'` is the Kleisli lift of a value relation `Rα` to monadic
computations: for every pair of postconditions related pointwise by `Rα`, the
weakest precondition of `c` entails that of `c'`. `RCompOk` is its
success-restricted variant: each value that `c` returns without an exception has
an `Rα`-related partner among the results of `c'` (`ParamRCompOk`, tactic
`rcomp_ok`). Both are instances of `Param`, and both compose (`ParamRCompParam`).

## Quick start

A file that uses the library starts with

```lean
import Transfer
open Transfer Transfer.Param Transfer.ExampleField
```

and can then register witnesses, transfer statements, derive relations, and close
goals by congruence:

```lean
-- register a witness
def double (n : ℕ) : ℕ := 2 * n
@[param] theorem doubleR : RArrow Eq Eq double double := fun _ _ h => congrArg double h

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
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_solve
```

Full per-tactic / per-attribute reference: [`TACTICS.md`](TACTICS.md).

## File map (reference)

The source under `Transfer/` is organized into concept subdirectories. The root
`Transfer.lean` is the single entry point.

**`Base/`** — the `Related`/`RelatedBinOp` substrate and the class-hierarchy,
level and tactic substrate the engine reuses.

| Module | Content |
|---|---|
| `Core` | the `repr` registry and the `repr_transfer` tactic |
| `FieldRegistry` | the Baby Bear field kernels as registered operations |
| `Hierarchy` | the relation hierarchy as classes |
| `HigherOrderTransfer` | binder / higher-order / `∀` transfer as lemmas |
| `LevelRefusal` | the univalence-free refusal guard |
| `Levels` | relatedness levels: the three-point view of the Trocq lattice |
| `Related` | `Related`: transfer by instance resolution |
| `RelatedAt` | level-annotated relatedness |
| `TransferInduction` | transported induction, the equiv-level combinator |
| `TransferLevel` | the level-aware `transfer!` elaborator |
| `TransferTactic` | the `transfer` tactic (automatic binder translation) |
| `UnivalenceStatus` | univalence in Lean 4 and the Trocq `map4` cap |

**`Hierarchy/`**

| Module | Content |
|---|---|
| `ParamEquiv` | the equivalence bridge and `Param` weakening |
| `ParamHierarchy` | the `Param` relation hierarchy |
| `ParamLevel` | the level lattice and the minimal-`(m,n)` solver core |
| `ParamWeaken` | the `⊑`-driven `Param` weakening (level navigation) |

**`Combinators/`**

| Module | Content |
|---|---|
| `ParamArray` | the `Array` container rule and relational `foldl` transfer |
| `ParamArrow` | the arrow (`app` / function) parametricity rule |
| `ParamCoherence` | the coherence-law suite (functor laws) |
| `ParamData` | the data-type (`×` / `Option` / `List`) parametricity rules |
| `ParamForall` | the dependent-Π (`∀`) parametricity rule |
| `ParamSigma` | the dependent-pair (`Σ`) parametricity rule |
| `ParamTrans` | relation composition (`Param_trans`) |

**`Synthesis/`**

| Module | Content |
|---|---|
| `ParamInfer` | variable-level minimal-class inference |
| `ParamInferMeta` | level inference over `Expr` |
| `ParamResolve` | the upward level search (`param_resolve`) |
| `ParamSynth` | the `Param`-witness synthesizer |
| `ParamSynthExt` | the multi-level `Param`-witness synthesizer |

**`Translate/`**

| Module | Content |
|---|---|
| `ParamDB` | the persistent `@[param]` constant database |
| `ParamTranslate` | the term-level `⟦·⟧` synthesizer (the parametricity translation) |
| `ParamTranslateFull` | the integrated term-level translator `⟦·⟧` |
| `ParamTranslateOp` | the operator/arity rule for the term-level translator |
| `ParamTranslateTy` | the binder type-translation rule (change of representation) |

**`Statements/`**

| Module | Content |
|---|---|
| `ParamForallNested` | dependent-Π transfer for nested `∀`-statements |
| `ParamTransfer` | `∀`-transfer through the `Param` engine (`Map1_forall`) |
| `ParamTransferTac` | `param_transfer`, end-to-end `∀`-transfer |

**`Congruence/`**

| Module | Content |
|---|---|
| `GCongrProbe` | whether `@[gcongr]` accepts cross-head realization lemmas |
| `HCongrConnection` | a set-level analogue of cubical heterogeneous congruence (`hcongr`) |
| `HGCongr` | `hgcongr`: heterogeneous (cross-head) generalized congruence |
| `HGCongrInit` | the `hgcongr` engine: head-pair-keyed database, attribute, and tactic |
| `ParamAuto` | `param_auto`: one coordinator over every congruence surface |
| `ParamCompose` | `param_compose`: descend-and-dispatch congruence |
| `ParamCongrClosure` | `param_cc`: relational congruence closure over `Related` |
| `ParamSolve` | `param_solve`: the common generalization of `rcongr` and `param_cc` |
| `RCongr` | `rcongr`: relational (cross-head) congruence descent |

**`Deriving/`**

| Module | Content |
|---|---|
| `ParamCongr` | `derive_param_congr`: a constructor-congruence `Related` deriver |
| `ParamDerive` | hand-ported `Param` lifts and the specification of the `@[derive Param]` handler |
| `ParamDeriveHandler` | the description-based `@[derive Param]` handler |

**`Integrations/`**

| Module | Content |
|---|---|
| `AesopIntegration` | the `Transfer` aesop rule set |
| `AesopRuleSet` | the declaration module of the `Transfer` aesop rule set |
| `GrindIntegration` | `grind` as a transfer leaf discharger |
| `ParamAutoWeaken` | auto-weakening of witnesses and a unified transfer entry |
| `ParamCoe` | the coercion integration (`Param` witness → `Coe`) |
| `ParamConv` | `conv`-mode transfer |
| `ParamForIn` | `forIn` / `do`-loop transfer: `foldlR` meets `RComp` |
| `ParamNormCast` | `norm_cast` move-lemmas as `Param` relatedness witnesses |
| `ParamRComp` | `rcomp`: structural assembly of an `RComp` witness |
| `ParamRCompOk` | `RCompOk`: the success-restricted Kleisli relation |
| `ParamRCompParam` | `RComp`/`RCompOk` as instances of `Param`, and their composition |
| `ParamRelatedBridge` | one witness, both engines: `RelatedBinOp` ⇒ `RArrow` |
| `ParamTripleTransfer` | transferring a Hoare/`wp` triple through a `Param` relation; defines the Kleisli relation `RComp` |

**`Examples/`**

| Module | Content |
|---|---|
| `EffectfulTransfer` | an effectful transfer across a value-type change, proved by `mvcgen` |
| `ExampleField` | a self-contained example field for the engine demos |
| `IsogenyBoundedProbe` | BLS12-381 hash-to-curve isogeny identity: bounded per-coefficient probe |
| `MachineLimbField` | machine limbs ↔ prime field: a non-diagonal heterogeneous dependent example |
| `ParamCryptoDomains` | the Baby Bear field as a first-class transfer domain |
| `ParamCryptoExamples` | cryptographic representation examples: coherence laws and `deriving Param` |
| `ParamRetraction` | the `ℤ ↠ ZMod p` retraction transfer domain (non-diagonal) |
| `PeanoBinNat` | the `peano_bin_nat` example, first-order slice |
| `RCompOkExamples` | `RCompOk` over a two-outcome test monad |
| `Readme` | the examples of this README |
| `StrongExamples` | congruence that the native tactics cannot do |
| `Trocq` | the Trocq example suite (index) |
| `Trocq/Summable` | Trocq `summable`: summability transfers across an equivalence |

*Hex suite*: worked refinements on the carriers of `leanprover/hex`.

| Module | Content |
|---|---|
| `HexArrayCompute` | `hex`'s `Array`-backed storage: carrier-agnostic refinement and verified compute |
| `HexDecide` | discharging a `hex` side condition by computation on the concrete representation |
| `HexEffectful` | transferring a `hex` elimination step across dense storage, effectfully |
| `HexMatrixCorrespondence` | `hex`-style dense-storage ↔ Mathlib correspondence, generated by the engine |
| `HexSeqPoly` | `hex`'s dense polynomial storage: a non-injective refinement at `map2a` |

*ZMod suite*: deciding modular identities by bounded computation.

| Module | Content |
|---|---|
| `ZModDecide` | `decide_zmod`: ground ring identities over `ZMod m` by bounded residue computation |
| `ZModPolyDecide` | `decide_zmod_poly`: univariate polynomial identities over `ZMod m` |
| `ZModPowMod` | `powMod`: binary modular exponentiation for kernel-`decide` modular arithmetic |

*CoqEAL suite*: the library `TransferCoqEAL`, rooted at `Transfer.Examples.CoqEAL`,
which depends on CompPoly.

| Module | Content |
|---|---|
| `CoqEAL` | the CoqEAL / Trocq example suite (index) |
| `CoqEAL/BareissDet` | CoqEAL `bareiss`: a fraction-free determinant certified against `Matrix.det` |
| `CoqEAL/BinInt` | CoqEAL `binint`: sign + magnitude refines `ℤ` |
| `CoqEAL/BinNat` | CoqEAL `binnat`: `List Bool` refines the natural numbers |
| `CoqEAL/BinRat` | CoqEAL `rational`/`binrat`: num/den pairs refine `ℚ` |
| `CoqEAL/ComputePolynomial` | computing with Mathlib's `Polynomial` through a CompPoly refinement |
| `CoqEAL/GaussPivotStep` | Gaussian elimination: single forward-elimination pivot step |
| `CoqEAL/GaussSweep` | Gaussian elimination: multi-row forward sweep |
| `CoqEAL/Karatsuba` | CoqEAL Karatsuba polynomial multiplication |
| `CoqEAL/KaratsubaRec` | recursive Karatsuba on `CPolynomial R` |
| `CoqEAL/Multipoly` | CoqEAL `multipoly`: multivariate polynomials as finite maps |
| `CoqEAL/Rank` | CoqEAL `rank`: matrix rank certified against `Matrix.rank` |
| `CoqEAL/SeqMatrix` | CoqEAL `seqmatrix`: `List (List R)` refines the entry function |
| `CoqEAL/SeqMatrixMul` | CoqEAL `seqmatrix` multiplication: `List (List R)` row-column product |
| `CoqEAL/SeqPoly` | CoqEAL `seqpoly`: `List R` refines the coefficient function |
| `CoqEAL/Strassen` | Strassen one-level 2×2 block multiplication identity |
| `CoqEAL/StrassenRec` | recursive (fuel-driven) Strassen block multiplication |
| `CoqEAL/ToomCook` | CoqEAL `toomcook`: the evaluate–multiply–interpolate core |

**Top-level modules and libraries**

| Module | Content |
|---|---|
| `Transfer` | the single entry point |
| `Transfer/Audit` | axiom ledger: a build-time hygiene check (`lake build Transfer.Audit`) |
| `ReprTransfer` (library) | representation transfer for emit-realization bridges |
| `ReprTransferExpr` (library) | compositional transfer via the abstraction theorem |

## Provenance

The library builds on the work credited in [`ATTRIBUTION.md`](ATTRIBUTION.md):
**Trocq** (Cohen–Crance–Mahboubi), whose parametricity lattice and combinators the
engine's core adapts; **AdapTT** (functorial casts and description-based
deriving); **CoqEAL** (data refinement); the **cubical congruence** of
Gjørup–Spitters; and **Lean 4 / Mathlib**.
