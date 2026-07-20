/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: ParamTransfer Contributors
-/
import VersoManual

open Verso.Genre Manual

#doc (Manual) "ParamTransfer — reasoning up to a registered relation" =>

ParamTransfer is a Lean 4 + Mathlib framework for reasoning up to a registered
relation. A single declaration states how an abstract value relates to a concrete
representation of it; the framework then synthesizes witnesses of that relation,
transfers statements and terms across it, and decides it structurally by
congruence — emitting kernel-checked proof terms throughout.

The design synthesizes several lines of work: modular parametricity (Trocq's
lattice and combinators — the largest single influence), relational transfer and
data refinement ([CoqEAL](https://github.com/coq-community/coqeal)), set-level
heterogeneous congruence from cubical type
theory (Gjørup–Spitters), and congruence-closure algorithms. From that synthesis
comes one auto tactic that unifies the native Lean relational tactics —
`congr`/`gcongr`, `norm_cast`, cast-`rw`, `conv`, `aesop`/`grind` — behind a
single inference rule. Two application domains drive the framework: compiler
verification (the CatCrypt compiler) and program verification (`mvcgen` / `Std.Do`
triples and [hax](https://github.com/cryspen/hax)-extracted code).

Single entry point: `import Transfer`. Released under LGPL-3.0.

🚧 *Under construction.* This manual is being expanded — some sections are still
growing, and details may change. Feedback is welcome.

Each code block below transcribes a library declaration and names its source file,
where the compiler-checked original lives.

# Part I — The idea

## Overview

The framework operates on a single object: a relation `R` between a value and a
representation of it — `Related enc a b` (the encoding view, `enc a = b`) or,
graded, `Param (m n) A B` (relation plus maps). The relation `R` is registered once,
through attributes and instances (`@[param]`, `@[transfer]`, `RelatedBinOp`
instances, `deriving Param`); every tactic and translator in this manual reads that
registration. Setup and build instructions live in the repository's `BUILDING.md`.

The smallest transfer decides that two structurally similar terms are related,
where `bbFieldMul` / `bbFieldAdd` are registered as realizing `*` / `+`:

```
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_solve
```

That is the whole loop in miniature: a registered relation, and one tactic that
closes the goal by congruence over it.

## Three operations from one registration

Registering `R` once gives three operations on the _same_ object. Build a witness,
transfer a statement across it, or decide it structurally — each is one instance of
a single inference step.

*Build `R a b` — synthesis.* Find or compose a witness by type-class resolution:
`Related` / `HasParam` instance search composes registered witnesses through the
structure of a term (the analogue of Trocq's Elpi search).

```
example (a b c : F) :
    Related (id : F → F) (a * b + c) (bbFieldAdd (bbFieldMul a b) c) := by param_solve
```

*Transfer a goal along `R` — parametricity.* Move a `∀`-statement to the other
representation with `param_transfer`, or emit a term's `⟦·⟧` translation with
`#transfer`.

```
-- ℤ ↠ ZMod p: an integer fact transfers to its modular image.
example (p : ℕ) [NeZero p] :
    (∀ i : ℤ, (Int.cast i : ZMod p) + 0 = (Int.cast i : ZMod p)) →
      (∀ x : ZMod p, x + 0 = x) := by
  param_transfer
  intro i x (hix : (Int.cast i : ZMod p) = x) h
  rw [← hix]; exact h

#transfer (fun x : Nat => Nat.succ x * x)
```

*Decide `R a b` structurally — congruence.* Relate two structurally similar
terms by relational congruence closure.

```
example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by param_cc
```

All three run on one inference rule — related arguments give related applications,
from `R aᵢ bᵢ` infer `R (f a…) (g b…)` (`R_arrow` / `R_forall`). The next section
unpacks that rule and the tactic that dispatches to it.

## The unifying auto tactic

Each native Lean relational tactic is congruence for one _fixed_ relation. The
framework generalizes that rule to a registered relation and exposes one call site.

:::table +header
*
  * native tactic
  * its fixed relation
  * what the one rule adds
*
  * `congr` / `HEq`
  * `Eq` / `HEq`
  * relates values in _different_ fiber types
*
  * `gcongr`
  * `≤` / `⊆`, same head
  * changes representation across a cross-head op-tree
*
  * `norm_cast`
  * the scalar cast graph
  * transports a _dependent family_ of casts
*
  * cast-`rw`
  * a single coercion lemma
  * any registered `Param` witness
*
  * `conv`
  * focused rewriting
  * focused sub-term _transfer_ (`transferConv`)
*
  * `aesop` / `grind`
  * `Eq` congruence closure
  * closure over a registered `R` (`param_cc`)
:::

`param_auto` (`Congruence/ParamAuto.lean`) is the coordinator: a stable call site
that dispatches to all of these surfaces — the engine tactics (`param_solve`,
`rcongr`) and the native ones (`norm_cast`, `gcongr`, `grind`). The dispatch
strategy underneath — currently a `first`-cascade, later a goal-directed router —
can change without touching any call site. `param_compose` (`ParamCompose.lean`) is
the composer for goals needing _two_ extensions at once: it descends a `Related`
op-tree with the cross-head rule `rcongrBinOp` and closes each residual leaf with
the full native cascade (`param_leaf`), the niche where neither a native tactic nor
the engine alone suffices.

Each example in `Examples/StrongExamples.lean` beats a specific native tactic on an
axis that tactic structurally cannot cross. Over the genuinely
non-diagonal encoding `Nat.cast : ℕ → ℤ`, `rcongr` descends the cross-head op-tree
_and_ changes representation (`natCastAdd` / `natCastMul` register the two commuting
squares; `transferRel` extracts the equation `↑(a*b+c) = ↑a*↑b+↑c`) — a move
`gcongr` rejects. Across `Fin (a+1) ↔ ℕ`, the heterogeneous rule relates values in
different fiber types where `congr` forces the types equal. And a dependent family
of casts `Fin (n+1) → ℕ` transports uniformly across `∀ n, …` where `norm_cast`
moves only a fixed scalar coercion.

# Part II — The engine

## The graded relation

`Param (m n) A B` is a relation `R : A → B → Prop` carrying a chosen amount of
structure in each direction, fixed by the pair of levels `(m, n)` — `m` grades the
forward direction (`A → B`), `n` the backward (`B → A`). Each level is drawn from a
six-point lattice `map0 ≤ … ≤ map4`:

* `map0` — a bare relation, no map;
* `map1` — a map in that direction;
* `map2a` / `map2b` — a map whose graph is contained in `R`, respectively contains
  `R` (the two are incomparable);
* `map3` — a map whose graph _is_ `R` (both inclusions);
* `map4` — `map3` with an added coherence on top.

So `(map0, map0)` relates values sharing no maps; a forward cast `A → B` is
`m = map1`. A backward decoder whose graph is contained in the relation — a
retraction such as `ℤ ↠ ZMod p` — is `n = map2a`: the engine ships it as
`intZModParam : Param .map3 .map2a ℤ (ZMod p)`. A left-inverse encoding reaches
`n = map2b`, and a two-sided equivalence reaches `(map3, map3)`. A transfer needs
only as much structure as the goal touches: register `R` at the provable `(m, n)`,
and the level solver (`ParamInfer`) picks the minimum a goal needs,
weakening down the lattice (`ParamWeaken`, `auto_weaken`).

## Combinators and the congruence layer

The `R_arrow` / `R_forall` combinators carry `R` through `→` and `Π`; their
coherence (`ParamCoherence`) makes composition well-behaved, and the container
rules `ParamData` (`×` / `Option` / `List`) and `ParamArray` (`Array`) extend `R`
structurally. On top of them sit four congruence tactics — one relation, two
strategies plus their union:

* `rcongr` / `hgcongr` — top-down descent through a registered cross-head op-tree,
  leaving per-argument relatedness subgoals;
* `param_cc` — bottom-up closure (via `grind`): transitivity and context-hypothesis
  chains;
* `param_solve` — descent with the closure as the leaf discharger, the union of the
  above, and the default.

`hgcongr` is the heterogeneous generalization of `gcongr`: an attribute-driven
(`@[hgcongr]`), head-pair-keyed congruence relating different head functions
`f ≠ g`. It carries the exact upstream `Mathlib.Tactic.GCongr.Core` patch that
would lift this.

## Composition and derivation

What makes transfer compositional and extensible:

* `R` composes — `Param_trans` glues `A↔B` and `B↔C` into `A↔C`.
* casts compose and preserve identity — `cast_trans` (AdapTT's `AdaptComp`:
  `cast (R∘S) = cast S ∘ cast R`) and `cast_id`; the combinators
  distribute over composition (`ParamCoherence`).
* inductive `R` is derived — `deriving Param` reads an inductive's constructor
  signature (AdapTT's `IndDesc`), generates its constructor-wise relation and a
  full `Param` instance, and rejects mixed-variance inductives. It covers records,
  enums, uniform-recursive (`List` / `Tree`-shape) types, and `List`-nested
  recursion (`Rose`-shape — a recursive occurrence under `List`).

```
inductive Pair (A B : Type) | mk : A → B → Pair A B
  deriving Param

inductive RoseT (A : Type) | node : A → List (RoseT A) → RoseT A
  deriving Param
```

## Integration with native machinery

The framework cooperates with native machinery and reuses it. Transfer is only as
sound as the registered witnesses, so a missing witness stays a visible residual
goal.

* type classes — the synthesis engine (`Related` / `HasParam` resolution);
* `grind` — the equational congruence-closure backend for `param_cc`;
* `gcongr` — homogeneous congruence; `hgcongr` is its cross-head generalization;
* `simp` / `norm_cast` — the closed-equation fast path; a `@[norm_cast]` move-lemma
  is a transfer witness over the cast graph (`ParamNormCast`);
* `conv` — focused sub-term transfer (`transferConv`);
* `aesop` — an opt-in `Transfer` rule set bundling the transfer rules;
* `Std.Do` / `mvcgen` — Hoare-triple transfer via the Kleisli relation `RComp`
  (`ParamTripleTransfer`).

# Part III — Applications

## Compiler verification

The lead application relates emitted low-level code to a clean algebraic
specification. The principal example is `Transfer/Examples/MachineLimbField.lean`:
the machine-limb view of a prime-field element and its abstract `ZMod p` view,
exercised at full strength. The domain is non-diagonal (`BitVec 64` /
`Fin n → BitVec 64` on the left, `ZMod p` on the right), heterogeneous (the value
leaf relates terms in different types via a decoder), and dependent (the multi-limb
section is the `R_forall` dependent-Π relation over the `Fin n`-indexed limb
family).

The single-limb split surjection `BitVec 64 ↠ ZMod p` is a retraction
`Param .map0 .map2a`:

```
def limbFieldParam (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64) :
    Param .map0 .map2a (BitVec 64) (ZMod p) where
  R   := fun w x => ((w.toNat : ZMod p) = x)  -- the decoder's graph
  fwd := ⟨⟩                                   -- map0: no forward map
  bwd := ⟨fun x => BitVec.ofNat 64 x.val, …⟩  -- map2a: section + retraction proof (elided)
```

Forward is the trivial `map0` (the relation is the decoder's graph). Backward is
`map2a`: the section `x ↦ BitVec.ofNat 64 x.val` satisfies the retraction law but
not injectivity, so the class stays asymmetric — an equivalence-based transfer
would reject this refinement. Under a no-overflow guard the word operations commute
with the field operations across the decoder (`dec_add`, `dec_mul`): the decoder is
a partial, overflow-guarded ring homomorphism. `instTransferDomLimbField` wires the
change of representation into `param_transfer`.

The multi-limb case lifts this to a limb array `Fin n → BitVec 64` read as its
base-`2^64` value (Curve25519 `n = 4`, P-384 `n = 6`):

```
def multiLimbFieldParam (n p : ℕ) [NeZero p] (hp : p ≤ 2 ^ (64 * n)) :
    Param .map0 .map2a (Fin n → BitVec 64) (ZMod p) where
  R := fun limbs x => ((limbVal n limbs : ZMod p) = x)
  fwd := ⟨⟩
  bwd := ⟨fun x => toLimbs n x.val, …⟩
```

Its crux is the recomposition law `limbVal_toLimbs`: splitting an in-range value
into base-`2^64` digits and Horner-recomposing recovers it. A store refinement
(`LimbStoreRefines` / `MultiLimbStoreRefines`) is then `R_forall` over the decoder
fiber, and reading any variable is `hcongr_hetero` — the value-abstraction layer of
a verified compiler's store refinement.

The underlying compute layer is `ReprTransfer`: a protocol-agnostic
proof-transfer layer for the recurring pattern where a proof quantifies over an
abstract (often `noncomputable`) operation while the emitted artifact computes a
byte-level one and an encoding ties them. It factors out the shared content — the
relation structure and one generic transfer theorem — that hand-written CatCrypt
bridges (KZG's byte↔group pairing, the ML-KEM / ML-DSA / STARK emit-realization
ties) each re-derived. It identifies the minimal level for transferring a decidable
equation: the domains need only a map, the codomain an embedding (an injective
encoding) — no equivalence, no univalence.

## Program verification

The second application transfers program correctness across a change of
representation. The `Transfer/Examples/HexEffectful.lean` example transfers a Hoare triple: a
Bareiss-style elimination step written as a `do`-block moves its triple across a
storage change via the Kleisli relation `RComp` and `triple_transfer`
(`Integrations/ParamTripleTransfer`). The concrete step's triple is proved by
`mvcgen`; the abstract step's triple is not re-proved but _derived_ from it by
`triple_transfer`, which carries the correctness across the storage change along an
`RComp` witness (assembled leaf-by-leaf from `RComp.pure` / `RComp.bind`, mirroring
the do-block):

```
theorem hexStep_spec (l : List ℤ) :
    ⦃⌜True⌝⦄ (hexStep l) ⦃⇓r => ⌜r = l.getD 0 0 - l.getD 1 0⌝⦄ := by
  mvcgen [hexStep]

theorem absStep_spec {n : ℕ} (l : List ℤ) (v : Fin (n + 2) → ℤ)
    (h0 : l.getD 0 0 = v 0) (h1 : l.getD 1 0 = v 1) :
    ⦃⌜True⌝⦄ (absStep v) ⦃⇓r => ⌜r = v 0 - v 1⌝⦄ := by
  refine triple_transfer (Rα := fun a a' => a = a') (hexStep_RComp l v h0 h1)
    ?_ (hexStep_spec l)
  intro a a' (haa : a = a') hc
  subst haa; rw [← h0, ← h1]; exact hc
```

The `do` / `for` loops ride `RComp.forIn_list` (effects plus early
exit), so a loop-shaped program transfers through one combinator lemma rather than
an inline recursion translation. This is the mechanism for reasoning about
hax-extracted code up to its representation: the extracted `Std.Do` program and its
abstract spec are related at value equality, and the triple transfers.

## Data refinement

The third application is CoqEAL-style data refinement: a computational
representation of a proof-oriented Mathlib object, related by a refinement across
which statements, terms, and computations transfer.

The [`leanprover/hex`](https://github.com/leanprover/hex) retrofit models `hex`'s
verified computational-algebra carriers and drives them through the engine, one file
per axis. Dense storage
(`List ℤ` / `List (List ℤ)`) refines a Mathlib vector / matrix as a
`Param .map0 .map2a`, and `param_transfer` _generates_ the correspondence rather
than hand-proving it per operation (`HexMatrixCorrespondence`). The seq-polynomial
refinement is non-injective — trailing zeros mean `[1,2]` and `[1,2,0]` both denote
`2X+1` — reaching `map2a` but provably not `map2b`, a refinement the graded engine
accepts (`HexSeqPoly`). A modular side condition is discharged by computing on the
concrete representation through `ReprTransfer`'s embedding `ZMod m ↪ ℤ`
(`HexDecide`), and `Array ℤ` gets a `@[csimp]` verified-compute swap so a spec-level
fold runs as an `Array` fold carrying its proof (`HexArrayCompute`).

The `Transfer/Examples/CoqEAL/` suite is a separate library (`TransferCoqEAL`), so
its dependency on [CompPoly](https://github.com/Verified-zkEVM/CompPoly) stays out
of the core graph. It ports the effective-algebra refinements — `SeqPoly`,
`SeqMatrix`, `Strassen`, `Karatsuba`, `Gauss*`, `Bareiss` (`BareissDet`), `Rank`,
`ToomCook`, `Multipoly`, and the `BinNat` / `BinInt` / `BinRat` number refinements
— and, in `ComputePolynomial`, computes with Mathlib's `Polynomial` through
CompPoly's `RingEquiv` (the CoqEAL / Kaliszyk–O'Connor "refinements for free" move).

# Part IV — Reference

## Tactic reference

Each tactic reads the registered relation; they differ in direction and discharger.

* `param_solve` — the default. Congruence descent with the closure as leaf
  discharger (the union of `rcongr` and `param_cc`). Try it first.
* `param_auto` — the coordinator: one call site dispatching to every congruence
  surface (engine and native).
* `param_compose` — descend-and-dispatch: descends a `Related` op-tree and closes
  each leaf with the native cascade.
* `param_cc` — bottom-up relational congruence closure via `grind`. Best when the
  proof must _chain_ known relatednesses.
* `rcongr` — top-down descent through the registered cross-head op-tree; leaf
  discharger `inferInstance | rfl`.
* `hgcongr` — heterogeneous, attribute-driven (`@[hgcongr]`) congruence relating
  different head functions `f ≠ g`.
* `param_transfer` — transfer a `∀`-goal along the relation (the abstraction
  theorem), leaving per-argument relatedness hypotheses.
* `transfer` — the term-level elaborator entry point.
* `#transfer t` — print the translation of a term `t` in the other representation.
* `auto_weaken` — weaken a `Param (m n)` witness down the lattice (drives
  `ParamWeaken`).
* `synth_param` — run the `HasParam` synthesis engine to build a witness.
* `transfer_induction` / `transfer_auto` — induction- and automation-flavored
  drivers for transfer goals.

## Registration

Transfer only knows what is registered; the following attributes and instances
extend it.

* `@[param]` — register a constant as transferable. Its presence lifts the
  constant's leaf to at least `map1` in level inference (`getParamDB`).
* `@[transfer]` — register a translation witness for the term translator.
* `RelatedBinOp` instances — register a binary operation as realizing an abstract
  one (`*` ↦ `bbFieldMul`, `+` ↦ `bbFieldAdd`).
* `@[hgcongr]` — register a head-pair congruence lemma so `hgcongr` can relate two
  specific head functions.
* `deriving Param` (or `deriving instance Param for T`) — generate, for an
  inductive `T`, its relational lift `R_<T>` and a full `Param .map3 .map0`
  instance. Covers records, enums, uniform-recursive types, and `List`-nested
  recursion.

An unregistered constant does not silently transfer — it stays a visible residual
goal.

### A minimal single-relation registration (pedagogical)

The smallest registration teaches the shape, not a real change of representation.
`Transfer/Examples/ExampleField.lean` sets `F = ZMod p` for the Baby Bear prime and
registers two same-type operations that stand in for abstract `*` and `+`:

```
def bbFieldMul (a b : F) : F := a * b
def bbFieldAdd (a b : F) : F := a + b
```

These are `RelatedBinOp` witnesses (`bbFieldMul_eq` / `bbFieldAdd_eq` are the
commuting squares). With them in scope, `param_solve`, `param_cc`, and synthesis all
read the same relation on the same objects. This is a same-type op-renaming
demo — the encoding is the identity — so it shows registration mechanics, not a
cross-type encoding. For a cross-type encoding, see `MachineLimbField` (Part III).

## Cookbook

* A new binary operation realizing an abstract one. Add a `RelatedBinOp`
  instance; `param_solve` then descends through it.
* A new inductive type. Put `deriving Param` on it to obtain the relation
  and a usable forward map (`castViaParam`).
* A witness stronger than the goal needs. Let level inference pick the minimum, or
  `auto_weaken` an over-strong `Param` down the lattice.
* Transferring a `∀` over a non-diagonal domain (`ℤ ↠ ZMod p`). Provide a
  `Param` at `(map3, map2a)` (or weaker) and a `TransferDom`; use `forallTransfer`
  / `param_transfer`.
* Transferring a Hoare triple. Use the Kleisli relation `RComp`
  (`ParamTripleTransfer`) with `Std.Do` / `mvcgen`.
* Rewriting a single sub-term. Use `transferConv` inside a `conv` block.

## Module map

The library is organized by role; `import Transfer` pulls in all of it.

* `Transfer/Base/` — `Core`, `Related`, `RelatedAt`, the field registry. The
  relation encoding and registry substrate.
* `Transfer/Hierarchy/` — `MapClass`, the `Param (m n)` structure, `ParamEquiv`,
  `ParamWeaken`, `ParamLevel`. The graded relation and its lattice.
* `Transfer/Combinators/` — the `R_arrow` / `R_forall` combinators and their
  coherence (`ParamCoherence`); the container rules `ParamData` (`×` / `Option` /
  `List`) and `ParamArray` (`Array`, with the relational `foldl` transfer).
* `Transfer/Synthesis/` — `ParamInfer` (level inference, including the full-`Expr`
  front-end), `ParamResolve`, `ParamSynth`. The witness-building engine.
* `Transfer/Translate/` — the term translator (`translateAll` in
  `ParamTranslateFull`, operator spine in `ParamTranslateOp`), `#transfer`.
* `Transfer/Statements/` — `TransferDom`, `forallTransfer`, the `∀`-rule.
* `Transfer/Congruence/` — `ParamSolve`, `ParamCongrClosure`, `ParamAuto`,
  `ParamCompose`, `rcongr` / `hgcongr`.
* `Transfer/Deriving/` — `ParamDeriveHandler` (the `deriving Param` handler) and
  `ParamDerive`.
* `Transfer/Integrations/` — `ParamNormCast`, `ParamTripleTransfer`, `ParamForIn`
  (the `forIn` / `do`-loop transfer), the `aesop` rule set, and the other
  native-machinery bridges.
* `Transfer/Examples/` — `ExampleField`, `MachineLimbField`, `ParamRetraction`,
  `StrongExamples`, `ParamCryptoDomains`, `ParamCryptoExamples`, the `Hex*` modules
  targeting `leanprover/hex`, and the `PeanoBinNat` example.
* [`Transfer/Examples/CoqEAL/`](api/Transfer/Examples/CoqEAL.html) — the CoqEAL
  example suite, a separate library `TransferCoqEAL`, kept off the core graph.
* [`Transfer/Examples/Trocq/`](api/Transfer/Examples/Trocq.html) — the Trocq example
  suite (`PeanoBinNat`, `ExampleField`, `ParamRetraction`, `Summable`), needing only
  Mathlib.

The sibling layers `ReprTransfer` and `ReprTransferExpr` sit at the package root.
For per-declaration signatures and docstrings, the doc-gen4
[API reference](api/index.html) (built from the `docbuild/` package) deploys
alongside this manual under `api/`.

## Coverage

The engine walks terms, not only type spines:

* level inference has a full-`Expr` front-end (`exprToTyShape` /
  `inferParamLevelsExpr`): it walks an actual Lean type — distinguishing
  non-dependent `→` from dependent `Π`, reading const/app heads as leaves whose
  lower bound comes from the `@[param]` registry — and solves the minimal class per
  node by constraint propagation. Universe-polymorphic declarations are walked too;
* the term translator handles the operator spine, registry constants, application,
  and the type-translating `λ` (`translateAll`); an unregistered constant surfaces
  as a residual goal;
* `deriving Param` generates the full instance for non-recursive inductives, uniform
  recursion, and `List`-nested recursion (`Rose`-shape, with the forward map
  recursing through `List.map` and both graph inclusions proved by mutual structural
  recursion);
* `TransferDom` covers diagonal domains and retractions (`ℤ ↠ ZMod p`);
* the `Array` container is a first-class rule (`ParamArray`) and the relational
  `foldl` transfer `foldlR_list` / `foldlR_array`, together with the `forIn` /
  `do`-loop transfer (`RComp.forIn_list`), let a fold- or loop-shaped program
  transfer through one combinator lemma.

## Glossary

* `Param (m n) A B` — a relation `R : A → B → Prop` graded by a pair of levels, one
  per direction (forward `A → B`, backward `B → A`).
* `MapClass` — the six-point lattice `map0 ≤ … ≤ map4` a single direction's
  structure is drawn from.
* `Related enc a b` — the encoding view of the relation: `enc a = b`.
* `R_arrow` / `R_forall` — the functoriality rule: related arguments give related
  applications; the shared inference step of all three uses.
* retraction — a representation with a backward decoder whose graph is contained in
  the relation (`map2a`), e.g. `ℤ ↠ ZMod p`; weaker than an equivalence.
* `TransferDom` — the instance supplying the domain `Param` the `∀`-rule needs.
* `castViaParam` — the forward map extracted from a `Param` witness, the
  computational content of a transfer.

## Provenance

The framework synthesizes several lines of work:

* [Trocq](https://arxiv.org/abs/2310.14022) (Cohen–Crance–Mahboubi, ESOP 2024 /
  TOPLAS 2025) — the largest single influence: the parametricity lattice and
  combinators the engine's core adapts.
* [CoqEAL](https://github.com/coq-community/coqeal) — relational transfer and data
  refinement.
* the [cubical congruence of Gjørup–Spitters](https://users-cs.au.dk/spitters/Emil.pdf)
  (_Congruence Closure in Cubical Type Theory_, 2020) — the set-level form of
  heterogeneous congruence.
* [AdapTT](https://arxiv.org/abs/2507.13774) — functorial casts and
  description-based deriving.
* congruence-closure algorithms — the closure backend behind `param_cc`.

Built on [Lean 4](https://lean-lang.org) and
[Mathlib](https://github.com/leanprover-community/mathlib4).
