# Attribution

The `ParamTransfer` library provides proof transfer by modular parametricity in
Lean 4, drawing on the work below. It is released under **LGPL-3.0** (see `LICENSE`):
its parametricity core adapts the design of Trocq's LGPL-3.0 `std` development, so
it carries the same license. The attributions here record intellectual
provenance.

## Parametricity core — Trocq

The engine's parametricity layer adapts the design of the `std` (standard-library,
non-HoTT) variant of **Trocq**:

- Cyril Cohen, Enzo Crance, Assia Mahboubi.
  *Trocq: Proof Transfer for Free, With or Without Univalence.*
  ESOP 2024. [arXiv:2310.14022](https://arxiv.org/abs/2310.14022).
- Cyril Cohen, Enzo Crance, Assia Mahboubi.
  *Trocq: Proof Transfer for Free, Beyond Equivalence and Univalence.*
  ACM TOPLAS, 2025. [doi:10.1145/3737283](https://doi.org/10.1145/3737283).
- Implementation: [`rocq-community/trocq`](https://github.com/rocq-community/trocq).

The map-class hierarchy (`map0`–`map4`), the `(m,n)` annotation lattice, the
weakening calculus, the `R_arrow`/`R_forall` combinators, the `@[param]` registry
and the term-level translation `⟦·⟧` follow Trocq's design. Where Trocq is built
on Coq-Elpi, the Lean realization uses typeclass resolution and `MetaM`.

## Ideas drawn from other work

- **AdapTT** — Arthur Adjedj, Meven Lennon-Bertrand, Thibaut Benjamin, Kenji
  Maillard. *AdapTT: Functoriality for Dependent Type Casts.* POPL 2026.
  [arXiv:2507.13774](https://arxiv.org/abs/2507.13774), [doi:10.1145/3776664](https://doi.org/10.1145/3776664).
  The functor laws (`cast_id`/`cast_trans` = AdapTT's `AdaptId`/`AdaptComp`),
  the combinator-distributes-over-composition coherence, and the
  description-based (`IndDesc`) scheme for `@[derive Param]` — including the
  mixed-variance "Non-example" guard — follow AdapTT. Where AdapTT secures the
  laws *definitionally* via a cast calculus, the Lean realization obtains them by
  `rfl` from the fact that the composite's forward map is function composition;
  the dependent formers `paramForall` (Π) and `paramSigma` (Σ, `sigma_cast_eq` =
  `Adapt Σ = Σ Adapt`) carry the same functoriality into the dependent world,
  univalence-free below the universe.

- **CoqEAL** — Cyril Cohen, Maxime Dénès, Anders Mörtberg.
  *Refinements for Free!* CPP 2013.
  The data-refinement view — parametric relations between an abstract type and a
  computational representation — informs the `Related`/`RelatedBinOp` encoding
  layer.

- **Computing with classical reals** — Cezary Kaliszyk and Russell O'Connor.
  *Computing with Classical Real Numbers.* Journal of Formalized Reasoning, 2009.
  [arXiv:0809.1644](https://arxiv.org/abs/0809.1644).
  The minimal level for transferring a decidable equation — a map on the domains
  and an equality-reflecting embedding on the codomain — is their proof-transfer
  move, realized in `ReprTransfer` by `BinOpRealization.eq_transfer`.

- **Cubical congruence** — Emil Holm Gjørup and Bas Spitters,
  *Congruence Closure in Cubical Type Theory* (2020; Cubical Agda implementation
  [github.com/limemloh/cubical-congruence](https://github.com/limemloh/cubical-congruence)).
  An advanced heterogeneous congruence (`hcongr`) provable in cubical type
  theory. The general dependent-Π relation `R_forall` relates outputs of
  *different* fiber types across a representation change (`hcongr_hetero`,
  `HCongrConnection`) — the univalence-free realization of the cubical
  `hcongr_ideal` shape, using a graded `Param` where the cubical version uses a
  `PathP`. The diagonal `Eq`/`HEq` instance is its degenerate case (it collapses
  to native `congr`), and the set-level relational congruence closure
  (`param_cc`) is the closure form. Only the universe-valued fiber (`map4`) is
  out of reach, for the same reason (`UnivalenceStatus.univalence_inconsistent`)
  as the rest of the engine.

- **Two-Level Type Theory and the strict/univalent boundary** —
  Annenkov, Capriotti, Kraus, Sattler (*Two-Level Type Theory and Applications*);
  Voevodsky's Homotopy Type System (HTS); the `SProp` line (Gilbert, Cockx,
  Sozeau, Tabareau, *Definitional Proof-Irrelevance without K*). These frame the
  analysis behind `UnivalenceStatus` — why type-level univalence is inconsistent
  with Lean's `Eq : Prop`, and what a strict + univalent coexistence would
  require.

## Lean / Mathlib mechanisms it integrates with or mirrors

The library is designed to cooperate with native Lean 4 + Mathlib machinery
(see `README.md` §"Interactions with Lean mechanisms"):

- **`Mathlib.Tactic.Translate`** (the generic name-mapping term-translation
  framework underlying `@[to_additive]` / `@[to_dual]`) — the mature analogue of
  our `@[param]` registry + `#transfer` translator; cited as the reference design
  for the translator's inductive/projection handling.
- **`gcongr`** (`Mathlib.Tactic.GCongr`) — `hgcongr` is its cross-head
  generalization; `GCongrProbe` records the single-head constraint and `HGCongr`
  carries the upstream patch.
- **`grind`** — the congruence-closure backend for `param_cc`; foundation squares
  are dual-tagged `@[grind =]`.
- **`aesop`** — the opt-in `Trocq` rule set bundles the transfer rules.
- **`norm_cast` / `push_cast`** — `@[norm_cast]` move-lemmas are recognized as
  embedding-level `Param` witnesses over the cast graph.
- **`Std.Do` / `mvcgen`** (`Triple`/`wp`) — `ParamTripleTransfer` lifts transfer
  to Hoare triples via the Kleisli logical relation `RComp`.

## Demonstration target — leanprover/hex

The `Transfer/Examples/Hex*` modules are a worked demonstration of the engine on
CoqEAL-style data refinements, modelled on the carriers of:

- **hex** — Kim Morrison and contributors.
  *Verified computational algebra in Lean 4* — Mathlib-free computational cores
  (dense-array linear algebra, fraction-free Bareiss, seq-polynomials, LLL) with
  separate `*-mathlib` correspondence libraries.
  [`leanprover/hex`](https://github.com/leanprover/hex).

These examples model hex's representations (dense `List` / `Array` storage,
seq-polynomials, modular residues) to exercise the refinement, `foldl` / `forIn`
combinator, and verified-compute layers. They contain no hex source; hex's own
`*-mathlib` libraries are the hand-written correspondence the engine mechanizes.

## Foundation

Built on **Lean 4** and **Mathlib** (leanprover and the Mathlib community).
