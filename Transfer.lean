/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Hierarchy.ParamLevel
import Transfer.Hierarchy.ParamWeaken
import Transfer.Hierarchy.ParamEquiv
import Transfer.Combinators.ParamArrow
import Transfer.Combinators.ParamForall
import Transfer.Synthesis.ParamSynth
import Transfer.Synthesis.ParamSynthExt
import Transfer.Synthesis.ParamResolve
import Transfer.Statements.ParamTransfer
import Transfer.Statements.ParamForallNested
import Transfer.Statements.ParamTransferTac
import Transfer.Translate.ParamTranslate
import Transfer.Translate.ParamDB
import Transfer.Translate.ParamTranslateTy
import Transfer.Translate.ParamTranslateOp
import Transfer.Translate.ParamTranslateFull
import Transfer.Base.UnivalenceStatus
import Transfer.Base.TransferLevel      -- transfer! : level-directed transfer tactic
import Transfer.Base.LevelRefusal       -- the decidable univalence-free level guard
import Transfer.Base.TransferInduction  -- natEquivInduction: recursor transfer
-- Interactions with native Lean mechanisms (see README §Interactions):
import Transfer.Integrations.ParamNormCast  -- norm_cast move-lemmas are Param witnesses
import Transfer.Integrations.ParamRelatedBridge -- one witness, both engines: RelatedBinOp ⇒ RArrow
import Transfer.Integrations.ParamCoe        -- Coe/CoeTC from a Param forward map
import Transfer.Integrations.ParamConv       -- conv-mode sub-term transfer
-- Container relational lift: `Param` for `×`/`Option`/`List` (extends the engine
-- from `→`/`∀` to data types).
import Transfer.Combinators.ParamData
import Transfer.Combinators.ParamSigma       -- dependent-pair (Σ) former + AdapTT cast law (Adapt Σ = Σ Adapt)
import Transfer.Combinators.ParamArray      -- Array container rule + relational foldl transfer (combinator lemma)
import Transfer.Integrations.ParamForIn      -- forIn/do-loop transfer: foldlR meets RComp (early exit + effects)
import Transfer.Integrations.ParamRComp      -- `rcomp`: structural RComp-witness assembly, folded into `param_transfer`
-- Automation-tactic integrations:
import Transfer.Integrations.GrindIntegration -- foundation lemmas dual-tagged @[grind =]
import Transfer.Integrations.AesopIntegration -- opt-in `Trocq` aesop rule set (importer-split)
import Transfer.Congruence.RCongr            -- rcongr: cross-head congruence descent
import Transfer.Congruence.HGCongrInit       -- hgcongr engine: env ext + @[hgcongr] attr + tactic
import Transfer.Congruence.HGCongr           -- hgcongr correspondences + cross-head demos
import Transfer.Congruence.ParamCongrClosure -- param_cc: relational congruence closure
import Transfer.Congruence.ParamSolve        -- param_solve: descent + closure-leaf (the union)
import Transfer.Congruence.ParamAuto         -- param_auto: one coordinator dispatching to every surface
import Transfer.Congruence.ParamCompose      -- param_compose: descend-and-dispatch (two extensions on one goal)
import Transfer.Congruence.GCongrProbe        -- gcongr single-head constraint probe
import Transfer.Congruence.HCongrConnection   -- cubical hcongr ↔ R_forall at the diagonal
-- Level inference, composition, deriving, crypto domains, and auto-weakening:
import Transfer.Synthesis.ParamInfer         -- variable-level (m,n) minimal-class inference
import Transfer.Combinators.ParamTrans       -- Param_trans: relation composition (map0..map3)
import Transfer.Deriving.ParamDerive         -- toward @[derive Param]: hand-ports + handler spec
import Transfer.Examples.ParamCryptoDomains  -- Baby Bear @[param] witnesses + TransferDom
import Transfer.Integrations.ParamAutoWeaken -- auto-weakening of witnesses + transfer_auto
-- Coherence laws (AdapTT) + description-based deriving:
import Transfer.Combinators.ParamCoherence   -- functor laws: cast_trans/cast_id + distributivity
import Transfer.Deriving.ParamDeriveHandler  -- @[derive Param] handler: IndDesc gen + variance
import Transfer.Deriving.ParamCongr          -- derive_param_congr: Related-kernel constructor congruence per structure
import Transfer.Examples.ParamCryptoExamples -- worked examples (cast_trans, derive, transfer)
import Transfer.Examples.ParamRetraction     -- non-diagonal ZMod p retraction domain (map3 map2a)
import Transfer.Examples.MachineLimbField     -- machine limbs ↔ prime field: strong non-diagonal heterogeneous dependent (multi-limb) example
import Transfer.Examples.StrongExamples       -- native-tactic-beating demos over non-diagonal domains
import Transfer.Examples.Trocq                -- the Trocq example suite (index + summable)
import Transfer.Examples.EffectfulTransfer    -- effectful triple transfer across a value-type change (ℕ↔ℤ), by mvcgen
-- Retrofit onto `leanprover/hex`'s verified computational algebra (README §Hex):
import Transfer.Examples.HexMatrixCorrespondence -- hex dense-storage ↔ Mathlib correspondence, generated
import Transfer.Examples.HexSeqPoly              -- hex dense-poly seqpoly refinement: non-injective, map2a
import Transfer.Examples.HexEffectful            -- hex elimination-step triple transfer (RComp/Std.Do)
import Transfer.Examples.HexDecide               -- hex `decide +kernel` side condition via ReprTransfer
import Transfer.Examples.HexArrayCompute         -- hex `Array` carrier: refinement is carrier-agnostic + @[csimp] verified compute

/-!
# ParamTransfer — the single entry point

`import Transfer` loads the whole engine: a Lean 4 framework for reasoning up to a
registered relation. It draws on modular parametricity
([Trocq](https://github.com/coq-community/trocq)'s graded map-class lattice and
combinators), relational transfer and data refinement (CoqEAL), heterogeneous
congruence from cubical type theory (the set-level form; Gjørup–Spitters), and
congruence-closure algorithms. On top of these it provides one auto tactic that
unifies several native Lean relational tactics (`congr`/`gcongr`, `norm_cast`,
cast-`rw`, `transfer`, `conv`, `aesop`/`grind`) behind a single inference rule.
Trocq is the largest single influence. The framework verifies compilers (the
CatCrypt compiler) and programs (`mvcgen` / `Std.Do` triples, hax-extracted code).
Full overview, file map and usage: [`README.md`](./README.md).

## The five layers (bottom-up; see the README table for the file map)

0. **Relation hierarchy** — `ParamHierarchy` (`MapClass = map0…map4`, `Map_k.Has`,
   `Param (m n) A B`), `ParamLevel` (lattice `⊑`/`meet` + the `arrowReq`/`forallReq`
   level tables), `ParamWeaken` (downgrade), `ParamEquiv` (bridges from the encoding
   classes).
1. **Combinators** — `ParamArrow` (function rule, map0–map4), `ParamForall`
   (dependent-Π rule).
2. **Synthesis** — `ParamSynth`(`Ext`) (`HasParam`: resolution = Elpi search) +
   `ParamResolve` (`param_resolve`, the level-directed search).
3. **Transfer** — `ParamTransfer` / `ParamForallNested` (`forallTransfer`),
   `ParamTrocq` (`param_transfer`, auto-resolved domain).
4. **Term-level `⟦·⟧`** — `ParamTranslate` (core), `ParamDB` (`@[param]` registry),
   `ParamTranslateTy` (change-of-rep binders), `ParamTranslateOp` (operators),
   `ParamTranslateFull` (the integrated translator + `#transfer`).

## The boundary (proven)

`UnivalenceStatus.univalence_inconsistent : Univalence → False`. Type-level
univalence is inconsistent in Lean (`Eq : … → Prop` is proof-irrelevant), so the
`map4`/`Type`-motive level is unreachable. The univalence-free fragment realized
here is therefore the entire consistent space — and, since Lean's `funext` is
free, it is wider than Coq's univalence-free cap.
-/
