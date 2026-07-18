# Trocq / ParamTransfer — tactic, command, and attribute reference

This reference covers every tactic, command, attribute, conv step, and
Lean-mechanism integration the library exposes. For the architecture and the
theory, see [`README.md`](README.md); this file is the call-site manual.

The engine is **relational congruence closure over a registered relation**:
the same job `grind` does for `=` and `gcongr` does for `≤`, generalized to an
arbitrary registered relation `R` (including cross-head representation changes
neither handles natively), emitting a kernel-checked proof term. Everything a
tactic does decomposes into three rule kinds over `R`:

* **atoms** — registered `@[param]` / `Related` / `RelatedBinOp` witnesses, plus
  context hypotheses of relatedness type;
* **congruence (functoriality)** — from related arguments infer related
  applications (this is where cross-head `f ≠ g` lives);
* **equivalence** — reflexivity, symmetry, transitivity of `R`.

There are four families:

| Family | What it does | Section |
|---|---|---|
| **Transfer** | synthesize a transferred statement/term **and** its relatedness proof | [↓](#transfer-family) |
| **Congruence** | discharge a *fixed* `Related`/`=` representation-change goal structurally | [↓](#congruence-family) |
| **Conv / cast / coe** | plug transfer into native rewriting and elaboration | [↓](#conv--cast--coe-family) |
| **Automation integration** | expose the engine through `grind` / `aesop` / `mvcgen` | [↓](#automation-integration-family) |

Two relations coexist. The **`Param` engine** (`Param .map_k .map_l A B`, on
`RArrow`/`Param`) is the faithful Coq-Trocq port carrying the term translation
`⟦·⟧`. The **`Related` engine** (`Related enc a b`, definitionally `enc a = b`)
serves the encoding-relation case. They meet in the example domains, where the
same operations are registered as both `@[param]` witnesses and `RelatedBinOp`
instances.

Namespaces: the `Param`-engine entry points live in
`Transfer.Param`; the `Related`-engine congruence tactics
(`transfer`, `rcongr`, `hgcongr`, `param_cc`, `param_solve`) live in
`Transfer`.

---

## Transfer family

These are the engine proper: each one *produces* a transferred object together
with its relatedness proof, resolving witnesses from the registries.

### `#transfer t`

1. **Purpose.** Term-level parametricity translation: synthesize `⟦t⟧` (the
   transferred term) and a relatedness proof, resolving constants from the
   ambient `@[param]` registry.
2. **Applies to / produces.** A command on a `term` `t`. Logs `⟦t⟧ = t'  ⊢  <type
   of the relatedness proof>`. Handles the first-order fragment:
   `const`/`var`/`app`/`lam`/operator spines, with change-of-representation
   binders.
3. **Example.**
   ```lean
   #transfer (fun x : Nat => Nat.succ x * x)
   -- ⟦fun x ↦ x.succ * x⟧ = fun x' ↦ x'.succ.mul x'
   --   ⊢  ∀ (x x' : Nat), x = x' → x.succ.mul x = x'.succ.mul x'
   ```
   `Nat.succ` resolves from the registry (`@[param] succWitFull`); `*` goes
   through the operator rule (`demoOpDB`, `HMul.hMul ↦ Nat.mul`).
4. **When to use vs alternatives.** Use to obtain the *synthesized term* and its
   proof, rather than to close an existing goal. To transfer an existing
   `∀`-goal, use `param_transfer`. To run the translation against a custom (not
   ambient) database, call `translateAll` directly.
5. **Gotchas.** Raises `translateAll: unregistered constant` on a constant with
   no `@[param]` witness — by design (the non-fabrication invariant). It does not
   name-guess, walk inductives/projections, or do dependent `Π`/recursor
   transfer (the `map4` univalence cap). The operator database is fixed to
   `demoOpDB` at the `#transfer` call site.
6. **File.** `ParamTranslateFull.lean` (`#transfer`, `translateAll`). The ambient
   registry materialiser `getParamDB` and the lower-level driver
   `#param_translate` are in `ParamDB.lean`.

### `param_transfer`

1. **Purpose.** Reduce a `∀`-implication between two representations to its
   pointwise obligation; the domain `Param` is resolved automatically.
2. **Applies to / produces.** A goal `(∀ a, P a) → (∀ a', P' a')`. Leaves the
   pointwise obligation
   `∀ a a' (_ : (TransferDom.dom).R a a'), P a → P' a'`. Refines by
   `forallTransferAuto`, which resolves the domain via the `TransferDom` class.
3. **Example.**
   ```lean
   example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) :
       (∀ n : ℕ, P n) → (∀ n : ℕ, Q n) := by
     param_transfer
     intro a a' (haa' : a = a') hPa
     exact haa' ▸ h a hPa
   ```
   Change-of-representation works identically: `(∀ n : Num, 0 ≤ n) → (∀ k : ℕ, 0
   ≤ k)` resolves through `TransferDom Num ℕ`, and
   `(∀ i : ℤ, …) → (∀ x : ZMod p, …)` through the `ℤ ↠ ZMod p` retraction
   (`ParamRetraction.lean`).
4. **When to use vs alternatives.** The standard entry point for transferring a
   universally-quantified statement. `transfer_auto` is a superset that also
   handles the arrow `app`-rule shape. `#transfer` is for synthesizing a *term*, not
   reducing a `∀`-goal.
5. **Gotchas.** Resolves the domain via `TransferDom`, so the source/target type
   pair must have a `TransferDom` instance — built-in are the diagonal (any `A A`,
   graph `Eq`), `Num ↦ ℕ`, and `ℤ/ℕ ↠ ZMod p`. For a new representation change,
   add a `TransferDom` instance. The pointwise obligation remains to discharge
   (usually by `intro`/`assumption`/`exact`, plus a rewrite along the relation).
6. **File.** `ParamTransfer.lean` (`param_transfer`, `TransferDom`,
   `forallTransferAuto`).

### `transfer_auto`

1. **Purpose.** Single unified transfer entry dispatching both the `∀`-rule and
   the `R_arrow` `app`-rule.
2. **Applies to / produces.**
   * a `∀`-implication goal → the `∀`-rule (`forallTransferAuto`, falling back to
     explicit-domain `forallTransfer`);
   * an `R_arrow PA PB f f'` goal → peeled to its pointwise codomain obligation.
   Runs at a fixed univalence-free output class.
3. **Example.**
   ```lean
   -- arrow-relatedness goal, same tactic:
   example (f f' : ℕ → ℕ) (h : ∀ a, f a = f' a) :
       R_arrow (paramEqDom ℕ) (paramEqCod ℕ) f f' := by
     transfer_auto
     rename_i a a' har
     show f a = f' a'
     cases har; exact h a
   ```
4. **When to use vs alternatives.** Use when a proof mixes `∀`-goals and arrow
   `app`-goals and one tactic must handle both. For a `∀`-only proof,
   `param_transfer` is the more focused name.
5. **Gotchas.** Fixed output class (not per-occurrence minimal). Per-subterm
   level minimization is the job of `inferParamLevels`/`inferRootClass`
   (`ParamInfer.lean`); `transfer_auto` does not call the solver.
6. **File.** `ParamAutoWeaken.lean`.

### `param_resolve`

1. **Purpose.** Level-directed search closing a `Param m n A B` goal at any
   lattice-reachable level.
2. **Applies to / produces.** A goal `Param m n A B`. Tries, in order: a
   registered instance at the exact `(m,n)`; synthesize at a stronger registered
   level and `Param.weaken` down (discharging `⊑` by `decide`); decompose an
   arrow (`apply paramArrow`) and recurse; embedding/equivalence leaves.
3. **Example.**
   ```lean
   example : Param .map0 .map0 (Nat → Nat) (Nat → Nat) := by param_resolve
   -- synthesized at (map1,map1), weakened to (map0,map0)
   ```
4. **When to use vs alternatives.** Use to obtain a `Param` *witness* at a
   specific level for a function/base type. For a *single* registered witness
   reused at lower levels, `auto_weaken` is simpler. `HasParam` instance
   resolution covers the fixed self-relation level directly.
5. **Gotchas.** The candidate stronger levels are a hardcoded list
   (`(map1,map1)`, `(map3,map0)`); the `map4` universe relation is unreachable by
   construction. Works over arrow/base structure, not arbitrary terms.
6. **File.** `ParamResolve.lean`.

### `auto_weaken`

1. **Purpose.** "Register high, use low": close a `Param m' n' A B` goal at any
   lattice-lower level from a single registration at the strongest level.
2. **Applies to / produces.** A goal `Param m' n' A B`. Resolves
   `RegisteredParam A B m n` and applies `Param.weaken (by decide) (by decide)`
   down to `(m', n')`.
3. **Example.**
   ```lean
   instance regNatNat : RegisteredParam Nat Nat .map3 .map0 where
     reg := { R := Eq, fwd := ⟨id, fun _ _ h => h, fun _ _ h => h⟩, bwd := ⟨⟩ }

   example : Param .map0 .map0 Nat Nat := by auto_weaken   -- below the registration
   example : Param .map2b .map0 Nat Nat := by auto_weaken  -- incomparable branch, still ⊑ map3
   ```
4. **When to use vs alternatives.** Use when one type pair carries a strong
   witness and lower-class goals must resolve without restating it. This
   mirrors upstream Trocq's `Trocq Use` "register every sub-class version".
   `param_resolve` is the broader search over structure; `auto_weaken` is the
   single-registration shortcut.
5. **Gotchas.** Needs a `RegisteredParam` instance (a *sibling* registry, **not**
   `@[param]`/`paramExt`); the level pair is an `outParam` recovered from
   `(A, B)`. The data-level enumerator `allWeakenings` returns the full below-set
   of a witness when it is needed as data (`belowList`/`mem_belowList` give the
   decidable below-set).
6. **File.** `ParamAutoWeaken.lean` (`auto_weaken`, `RegisteredParam`,
   `allWeakenings`).

### `transfer`

1. **Purpose.** Automatic binder traversal plus per-leaf dispatch to the
   `Related` registry — no commuting square named at the call site.
2. **Applies to / produces.** A goal-shape-directed `elab` (`transferCore`). On
   the goal head:
   * `Iff` of two `∀`s → `forall_congr'`, `intro`, recurse;
   * `Eq` of functions → `funext`, recurse;
   * a `∀`/`→` → `intro`, recurse;
   * otherwise the leaf is dispatched (`transferLeaf`).
3. **Example.**
   ```lean
   example (c : F) : ∀ a b : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by transfer
   ```
   When a square is bundled in a local realization structure, surface it with a
   `have` and the registry sweep picks it up:
   ```lean
   example (R : ByteGroupRealization prims) (init : P.GT) (l : List P.GT) :
       R.encT (l.foldl (· * ·) init) = (l.map R.encT).foldl prims.fp12Mul (R.encT init) := by
     have hsq := R.fp12Mul_commutes
     transfer
   ```
4. **When to use vs alternatives.** Use to close an equation/`Iff`-of-`∀` whose
   cross-head op-tree leaf is a *single* registered composite. `rcongr`/`hgcongr`
   descend *into* the op-tree (first-class per-argument subgoals); `transfer`
   collapses the leaf inside one `inferInstance`. Compose them: `transfer` for
   the binder layer, `rcongr` for the op-tree.
5. **Gotchas.** `transferLeaf` swallows failure (leaves the goal rather than
   erroring) — the non-fabrication residual; a missing square stays a visible
   goal. The leaf cascade is `rfl | Iff.rfl | assumption | transferGround | simp
   only [transfer] | solve_by_elim [...] | grind`. Helper closers
   (`transferGround`, `transferLeaf`, `transferCore`, `transferRegistryLeaf`) are
   exposed for tactic authors; `transferRegistryLeaf` *propagates* failure (no
   `try`), so descent tactics can chain a heavier discharger after it.
6. **File.** `TransferTactic.lean`.

---

## Congruence family

These discharge a **fixed** relatedness/representation-change goal
`Related enc t t'` (or an `=` bridged to one) — the relational analogues of
`congr`/`gcongr`/`grind`. They are four views of one rule system; pick by the
shape of what closes the goal.

| | strategy | rules | reaches |
|---|---|---|---|
| `rcongr`, `hgcongr` | top-down **descent** | congruence only | nested cross-head op-trees, per-arg subgoals |
| `param_cc` | bottom-up **closure** | congruence + equivalence | transitivity / context-hypothesis chains |
| `param_solve` | **descent + closure-leaf** | both | the union |

### `rcongr`

1. **Purpose.** Relational cross-head congruence *descent* over the
   `Related`/`RelatedBinOp` square database.
2. **Applies to / produces.** A goal `Related enc t t'` (or an `=` bridged via
   `transferGround`). At a binary node `op a b` ↔ `bop a' b'` linked by a
   registered `RelatedBinOp enc op bop`, applies `rcongrBinOp`, leaving
   per-argument relatedness subgoals `Related enc a a'`, `Related enc b b'`, and
   recurses; leaves close via the registry (`leaf`/`leafId`) or `rfl`.
3. **Example.**
   ```lean
   example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by rcongr
   ```
4. **When to use vs alternatives.** Use for a pure cross-head op-tree goal that
   needs the *structural* descent (per-argument subgoals). `hgcongr` is the
   attribute-driven, relation-generic generalization; `rcongr` is its hard-wired
   specialization to `Related`/`RelatedBinOp` (no new attribute — it reuses the
   existing instance set). For transitivity/context chains, use `param_cc`.
5. **Gotchas.** Cannot close a pure transitivity goal: its leaf is
   `inferInstance | rfl`, which keys on the syntactic RHS and cannot bridge an
   intermediate `c`–`b` link. Adding a new realized op is a one-line
   `instance … : RelatedBinOp …`.
6. **File.** `RCongr.lean` (`rcongr`, `rcongrBinOp`, `rcongrCore`).

### `hgcongr`

1. **Purpose.** Heterogeneous (cross-head) generalized congruence: `gcongr` with
   the same-head constraint lifted, driven by a head-*pair*-keyed `@[hgcongr]`
   lemma database.
2. **Applies to / produces.** A goal `R (f a₁ … aₘ) (g b₁ … bₙ)` whose head pair
   `(f, g)` has a registered `@[hgcongr]` lemma (heads may differ; arities may
   differ). Reduces to the per-argument subgoals, recursing; leaves and reflexive
   steps close by `rfl`. The relation `R` is read off the lemma's conclusion
   (`Eq`, `≤`, `Related`, …), not fixed.
3. **Example.**
   ```lean
   @[hgcongr]
   theorem mul_bbFieldMul_hcongr {a₁ b₁ a₂ b₂ : F} (h₁ : a₁ = a₂) (h₂ : b₁ = b₂) :
       a₁ * b₁ = bbFieldMul a₂ b₂ := by subst h₁; subst h₂; exact (bbFieldMul_eq _ _).symm

   example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by hgcongr
   ```
   The diagonal pair `(f, f)` recovers gcongr's homogeneous case, so a same-head
   `@[hgcongr]` lemma mixes freely with cross-head steps.
4. **When to use vs alternatives.** Use for the gcongr *architecture*
   (attribute-tagged lemmas, any relation) extended to cross-head correspondences.
   `rcongr` is the in-tree, `Related`-only specialization; `gcongr` cannot host
   cross-head at all (see `GCongrProbe`).
5. **Gotchas.** Requires the head correspondence to be tagged `@[hgcongr]`. The
   varying-argument pairs are recovered from the lemma's *hypotheses* (insensitive
   to `arity(f) ≠ arity(g)`, e.g. `HMul.hMul` arity 6 vs `bbFieldMul` arity 2), so
   the lemma must state each varying pair as a hypothesis `Rᵢ lᵢ rᵢ`; tagging
   fails with "no varying-argument hypotheses found" otherwise.
6. **File.** `HGCongr.lean` (correspondences + demos); engine — the head-pair env
   extension, the `@[hgcongr]` attribute (`makeHGCongrLemma`), and `hgcongrCore`
   — in `HGCongrInit.lean`.

### `param_cc`

1. **Purpose.** Saturating, context-incorporating relational congruence
   *closure* over `Related`.
2. **Applies to / produces.** A goal `Related enc s t` (or its underlying
   `enc s = t`). Surfaces every context hypothesis `h : Related enc a b` as its
   equation `h.rel : enc a = b` and every `h : RelatedBinOp enc op bop` as its
   square `h.comm`; reduces a `Related` goal to its equation; closes by `grind`,
   whose congruence closure composes the squares and surfaced equations
   transitively to a fixpoint.
3. **Example.**
   ```lean
   -- transitivity through a context hypothesis (out of rcongr's reach):
   example {A α : Type} (enc : A → α) (a : A) (c b : α)
       (hac : Related enc a c) (hcb : c = b) : Related enc a b := by param_cc

   -- saturating congruence over context hyps + a registered square:
   example {A α : Type} (enc : A → α) (op : A → A → A) (bop : α → α → α)
       [RelatedBinOp enc op bop] (x y : A) (x' y' : α) (z : A) (z' : α)
       (hx : Related enc x x') (hy : Related enc y y') (hz : Related enc z z') :
       Related enc (op (op x y) z) (bop (bop x' y') z') := by param_cc
   ```
4. **When to use vs alternatives.** Use when the proof needs transitivity or
   chaining through context hypotheses — what `rcongr` provably cannot do.
   `param_solve` is the union (descent *and* closure); use `param_cc` standalone
   when there is no op-tree to descend.
5. **Gotchas.** Over the encoding relation, `Related enc a b` is definitionally
   `enc a = b`, so `param_cc` *is* `grind` plus a relation→equation prelude; its
   independent value appears only for a non-equational relation. Inherits
   `grind`'s limits (e.g. it can time out on heavy ENNReal/BitVec arithmetic);
   keep the emitted kernel opaque on the RHS of each square.
6. **File.** `ParamCongrClosure.lean` (`param_cc`, `paramCCCore`).

### `param_solve`

1. **Purpose.** The common generalization of `rcongr` (descent) and `param_cc`
   (closure): goal-directed cross-head descent with the saturating closure as the
   leaf discharger.
2. **Applies to / produces.** A goal `Related enc t t'` (or `=` bridged). At a
   binary op-tree node, apply `rcongrBinOp` and recurse (descent); at a leaf, try
   the registry/`rfl`, and on failure fall into `paramCCCore` (closure — surface
   context hypotheses, saturate with `grind`). Closes the **union** of what
   `rcongr` and `param_cc` close.
3. **Example.**
   ```lean
   -- cross-head descent AND a closure leaf together:
   example {A α : Type} (enc : A → α) (op : A → A → A) (bop : α → α → α)
       [RelatedBinOp enc op bop] (a b : A) (a' : α) (b'' c : α)
       (ha : Related enc a a') (hb : Related enc b b'') (hbc : b'' = c) :
       Related enc (op a b) (bop a' c) := by param_solve
   ```
4. **When to use vs alternatives.** The default when it is unclear whether the
   goal needs descent, closure, or both. Use the narrower `rcongr`/`param_cc`
   for a single strategy (faster, more predictable subgoals).
5. **Gotchas.** Same encoding-relation collapse as `param_cc` (the closure leaf
   is `grind`). The descent backend is hardwired to `rcongrBinOp`
   (`Related`/`RelatedBinOp`); swapping in an `hgcongr` head-pair lookup is the
   pluggable general form but is not the default.
6. **File.** `ParamSolve.lean` (`param_solve`, `paramSolveCore`).

### The same-head restriction in `gcongr` — `GCongrProbe`

`@[gcongr]` accepts **only** same-head monotonicity lemmas `f x₁…xₙ ∼ f x₁'…xₙ'`.
`Mathlib.Tactic.GCongr.Core` enforces `lhsHead == rhsHead && arity ==` at three
sites: lemma registration (`makeGCongrLemma`), the runtime descent
(`Lean.MVarId.gcongr`), and the single-head lookup key (`GCongrKey`). A
`RelatedBinOp`-shaped lemma cannot even be tagged. This is *why* the family needs
`rcongr`/`hgcongr`. `GCongrProbe.lean` records the rejection with a control
(`add_mono_probe`, accepted) and a cross-head record (`cross_head_realization`,
left untagged); `HGCongr.lean`'s "Upstream patch" section carries the exact
3-site head-pair patch that lifts the restriction upstream.

---

## Conv / cast / coe family

These plug transfer into native rewriting (`conv`), into `norm_cast`-style
witnesses, and into elaboration-time coercion.

### `transferConv` (conv step)

1. **Purpose.** Rewrite a focused sub-term to its transferred form *inside a
   context*, justified by the `Related` instance composite.
2. **Applies to / produces.** A `conv` step. On the focus `t`: discover the
   transferred shape `t'` via the `@[transfer]` simp set, prove `t = t'` by
   synthesizing `Related id t t'` (composing registered `RelatedBinOp` squares,
   extracted via `transferGround`), and install that proof — **the typeclass
   composite, not the simp proof**.
3. **Example.**
   ```lean
   example (a b c : F) (P : F → Prop) (h : P (bbFieldAdd (bbFieldMul a b) c)) :
       P (a * b + c) := by
     conv in (a * b + c) => transferConv
     exact h
   ```
4. **When to use vs alternatives.** Use to transfer one sub-term in the middle of
   a larger goal, alongside `rw`/`simp`/`gcongr`. For the whole goal, use
   `transfer`. For the simp proof (rather than the typeclass composite), use
   `transferSimpConv`.
5. **Gotchas.** Scope is the closed first-order, identity-encoding (`id`) op-tree
   fragment `Related.lean` covers — no binder traversal, no richer encodings. The
   focus type must live in a `Type u` universe (the proof is built at that
   level). The `Related id t t'` goal is elaborated *from source syntax* so
   `composeBinOp` keys on the source-elaborated `id` (a hand-assembled `mkApp` is
   defeq but does not match instance resolution).
6. **File.** `ParamConv.lean`.

### `transferSimpConv` (conv step)

1. **Purpose.** The simp-set-driven complement of `transferConv`.
2. **Applies to / produces.** A `conv` step; a thin wrapper for `simp only
   [transfer]` on the focus — the equational `@[transfer]` realization set with the simp
   proof.
3. **Example.**
   ```lean
   example (a b c : F) (P : F → Prop) (h : P (bbFieldAdd (bbFieldMul a b) c)) :
       P (a * b + c) := by
     conv in (a * b + c) => transferSimpConv
     exact h
   ```
4. **When to use vs alternatives.** Use when the simp rewrite suffices and the
   typeclass-composite proof of `transferConv` is unneeded. It is the `conv`-mode
   form of `repr_transfer`.
5. **Gotchas.** Only as strong as the `@[transfer]` equational set; carries no
   relatedness proof beyond the simp justification.
6. **File.** `ParamConv.lean`.

### `repr_transfer` / `repr_transfer!`

1. **Purpose.** Whole-goal Phase-1 transfer: rewrite the goal's abstract
   operations into their registered emitted kernels.
2. **Applies to / produces.** `repr_transfer` ≡ `simp only [transfer]`;
   `repr_transfer!` ≡ `simp only [transfer] <;> rfl` (also closes by reflexivity).
3. **Example.** `by repr_transfer!` closes a goal whose two sides differ only by
   registered `@[transfer]` realizations.
4. **When to use vs alternatives.** The simplest "compile to the emitted leaf"
   driver. `transfer` adds binder traversal and a richer leaf cascade; the
   `param_*` tactics add cross-head descent and closure.
5. **Gotchas.** Pure simp — no proof-term parametricity, no level tracking, no
   cross-head descent. Only the registered equational set.
6. **File.** `Core.lean`.

### `norm_cast` move-lemmas as `Param` witnesses

1. **Purpose.** A `@[norm_cast]` move lemma `↑(a ⋄ b) = ↑a ⋄ ↑b` **is** a Trocq
   `Param` binary relatedness witness for the cast graph `R a a' := (↑a = a')`.
2. **Applies to / produces.** Not a tactic — a *correspondence* the translator
   consumes. `addCastWit` (from `Nat.cast_add`) and `mulCastWit` (from
   `Nat.cast_mul`) are `RArrow NatIntR (RArrow NatIntR NatIntR) op op'` witnesses;
   `paramWitOfCastHom` exhibits the generic equivalence (a cast-homomorphism
   property *is* the curried `RArrow` witness).
3. **Example.** Wired into `castOpDB`/`castTyDB`, the translator transfers a whole
   `ℕ`-term across `ℕ ↦ ℤ`:
   ```lean
   translateAll castOpDB castTyDB {} {} ⟦fun n : ℕ => n + n * n⟧
   -- ⊢ ∀ n n', ↑n = n' → ↑(n + n * n) = n' + n' * n'
   ```
4. **When to use vs alternatives.** Use to transfer across a coercion graph using
   the existing `norm_cast` lemma set as operator witnesses — Trocq is
   `norm_cast` generalized from coercions to arbitrary registered
   representations.
5. **Gotchas.** Demonstrated for the binary case over `ℕ → ℤ` with `+`/`*`; the
   `n`-ary generalization is the same operator-spine stripping. The witnesses
   feed the term translator, not the `Related`-engine tactics directly.
6. **File.** `ParamNormCast.lean`.

### `Coe` / `CoeTC` from a `Param` forward map

1. **Purpose.** Derive a Lean coercion from a `Param` witness's forward map, so a
   representation change fires during elaboration.
2. **Applies to / produces.** Instances, not a tactic. `coeOfParam`/`Param.fwdMap`
   project the forward function `A → B`; `coeTCOfHasParam` is a **scoped** blanket
   `CoeTC A B` from a synthesized `HasParam .map1 .map1 A B`.
3. **Example.**
   ```lean
   instance coeNatWrap : Coe Nat Wrap where coe := coeOfParam natWrapParam
   example (a : Nat) : Wrap := a              -- Wrap.mk inserted by the elaborator
   example (a : Nat) : ((a : Wrap)) = Wrap.mk a := rfl
   ```
   The scoped blanket fires under `open scoped …Trocq.Param`:
   `example (b : Boxed) : Nat := b`.
4. **When to use vs alternatives.** Use for transparent, per-pair representation
   insertion at elaboration. To *also* keep the relatedness proof (not just the
   function), use `param_transfer` — a coercion drops the proof.
5. **Gotchas.** Lean has **no** general coercion-fallback hook (unlike
   Coq-Elpi's `trocqoercion`), so this is per-`(A, B)`, keyed on the instance
   cache. The blanket is `scoped` (opt-in) on purpose: a global version
   over-fires (every `idHasParam`, re-entrant arrow search) on any type mismatch.
   A specific `Coe` is the safest form.
6. **File.** `ParamCoe.lean`.

---

## Automation integration family

These expose the engine through `grind`, `aesop`, and `mvcgen`/`Std.Do` wp.

### `grind` integration (`@[grind =]` dual-tagging)

1. **Purpose.** Make `grind` a transfer leaf-discharger by dual-tagging
   realization squares into its database.
2. **Applies to / produces.** `attribute [grind =] mul_repr add_repr` adds the
   already-`@[transfer]` realization lemmas as `grind` rewrite candidates; `grind`
   then composes them through its congruence closure.
3. **Example.**
   ```lean
   attribute [grind =] mul_repr add_repr
   theorem grind_leaf (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by grind
   ```
4. **When to use vs alternatives.** Use to close transfer *leaf* equations (the
   closed first-order composites) in one `grind`, with no positional `rw` chain.
   This dual-tag is what makes `param_cc`'s closure work — the registered squares
   are already in `grind`'s DB. `transfer`'s leaf cascade falls back to `grind`
   last.
5. **Gotchas.** Safe only when the emitted kernel is **opaque** on the RHS of
   each square (so `grind` never chases the underlying `BitVec 64` arithmetic,
   which it can time out on). The dual-tag pattern is per realization lemma.
6. **File.** `GrindIntegration.lean`.

### The `Trocq` aesop rule set

1. **Purpose.** An opt-in aesop rule set bundling the transfer machinery as
   aesop rules.
2. **Applies to / produces.** `transferGround` as a **safe apply** rule;
   `transferCore` (the `transfer` driver) as an **unsafe 50% tactic** rule.
   Invoked with `aesop (rule_sets := [Transfer])`.
3. **Example.**
   ```lean
   example (a b c : F) : a * b + c = bbFieldAdd (bbFieldMul a b) c := by
     aesop (rule_sets := [Transfer])
   example (c : F) : ∀ a b : F, a * b + c = bbFieldAdd (bbFieldMul a b) c := by
     aesop (rule_sets := [Transfer])
   ```
4. **When to use vs alternatives.** Use when aesop's search should dispatch
   transfer-shaped goals (ground composites + quantified/function-equality
   shapes). For a single goal, the dedicated tactics are more direct.
5. **Gotchas.** The set is **OFF by default and never folded into the default
   set**: aesop fails open, so an always-on transfer rule could mask a *missing*
   square (the exact failure the layer surfaces). A rule set declared with
   `declare_aesop_rule_sets` is invisible in the declaring file, so the
   declaration (`AesopRuleSet.lean`) is split from the registrations and uses
   (`AesopIntegration.lean`); register rules and invoke the named set only from an
   importer.
6. **File.** `AesopIntegration.lean` (registrations + demos); declaration in
   `AesopRuleSet.lean`.

### `mvcgen` / `Std.Do` `wp` triple transfer (`RComp`)

1. **Purpose.** Transfer a Hoare/`wp` triple along a value relation, lifted to
   computations through the Kleisli relation `RComp`.
2. **Applies to / produces.** Lemmas, not a tactic. `RComp Rα c c'` is
   `wp`-refinement modulo `Rα`; `RComp.pure`/`RComp.bind`/`RComp.refl` are the
   compositional core; `triple_transfer` turns `⦃P⦄ c ⦃Q, E⦄` into
   `⦃P⦄ c' ⦃Q', E⦄` given an `RComp`-witness and postcondition relatedness.
3. **Example.** A concrete `SPComp` instantiation (`SPComp.triple_transfer`)
   transfers the triple of `SPComp.pure true` to that of `SPComp.pure false`
   across `Rα b b' := (b = true ∧ b' = false)`.
4. **When to use vs alternatives.** Use to transport a Hoare triple between two
   monadic programs related at the value level — the abstraction theorem at the
   monad level. For pure `∀`-statements, use `param_transfer`.
5. **Gotchas.** The `RComp`-witness is assembled by hand from `pure`/`bind` here
   (the `MetaM` synthesizer / full `mvcgen` integration is not provided). Scope is
   `Prop`-predicate `wp` triples; the quantitative/`Advantage` route is out of
   scope (expectation transformers are monotone but not conjunctive).
6. **File.** `ParamTripleTransfer.lean`.

---

## Deriving and level inference

### `deriving Param` / `@[derive Param]`

1. **Purpose.** Generate the parametricity lift of an inductive from its
   constructor signatures.
2. **Applies to / produces.** A `deriving Param` clause (or `deriving instance
   Param for T`). Emits the constructor-wise relation `T.R_param`; for
   **non-recursive** inductives (records/enums) and **uniform-recursive** ones
   (List/Tree-shape) it additionally synthesizes the forward map `T.paramMap` and
   a full `Param .map3 .map0` instance `T.param_instance` (so the result feeds
   `castViaParam`).
3. **Example.**
   ```lean
   structure ElGamalCt (G : Type) where
     c1 : G
     c2 : G
     deriving Param
   -- generated ElGamalCt.R_param: two ciphertexts related iff components are
   theorem elgamal_ct_related {G G' : Type} (P : G → G' → Prop)
       (a1 a2 : G) (b1 b2 : G') (h1 : P a1 b1) (h2 : P a2 b2) :
       ElGamalCt.R_param P (ElGamalCt.mk a1 a2) (ElGamalCt.mk b1 b2) :=
     ElGamalCt.R_param.mk h1 h2
   ```
4. **When to use vs alternatives.** Use to obtain a `Param` lift mechanically for
   a crypto record/enum or a uniform-recursive container, instead of hand-porting
   it (`R_prod`/`R_list` shapes). For arbitrary terms, use `#transfer`.
5. **Gotchas.** Rejects **mixed-variance** inductives (a parameter in both co-
   and contravariant position, e.g. a field `A → A`) with `NonExample (Mixed
   variance)`, and purely contravariant occurrences likewise. Declines
   **nested/reflexive/indexed** inductives up front (`isNested || isReflexive ||
   numIndices ≠ 0` → handler returns `false`) — no faux fallback. The handler is
   live only in *downstream* files (the `initialize` registration takes effect
   after import).
6. **File.** `ParamDeriveHandler.lean` (the handler, `IndDesc`, variance guard);
   `ParamDerive.lean`/`ParamData.lean` carry the hand-ported shapes
   (`R_sum`/`R_nat`/`R_prod`/`R_option`/`R_list`).

### Level inference for tactic authors — `inferRootClass` / `inferRootClassExpr`

1. **Purpose.** Compute the minimal `MapClass` an occurrence requires — the
   constraint-graph least-fixpoint solver over the proven lattice.
2. **Applies to / produces.** Pure/`MetaM` functions, not a tactic.
   `inferParamLevels : TyShape → (Nat × Assign)` and `inferRootClass : TyShape →
   MapClass` work on the simplified `TyShape` core (`base`/`arrow`/`forallT`);
   `inferParamLevelsExpr`/`inferRootClassExpr` are the `Expr` front-ends (walking
   a real Lean type via `exprToTyShape`, with `@[param]`-registry lower bounds and
   an override table).
3. **Example.**
   ```lean
   example : inferRootClass (.arrow .leaf .leaf) = .map0 := by native_decide
   example : inferRootClass (.arrow .leaf (.base (some .map3))) = .map3 := by native_decide
   ```
4. **When to use vs alternatives.** Use when building a level-directed tactic:
   read off `inferRootClass` for the (shape-abstracted) type, synthesize at that
   class, then `Param.weaken`/`auto_weaken` down. This generalizes the fixed
   output class of `transfer_auto`.
5. **Gotchas.** An unconstrained shape minimizes to `map0` (never the inconsistent
   `map4`). Not yet walked: operator/higher-order application spines (the head is
   a leaf) and universe polymorphism (`Sort` levels are `map0` leaves); a
   registered head with no machine-readable class defaults to `map1`
   (override-refinable via the `Std.HashMap Name MapClass` override).
6. **File.** `ParamInfer.lean`.

---

## Registration attributes

| Attribute / clause | Registers | Consumed by | File |
|---|---|---|---|
| `@[param]` | a `RArrow PA PB c c'` witness lemma: `c ↦ (c', lemma)` in the persistent constant DB | `#transfer` / `translateAll` (`const` rule) | `ParamDB.lean` |
| `@[transfer]` | an `abstract-op = emitted-kernel` simp lemma (e.g. `a * b = bbFieldMul a b`) | `repr_transfer`, `transfer`'s leaf cascade, `transferConv` shape discovery, `transferSimpConv` | `Core.lean` |
| `@[hgcongr]` | a cross-head congruence lemma `R (f a..) (g b..)`, keyed on the head pair `(f, g)` + relation | `hgcongr` | `HGCongrInit.lean` |
| `@[grind =]` (dual-tag) | a realization square into `grind`'s rewrite DB | `grind`, `param_cc`'s closure leaf | `GrindIntegration.lean` |
| `deriving Param` / `@[derive Param]` | the constructor-wise lift `T.R_param` (+ `Param .map3 .map0` instance for non/uniform-recursive) | downstream uses of the generated relation/instance | `ParamDeriveHandler.lean` |
| `Trocq` aesop rule set | `transferGround` (safe apply) + `transferCore` (unsafe tactic) | `aesop (rule_sets := [Transfer])` | `AesopRuleSet.lean` (decl), `AesopIntegration.lean` (rules) |
| `RegisteredParam` instance | one `Param m n A B` witness at its strongest class (`(m,n)` an `outParam`) | `auto_weaken` | `ParamAutoWeaken.lean` |
| `TransferDom` instance | the domain `Param .map0 .map2a A A'` for a representation change | `param_transfer` / `transfer_auto` | `ParamTransfer.lean`, `ParamRetraction.lean` |

Notes:

* `@[param]` peels the `RArrow PA PB c c'` from the lemma type's last two of its
  eight application arguments; the lemma type must be a literal `RArrow …` (it is
  not `whnf`'d). The DB is cross-file persistent.
* `@[transfer]` is named `trocq` (not `repr`) to avoid clashing with `Repr.repr`.
* `@[hgcongr]` rejects a lemma with no varying-argument hypothesis. The diagonal
  pair `(f, f)` is exactly a `@[gcongr]`-shaped lemma, so `@[hgcongr]` subsumes
  the homogeneous case.
* `register_simp_attr` / `declare_aesop_rule_sets` / `initialize` env-extensions
  are invisible in their declaring file — each lives in a small module imported by
  its consumers (`Core.lean`, `AesopRuleSet.lean`, `HGCongrInit.lean`,
  `ParamDB.lean`).

---

## Tactic selection

| Given | Use |
|---|---|
| a fixed equation between two representations (cross-head op-tree) | `rcongr` (or `param_solve`) |
| a relatedness goal needing transitivity / context-hypothesis chaining | `param_cc` (or `param_solve`) |
| a goal that might need either descent or chaining (don't know which) | `param_solve` |
| cross-head congruence with attribute-tagged, relation-generic lemmas | `hgcongr` |
| transfer a `∀`-statement to another representation | `param_transfer` |
| transfer a `∀`-statement *or* an `R_arrow` `app`-goal, one entry | `transfer_auto` |
| synthesize the transferred *term* + its proof | `#transfer` |
| a `Param m n A B` witness at a specific level | `param_resolve` |
| a low-class `Param` goal from one strong registration | `auto_weaken` |
| close an equation/`Iff`-of-`∀` by binder traversal + registry leaf | `transfer` |
| rewrite one sub-term inside a larger goal | `transferConv` (typeclass proof) / `transferSimpConv` (simp proof) |
| compile a whole goal to emitted kernels | `repr_transfer` / `repr_transfer!` |
| close a transfer leaf equation by congruence closure | `grind` (with `@[grind =]` squares) |
| the `Param` lift of a data type | `deriving Param` |
| transfer a Hoare/`wp` triple between related programs | `triple_transfer` (via `RComp`) |

Two cautions that recur:

* **`gcongr` cannot do cross-head** (different head functions left vs right) — the
  reason `rcongr`/`hgcongr` exist (`GCongrProbe.lean`).
* **Over the encoding relation `param_cc`/`param_solve` overlap `grind`**, since
  `Related enc a b` is definitionally `enc a = b`; their independent value is for
  a non-equational relation. The descent/closure split is the distinction that
  survives that collapse.
