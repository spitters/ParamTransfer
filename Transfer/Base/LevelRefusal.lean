/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedAt

/-!
# The univalence-free refusal guard

The crux of the Trocq port is to compute, per subterm, the minimal `(m,n)`
relation level a goal needs, and — when that level is the equivalence top
(level `equiv`, where an equivalence is used as an equality) — refuse and
report rather than import univalence (UA), which would enlarge the TCB and is
in any case false for the (non-surjective) byte encodings.

That full per-subterm level inference is a separate, larger engine (Coq-Elpi →
Lean `MetaM`). This module provides the tractable, decidable guard it relies
on. The **primary form of the cap lives on the Trocq lattice**: the guard
refuses exactly the `map4` universe witness (`permittedMapClass` /
`classifyMapClass` — `map0`–`map3` is the univalence-free fragment, wider than
the 3-point view). The 3-point classification (`permitted` / `classify`) is
the view of that lattice guard through `RelLevel.toMapClass`
(`permitted_toMapClass` / `classify_toMapClass`), so refusing `equiv` is the
derived form of refusing `map4`. This guard makes the discipline enforceable
and distinguishes this cap from full Coq-Trocq.

## The discipline

The permitted `(m,n)` slice on the lattice is `map0`–`map3`; in the 3-point
view: `map` (transfers `=` forward), `embedding` (`+ injective`, transfers `=`
both ways), and the refused `equiv` (image `map4`). Between universes `map4`
needs univalence; a `∀` reaches `map4` from `map3` inputs (`Map4_forall`), so
the cap at `map3` is the choice of this fragment. The crypto encodings
(point/`Fp¹²`/word serializations) are embeddings that are not onto, so a
backward `∀` over one lacks the domain backward at `map3` and is declined.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.LevelRefusal

open Transfer

/-- **Primary.** The univalence-free slice of the Trocq lattice: a `MapClass`
    is permitted iff it is not the `map4` universe witness. `map0`–`map3` are
    univalence-free (the fragment wider than the 3-point view — `map2a`,
    `map2b` and `map3` are all permitted); only `map4` needs UA. -/
def permittedMapClass : Param.MapClass → Bool
  | .map4 => false
  | _ => true

/-- The univalence-free slice in the 3-point view: the lattice guard through
    `toMapClass`. `map` and `embedding` are univalence-free; `equiv` (image
    `map4`) needs UA. -/
def permitted (lvl : RelLevel) : Bool :=
  permittedMapClass lvl.toMapClass

/-- The 3-point guard is the view of the lattice guard (definitional). -/
theorem permitted_toMapClass (lvl : RelLevel) :
    permitted lvl = permittedMapClass lvl.toMapClass := rfl

/-- Old = new: the derived guard agrees with the original 3-point table
    (refuse exactly `equiv`). -/
theorem permitted_eq_old :
    ∀ lvl, permitted lvl = match lvl with | .equiv => false | _ => true := by
  intro lvl; cases lvl <;> rfl

/-- The lattice cap refuses **exactly** the `map4` universe witness. -/
theorem permittedMapClass_eq_false_iff (m : Param.MapClass) :
    permittedMapClass m = false ↔ m = .map4 := by
  cases m <;> simp [permittedMapClass]

/-- The outcome of classifying the level a (sub)goal needs: either a permitted
    univalence-free transfer at `lvl`, or a refusal carrying a report of why
    (which subterm forced the equivalence level). The full engine feeds
    `classify` the level it infers per subterm; this module supplies `classify`
    and the report, not the inference. -/
inductive TransferOutcome
  | /-- Transfer permitted at this (univalence-free) level. -/
    ok (lvl : RelLevel)
  | /-- Transfer refused: the goal needs `equiv` (equivalence-as-equality). -/
    refused (report : String)
  deriving DecidableEq, Repr

/-- **Primary.** Classify a needed lattice level: refuse exactly `map4`, the
    level outside the fragment `map0`–`map3`, reporting it; every level of the
    fragment is permitted at its 3-point view. The cap is a decision of the
    fragment. A relation between universes at `map4` turns an equivalence of
    types into an equality of types, which is univalence
    (`UnivalenceStatus.univalence_inconsistent`). A relation between values
    reaches `map4` from `map3` without it: the dependent-Π rule builds output
    `map4` from a domain and a family at `map3` (`Param.Map4_forall`). -/
def classifyMapClass : Param.MapClass → TransferOutcome
  | .map4 =>
      .refused
        "transfer needs level `map4` (3-point view `equiv`), and the \
         univalence-free fragment stops at `map3`. Between universes, `map4` \
         is equivalence-as-equality and would need univalence. Between values, \
         a `∀` reaches `map4` from `map3` inputs without univalence \
         (`Param.Map4_forall`); the guard refuses `map4` there as well."
  | m => .ok m.view3

/-- Classify a needed level: the lattice classifier through `toMapClass` —
    refuses exactly the equivalence top (image `map4`), reporting it. -/
def classify (lvl : RelLevel) : TransferOutcome :=
  classifyMapClass lvl.toMapClass

/-- The 3-point classifier is the view of the lattice classifier
    (definitional). -/
theorem classify_toMapClass (lvl : RelLevel) :
    classify lvl = classifyMapClass lvl.toMapClass := rfl

/-- The lattice classifier refuses **exactly** the `map4` universe witness. -/
theorem classifyMapClass_refused_iff (m : Param.MapClass) :
    (∃ r, classifyMapClass m = .refused r) ↔ m = .map4 := by
  cases m <;> simp [classifyMapClass]

/-- The wider-than-3-point fragment is permitted at the lattice level: a
    two-sided graph relation (`map3`) classifies as an `embedding`-view
    transfer, not a refusal. -/
theorem classifyMapClass_map3_ok :
    classifyMapClass .map3 = .ok .embedding := rfl

/-! ## The guard is correct and decidable -/

/-- `map` is permitted (forward equation transfer needs no UA). -/
theorem classify_map : classify .map = .ok .map := rfl

/-- `embedding` is permitted (both-ways equation transfer via injectivity — the
    level at which the crypto encodings, and the `Num ↪ ℕ` transfer, live). -/
theorem classify_embedding : classify .embedding = .ok .embedding := rfl

/-- `equiv` is refused with a report — the univalence-free cap. -/
theorem classify_equiv_refused :
    ∃ r, classify .equiv = .refused r := ⟨_, rfl⟩

/-- `classify` permits a level iff `permitted` says so — the guard and the
    classifier agree, by cases on the three levels. -/
theorem permitted_iff_not_refused (lvl : RelLevel) :
    permitted lvl = true ↔ ∀ r, classify lvl ≠ .refused r := by
  cases lvl <;>
    simp [permitted, permittedMapClass, classify, classifyMapClass,
      RelLevel.toMapClass]

/-- The guard is decidable (it is `Bool`-valued), so the engine can branch on it
    without classical choice. -/
example (lvl : RelLevel) : Decidable (permitted lvl = true) := inferInstance

/-! ## A minimal-level inferencer over a goal-shape model

The classifier above takes the needed level as given and only classifies it. This
inferencer computes the level from a small, hand-rolled goal-shape AST and feeds
the inferred level to `classify`, so `classify` is reached with `equiv` when the
shape forces it rather than when a level is supplied. A shape whose backward `∀`
lacks its domain input is refused with the missing input level named
(`LevelNeed.lacks`).

This is a minimal model. It walks a `GoalShape` — a small model of the cases the
level discipline turns on — not a real `Expr`. The full engine traverses a Lean
`Expr`, threads `RelatedAt` annotations through binders, and is a larger
`MetaM` port (no Lean precedent). The contribution here is the direction of
dataflow: level ← shape, then refuse-or-permit.

### The modeling decisions

* A leaf is an equation whose carrier encoding has some `RelLevel` and a
  `surjective : Bool` flag. The flag distinguishes an embedding that is onto (so
  the backward direction is free) from a non-surjective encoding (the crypto
  case: a point/`Fp¹²`/word serialization that is injective but not onto, so the
  reverse needs UA).
* A forward `∀` (`forallFwd`) transfers in the `map` direction only: it adds
  no strength, so `inferLevel (forallFwd d) = inferLevel d`.
* A backward `∀` (`forallBwd`) asks for output level
  `max (level of d) embedding`, whose image `t` in the lattice is `map3` or
  `map4`. The dependent-Π rule then needs the domain backward at `forallReq t`
  (`Param.forallReq`, which is `map3` at both). The backward level a domain
  carries is `bwdAvail`: an onto leaf carries its forward level, a leaf that is
  not onto carries `map0` (no decoder, as for `Param.paramOfEmbedding`), and a
  composite domain is taken to carry `map3`.
  - When `forallReq t ⊑ bwdAvail d` the shape needs the output level.
  - Otherwise `inferLevel` returns `lacks (forallReq t) (bwdAvail d)`: the
    domain input the rule lacks and the level the domain carries. For the
    crypto encodings (injective, not onto) this is `lacks map3 map0`.
  - A `lacks` of the domain propagates.
* A composite (`compose a b`) supports only its weakest part, so two needed
  levels meet (`RelLevel.meet`); a part that lacks an input drops out when the
  other part needs a level, and two lacking parts report the first.

`inferAndClassify` hands a needed level to `classify` and turns `lacks` into a
refusal that names the missing input level.
-/

/-- A tiny goal-shape AST: the cases the minimal-level inferencer reasons about.
    A model of the level discipline rather than a real `Expr` (the full engine
    walks `Expr`; this drives the dataflow level ← shape). -/
inductive GoalShape
  | /-- An equation at a leaf whose carrier encoding has level `carrierLevel`;
        `surjective` records whether that encoding is onto (so the backward
        direction is free) — `false` is the crypto case (injective, not onto). -/
    leafEq (carrierLevel : RelLevel) (surjective : Bool)
  | /-- A `∀` transferred in the forward (`map`) direction: adds no strength. -/
    forallFwd (dom : GoalShape)
  | /-- A `∀` needing the backward direction over `dom`: needs at least
        `embedding`, and the domain backward at `Param.forallReq` of that level. -/
    forallBwd (dom : GoalShape)
  | /-- A composite: level is the `meet` (weakest) of the parts. -/
    compose (a b : GoalShape)
  deriving Repr

/-- The maximum (stronger) of two levels — dual to `RelLevel.meet`; a backward
    `∀` needs at least `embedding`, so it takes the `max` with `embedding`. -/
def maxLevel (l₁ l₂ : RelLevel) : RelLevel :=
  if l₁.toNat ≤ l₂.toNat then l₂ else l₁

/-- The backward level a shape carries as the domain of a backward `∀`: an onto
    leaf carries its forward level, a leaf that is not onto carries `map0` (no
    decoder), and a composite domain is taken to carry `map3`. -/
def bwdAvail : GoalShape → Param.MapClass
  | .leafEq l true => l.toMapClass
  | .leafEq _ false => .map0
  | _ => .map3

/-- The result of level inference: the level a shape needs, or the domain input
    level a backward `∀` lacks together with the level the domain carries. -/
inductive LevelNeed
  | /-- The shape needs this level. -/
    needs (lvl : RelLevel)
  | /-- The dependent-Π rule needs the domain backward at `input`; the domain
        carries only `avail`. -/
    lacks (input avail : Param.MapClass)
  deriving DecidableEq, Repr

/-- Infer the minimal level a shape needs, or the input level the `∀` rule
    lacks. See the section docstring above for the modeling decisions behind
    each clause. -/
def inferLevel : GoalShape → LevelNeed
  | .leafEq l _ => .needs l
  | .forallFwd d => inferLevel d
  | .forallBwd d =>
      match inferLevel d with
      | .needs l =>
          let out := maxLevel l .embedding
          let req := Param.forallReq out.toMapClass
          if Param.MapClass.le req (bwdAvail d) then .needs out
          else .lacks req (bwdAvail d)
      | .lacks r a => .lacks r a
  | .compose a b =>
      match inferLevel a, inferLevel b with
      | .needs la, .needs lb => .needs (RelLevel.meet la lb)
      | .needs la, .lacks _ _ => .needs la
      | .lacks _ _, .needs lb => .needs lb
      | .lacks r av, .lacks _ _ => .lacks r av

/-- The end-to-end guard: infer the level the shape needs, then refuse or
    permit it. A needed level goes to `classify`; a lacking input is refused
    with a report that names the input level and the level available. -/
def inferAndClassify (s : GoalShape) : TransferOutcome :=
  match inferLevel s with
  | .needs l => classify l
  | .lacks r a =>
      .refused
        s!"the dependent-Π rule needs the domain backward at `{repr r}`; the \
          domain carries `{repr a}` (an encoding that is not onto has no \
          decoder)."

/-- The label of a lacking input is correct: it is the domain level
    `Param.forallReq` asks for at some output level, and the domain does not
    carry it. -/
theorem inferLevel_lacks_spec (s : GoalShape) (r a : Param.MapClass)
    (h : inferLevel s = .lacks r a) :
    (∃ t, r = Param.forallReq t) ∧ Param.MapClass.le r a = false := by
  induction s generalizing r a with
  | leafEq l b => simp [inferLevel] at h
  | forallFwd d ih => exact ih r a h
  | forallBwd d ih =>
    simp only [inferLevel] at h
    split at h
    · split at h
      · cases h
      · rename_i hle
        cases h
        exact ⟨⟨_, rfl⟩, by simpa using hle⟩
    · rename_i hd
      cases h
      exact ih _ _ hd
  | compose x y ihx ihy =>
    simp only [inferLevel] at h
    split at h
    · cases h
    · cases h
    · cases h
    · rename_i hx _
      cases h
      exact ihx _ _ hx

/-! ## The inferencer is exercised end-to-end -/

/-- A plain embedding equation (e.g. a `Num ↪ ℕ` leaf) infers `embedding` and is
    permitted. -/
theorem inferAndClassify_leaf_embedding :
    inferAndClassify (.leafEq .embedding true) = .ok .embedding := rfl

/-- A leaf at `map` (forward-only) is permitted at `map`. -/
theorem inferAndClassify_leaf_map :
    inferAndClassify (.leafEq .map true) = .ok .map := rfl

/-- A forward `∀` over an embedding leaf still infers `embedding` and is
    permitted — the forward direction adds no strength. -/
theorem inferAndClassify_forallFwd_embedding :
    inferAndClassify (.forallFwd (.leafEq .embedding true)) = .ok .embedding :=
  rfl

/-- A backward `∀` over a surjective embedding leaf is still permitted at
    `embedding` — the reverse direction is available because the leaf is onto. -/
theorem inferAndClassify_forallBwd_surjective :
    inferAndClassify (.forallBwd (.leafEq .embedding true)) = .ok .embedding :=
  rfl

/-- A backward `∀` over an embedding leaf that is not onto (the crypto encoding
    case) is refused. -/
theorem inferAndClassify_forallBwd_nonsurjective_refused :
    ∃ r, inferAndClassify (.forallBwd (.leafEq .embedding false)) = .refused r :=
  ⟨_, rfl⟩

/-- The refused shape lacks the domain backward at `map3`; the leaf carries
    `map0`. -/
theorem inferLevel_forallBwd_nonsurjective :
    inferLevel (.forallBwd (.leafEq .embedding false)) = .lacks .map3 .map0 := rfl

/-- A composite drops to the weaker level: composing a `map` leaf with an
    `embedding` leaf infers `map` (the meet), and is permitted at `map`. -/
theorem inferAndClassify_compose_meet :
    inferAndClassify (.compose (.leafEq .map true) (.leafEq .embedding true))
      = .ok .map := rfl

/-- A composite of a `map` leaf and a backward `∀` that lacks its domain input
    needs `map`, the level of the part that has one, and is permitted at `map`. -/
theorem inferAndClassify_compose_rescues :
    inferAndClassify
      (.compose (.leafEq .map true) (.forallBwd (.leafEq .embedding false)))
      = .ok .map := rfl

/-- `inferAndClassify` is decidable end-to-end (it reduces to `Bool`-valued
    `permitted` via `classify`), so the engine branches on it without choice. -/
example (s : GoalShape) : Decidable (inferAndClassify s = inferAndClassify s) :=
  inferInstance

/-! ## What this module is not

The inferencer above is a minimal model over a hand-rolled `GoalShape`; the level it
computes follows the discipline (forward adds nothing; backward over a
non-surjective embedding lacks the domain backward at `map3`; composites meet), but the full engine
walks a real `Expr`, threads `RelatedAt` levels through actual binders, and
infers the least level that makes the whole transfer go through. That
level-annotated parametricity translation is the heart of the Trocq paper and
a larger `MetaM` port (no Lean precedent). The `RelatedAt` kernel carries
the level; the `transfer` tactic traverses binders; the minimal-level solver over
`Expr` is not implemented here. The contribution here is the
dataflow direction: the level is computed and fed to `classify` rather than
supplied. -/

end Transfer.LevelRefusal
