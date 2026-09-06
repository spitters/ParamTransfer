/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import Transfer.Synthesis.ParamInfer
public import Transfer.Synthesis.ParamInfer
public meta import Transfer.Translate.ParamDB
public import Transfer.Translate.ParamDB
public import Lean

/-!
# Level inference over `Expr`

The elaboration-time half of `Transfer.Synthesis.ParamInfer`: the same level
inference, driven by a real `Expr` and the ambient `@[param]` registry rather
than by the pure `TyShape` datatype.

It lives in its own module because a `meta` definition may not reference a
plain declaration of its own module, while the pure half is consumed by
compiled `#guard` and `native_decide` tests. Importing that half with
`public meta import` makes it available here.
-/

public section

meta section

namespace Transfer.Param
/-! ## Walking real Lean `Expr` (the full-`Expr` front-end)

The `TyShape` API above acts on a simplified spine. This section provides the
front-end: a `MetaM` walk over an actual Lean type `Expr` that produces a `TyShape`,
which the existing `genFrom`/`solve` core then consumes unchanged. The walk:

* `Expr.forallE _ dom body _` with `body` not depending on the bound variable
  (checked by `Expr.hasLooseBVar body 0`) ⇒ a non-dependent `arrow` node (`arrowReq`
  arithmetic). Both `dom` and `body` are recursed.
* `Expr.forallE _ dom body _` with a genuine dependency ⇒ a dependent `forallT` node
  (`forallReq` arithmetic). The bound variable is instantiated with a fresh local
  (`withLocalDecl`) before recursing into the instantiated body, so loose bvars never
  escape into the recursion.
* a constant or an application whose head is a constant ⇒ a `base` leaf; its lower
  bound is the registry class of the head constant (see `constLB`).
* `Sort`/`fvar`/`bvar`/anything else ⇒ a `base none` leaf (minimum `map0`).

The class-bound resolver reflects the registry's information content: an
`RArrow PA PB c c'` witness records *that* a constant transfers, not at which
`MapClass` (no `MapClass` appears in `RArrow`). So a registered head gets the minimum
nonzero level `map1` (the `paramOfMap : Param map1 map0` any transferable
representation carries), and a caller may refine per-name via an explicit `override`
map. -/

open Lean Meta in
/-- The registry-driven lower bound for a head constant. Looks up `override` first
    (an explicit per-name class a caller can pin); otherwise, if the constant is in
    the ambient `@[param]` database (`getParamDB`), it carries at least `map1` (the
    forward-map level `paramOfMap` provides for any transferable representation);
    otherwise no bound (`none`, i.e. the `map0` minimum). -/
def constLB (override : Std.HashMap Lean.Name MapClass) (n : Lean.Name) :
    MetaM (Option MapClass) := do
  match override[n]? with
  | some c => return some c
  | none =>
    let db ← getParamDB
    match db.find? n with
    | some _ => return some .map1
    | none   => return none

open Lean Meta in
/-- Walk a real Lean type `Expr` into a `TyShape` (the full-`Expr` front-end).
    Non-dependent `→` ⇒ `arrow`; genuine dependent `Π` ⇒ `forallT` (bound variable
    instantiated with a fresh fvar before recursing); constant/application head ⇒
    `base` leaf with its registry lower bound; everything else ⇒ `base none`. The
    resulting `TyShape` is consumed by the unchanged `genFrom`/`solve` core. -/
partial def exprToTyShape (override : Std.HashMap Lean.Name MapClass) : Expr → MetaM TyShape
  | .forallE nm dom body bi => do
      if body.hasLooseBVar 0 then
        if dom.cleanupAnnotations.isSort then
          -- a polymorphic type-parameter binder (`∀ {α : Sort u}, … α …`): the
          -- type variable is carried along, transparent to class inference. The
          -- universe relation that would transfer `α` itself is the capped `map4`
          -- level, not inferred here, so the binder contributes no shape node — the
          -- binder is instantiated with a fresh local and the body walked alone.
          -- A universe-polymorphic declaration thus infers the same term-level
          -- arrow shape as its monomorphic instances.
          withLocalDecl nm bi dom fun x => exprToTyShape override (body.instantiate1 x)
        else
          -- genuine dependent Π over a value: instantiate the binder with a fresh
          -- local first.
          withLocalDecl nm bi dom fun x => do
            let domShape ← exprToTyShape override dom
            let codShape ← exprToTyShape override (body.instantiate1 x)
            return .forallT domShape codShape
      else
        -- non-dependent arrow `dom → body`.
        let domShape ← exprToTyShape override dom
        let codShape ← exprToTyShape override body
        return .arrow domShape codShape
  | e => do
      -- a leaf: constant or application head. Take the head; if it is a constant,
      -- read its registry lower bound. Sorts / fvars / bvars / other heads ⇒ `none`.
      match e.getAppFn.constName? with
      | some n => return .base (← constLB override n)
      | none   => return .base none

/-- Infer the minimal `MapClass` per occurrence of a real type `Expr`. Walks the
    `Expr` into a `TyShape` (registry-driven leaf bounds), then reuses the pure
    `inferParamLevels` core. Returns `(rootId, assignment)`. -/
def inferParamLevelsExpr (override : Std.HashMap Lean.Name MapClass) (e : Lean.Expr) :
    Lean.MetaM (Nat × Assign) := do
  let shape ← exprToTyShape override e
  return inferParamLevels shape

/-- Convenience: the minimal forward class at the root occurrence of a real type
    `Expr`. The `Expr` analogue of `inferRootClass`. -/
def inferRootClassExpr (override : Std.HashMap Lean.Name MapClass) (e : Lean.Expr) :
    Lean.MetaM MapClass := do
  let (rootId, a) ← inferParamLevelsExpr override e
  return a.get rootId

open Lean Meta in
/-- Infer minimal classes for a (possibly universe-polymorphic) declaration by
    name. Instantiates the declaration's universe parameters with fresh level
    metavariables, then walks the resulting type with `inferParamLevelsExpr`. This
    closes the "universe-polymorphic declarations are not walked" residual: the
    universe parameters are carried along (the polymorphic type binders are skipped
    by `exprToTyShape`), so the term-level arrow/`Π` structure infers exactly as it
    does for a monomorphic instance. The universe *relation* — relating `Type u` to
    `Type v` as objects — is the capped `map4` level and is not inferred. -/
def inferParamLevelsConst (override : Std.HashMap Lean.Name MapClass) (declName : Lean.Name) :
    MetaM (Nat × Assign) := do
  let ci ← getConstInfo declName
  let lvls ← ci.levelParams.mapM (fun _ => mkFreshLevelMVar)
  let ty := ci.instantiateTypeLevelParams lvls
  inferParamLevelsExpr override ty

open Lean Meta in
/-- The minimal forward class at the root of a (possibly universe-polymorphic)
    declaration's type. The by-name analogue of `inferRootClassExpr`. -/
def inferRootClassConst (override : Std.HashMap Lean.Name MapClass) (declName : Lean.Name) :
    MetaM MapClass := do
  let (rootId, a) ← inferParamLevelsConst override declName
  return a.get rootId

/-! ## Demos on real Lean type `Expr`s

Each `run_meta` block elaborates a Lean type via quotation, runs the
`Expr` front-end, and `logInfo`s the inferred root class; the output is pinned with
`#guard_msgs`, so a regression fails the build. The first uses the empty override (no
registry constants involved); the registered-constant demo pins a head via the
override table so the registry-lower-bound path applies deterministically. -/

open Lean Meta Elab Term in
/-- A type-elaboration helper: elaborate a `term` syntax to its `Expr`. -/
def elabTy (stx : Lean.TSyntax `term) : Lean.MetaM Lean.Expr :=
  TermElabM.run' (do
    let e ← elabTerm stx none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e)

-- (a) Non-dependent arrow `ℕ → ℕ` with no registered constants: an unconstrained
-- arrow, so the root infers `map0` — matching the `TyShape` `demoUnconstrained`.
/-- info: Expr ℕ → ℕ root class = Transfer.Param.MapClass.map0 -/
#guard_msgs in
open Lean in
run_meta do
  let e ← elabTy (← `(Nat → Nat))
  let c ← inferRootClassExpr ∅ e
  logInfo m!"Expr ℕ → ℕ root class = {repr c}"

-- (a') Nested non-dependent `ℕ → ℕ → Prop`: per-subterm minima, all unconstrained,
-- so the root still infers `map0` — no global over-demand.
/-- info: Expr ℕ → ℕ → Prop root class = Transfer.Param.MapClass.map0 -/
#guard_msgs in
open Lean in
run_meta do
  let e ← elabTy (← `(Nat → Nat → Prop))
  let c ← inferRootClassExpr ∅ e
  logInfo m!"Expr ℕ → ℕ → Prop root class = {repr c}"

-- (b) Genuine dependent `Π`: `∀ n : ℕ, n = n`. The body depends on the bound var,
-- so this is a `forallT` node. The domain (`ℕ`) is an unconstrained leaf, so the
-- `∀`-root minimizes to `map0` (forallReq map0 = map0; nothing forces the domain up).
/-- info: Expr (∀ n, n = n) root class = Transfer.Param.MapClass.map0 -/
#guard_msgs in
open Lean in
run_meta do
  let e ← elabTy (← `(∀ n : Nat, n = n))
  let c ← inferRootClassExpr ∅ e
  logInfo m!"Expr (∀ n, n = n) root class = {repr c}"

-- (c) The registry-lower-bound path. We model a type `D → ℕ` whose domain head `D`
-- is a registered `@[param]` constant pinned (via the override) at class `map3`.
-- The arrow's domain leaf is therefore forced to `map3`; the arrow root's forward
-- class is unaffected by a *domain* bound (arrowReq's domain slot is backward, so a
-- domain demand does not raise the root) — the root stays `map0`, while the domain
-- occurrence (id 1) carries the registered `map3`. To exercise the root-lifting
-- registry path, the second block puts the registered constant in the codomain.
/--
info: Expr (D → ℕ) root = Transfer.Param.MapClass.map0, domain (id 1) = Transfer.Param.MapClass.map3
-/
#guard_msgs in
open Lean in
run_meta do
  -- `Nat → True`, but pin the head `Nat` (domain leaf) at map3 via the override,
  -- standing in for a registered representation-changing constant.
  let e ← elabTy (← `(Nat → True))
  let ov : Std.HashMap Lean.Name MapClass :=
    (∅ : Std.HashMap _ _).insert ``Nat MapClass.map3
  let (_, a) ← inferParamLevelsExpr ov e
  logInfo m!"Expr (D → ℕ) root = {repr (a.get 0)}, domain (id 1) = {repr (a.get 1)}"

-- (c') Registered constant in the codomain lifts the arrow root. `True → Nat` with
-- the codomain head `Nat` pinned at `map3`: the codomain demand propagates back
-- through `arrowRootFromCod` and lifts the root to exactly `map3` (never `map4`).
/-- info: Expr (True → D) root class = Transfer.Param.MapClass.map3 (≠ map4) -/
#guard_msgs in
open Lean in
run_meta do
  let e ← elabTy (← `(True → Nat))
  let ov : Std.HashMap Lean.Name MapClass :=
    (∅ : Std.HashMap _ _).insert ``Nat MapClass.map3
  let c ← inferRootClassExpr ov e
  logInfo m!"Expr (True → D) root class = {repr c} (≠ map4)"

-- (2a) Universe-polymorphic declarations are walked. The polymorphic type
-- binder `{α : Type u}` is transparent to class inference, so `polyArrow.{u} :
-- ∀ {α}, α → α` walks to an `arrow` shape (the type binder is skipped, not a
-- `forallT` over a `map0` type domain), and `inferRootClassConst` infers the same
-- root class as the monomorphic `True → True`. `inferParamLevelsConst` instantiates
-- the universe parameters, so the declaration is reachable by name.
private def polyArrow.{u} {α : Type u} : α → α := fun a => a

/-- info: polyArrow: shape head = arrow, root = mono(True→True) root: true -/
#guard_msgs in
open Lean in
run_meta do
  let ci ← getConstInfo ``polyArrow
  let ty := ci.instantiateTypeLevelParams (ci.levelParams.map (fun _ => Level.zero))
  let shape ← exprToTyShape (∅ : Std.HashMap _ _) ty
  let head := match shape with
    | .arrow _ _ => "arrow" | .forallT _ _ => "forallT" | .base _ => "base"
  let cPoly ← inferRootClassConst (∅ : Std.HashMap _ _) ``polyArrow
  let cMono ← inferRootClassExpr (∅ : Std.HashMap _ _) (← elabTy (← `(True → True)))
  logInfo m!"polyArrow: shape head = {head}, root = mono(True→True) root: {decide (cPoly = cMono)}"

end Transfer.Param

