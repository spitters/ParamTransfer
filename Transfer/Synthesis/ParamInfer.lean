/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Lean
import Transfer.Hierarchy.ParamLevel
import Transfer.Translate.ParamDB

/-!
# Variable-level minimal-class inference

`ParamSynth`/`ParamSynthExt` synthesize `Param` witnesses at a *fixed* menu of
levels; `ParamResolve.param_resolve` is a `first | …` macro with literally-written
candidate levels. Neither *infers* the level: they require the target `(m, n)` up
front and try a hardcoded list.

This module provides the constraint-graph minimal-class
solver, the Lean analogue of upstream Trocq's level-inference pass
(`coq-community/trocq`, paper §4.4): *"the [parametricity] class chosen must remain
a variable until the end; a reduction algorithm determines the minimal acceptable
class."* Each `Type`-occurrence gets a class variable whose value is determined
by least-fixpoint propagation over the `MapClass` lattice (`ParamLevel.lean`'s
proven `le`/`meet`), driven by the `arrowReq`/`forallReq` decision tables.

## Design (explicit constraint graph, not Lean metavariables)

The class of each occurrence is modeled as an explicit `Nat`-indexed
variable with a current lower bound in the lattice, not a Lean metavariable:

* `TyShape` — a simplified type structure (`base`/`arrow`/`forallT`) mirroring the
  `dep_→`/`dep_Π` cases the real constraint generator walks. Each node also carries
  an `optional user lower bound` (a registered witness available only at some class
  `c` forces that occurrence `≥ c`).
* `genConstraints` — assigns a fresh variable id to every node and emits, for each
  `arrow`/`forallT` node, the `arrowReq`/`forallReq`-derived constraints linking the
  node's variable to its children's, plus the user lower bounds.
* `solve` — least-fixpoint propagation: start every variable at `map0` (the lattice
  minimum), repeatedly raise any variable that a constraint demands be higher, until
  stable. The result is the minimal class per variable satisfying all constraints
  (unconstrained ⇒ `map0`).
* `inferParamLevels` — the entry point: `TyShape → (varId → MapClass)`.

`map4` is never selected by minimization: it is the lattice top, so the least
solution sits strictly below it whenever any solution exists — which is how
inference stays off the proven-inconsistent univalent level (`UnivalenceStatus`).

## Wiring (no change to `param_resolve`/`HasParam`)

A level-directed resolver would call `inferParamLevels` on the (shape-abstracted)
goal type, read off the minimal forward class `m` at the root occurrence, and then
invoke the existing `Param.weaken (by decide) … (inferInstance : HasParam …).param`
path at that `m` (the "synthesize-high, use-low" move `ParamWeaken` proves sound).
This module exposes the function and documents the consumption point; it does not
edit the resolver.

## The full-`Expr` front-end (`exprToTyShape`/`inferParamLevelsExpr`)

The `TyShape` core above is a *simplified* surface. The section "## Walking real
Lean `Expr`" below closes that residual: `exprToTyShape : Expr → MetaM TyShape`
walks an actual Lean type `Expr` — non-dependent `→` (an `arrow` node, `arrowReq`
arithmetic), dependent `Π` (a `forallT` node, `forallReq` arithmetic,
detected by `Expr.hasLooseBVar` on the body), and application/const heads (a `base`
leaf whose lower bound comes from the `@[param]` registry via `getParamDB`). It then
reuses the same `genFrom`/`solve` core — no new solver. `inferParamLevelsExpr`
and `inferRootClassExpr` are the `Expr` analogues of `inferParamLevels`/`inferRootClass`.

## Scope

The `Expr` walk covers: non-dependent arrows, dependent `Π` (instantiating the bound
variable with a fresh fvar), constant/application heads as leaves, and registry lower
bounds (a `@[param]`-registered head constant lifts its leaf to `map1`, the level
`paramOfMap` provides for any transferable representation; an explicit override table
refines this per name). It does not cover: higher-order/operator spines beyond a
const application head (the head is taken as the leaf; argument types are not
re-walked), universe polymorphism (sort levels are ignored — every `Sort`/`fvar`/`bvar`
is a `map0` leaf), or term-level `⟦t⟧` translation (that is `ParamTranslate`). The
registry path imposes only *presence*-driven bounds: the `RArrow` witnesses carry no
machine-readable `MapClass`, so an exact per-witness class is taken from the optional
override, defaulting to `map1` on registry hit. The minimizer is a least-fixpoint
solver over the proven lattice.
-/

set_option autoImplicit false

namespace Transfer.Param

open Std

/-! ## The simplified type shape (the constraint generator's input) -/

/-- A simplified type structure mirroring the `dep_→`/`dep_Π` cases of the real
    constraint generator. Each node optionally carries a user lower bound: a
    registered witness available only at class `c` forces that occurrence `≥ c`.
    `base` is a leaf (an opaque type occurrence); `arrow d c` is `d → c`;
    `forallT d c` is the dependent `∀`-spine `(a : d) → c`. -/
inductive TyShape
  | base (lb : Option MapClass)
  | arrow (dom cod : TyShape)
  | forallT (dom cod : TyShape)
  deriving Repr

/-- A `base` occurrence with no user lower bound (the common leaf). -/
def TyShape.leaf : TyShape := .base none

/-! ## Constraints over class variables

A class variable is a `Nat` id. A constraint is a *lower bound* demand on a
variable: `geq v c` forces `assignment v ≥ c` directly; `geqVar v w f` forces
`assignment v ≥ f (assignment w)` (a child-driven demand, where `f` is the
relevant projection of an `arrowReq`/`forallReq` table entry). All constraints are
monotone in the current assignment, which is what makes least-fixpoint propagation
converge to the minimal solution. -/

/-- A lower-bound constraint on class variables. -/
inductive Constraint
  /-- `assignment v ≥ c` (a fixed user/leaf lower bound). -/
  | geq (v : Nat) (c : MapClass)
  /-- `assignment v ≥ f (assignment w)` (a child-driven lattice demand). -/
  | geqVar (v w : Nat) (f : MapClass → MapClass)

/-! ## The lattice as a join-semilattice for fixpoint propagation

The lattice gives `meet` (greatest lower bound). Least-fixpoint
propagation raises variables, so it needs the join (least upper bound),
derived from the proven `le`: `join a b` is the `le`-smaller of the two that is
`≥` both, falling back up the chain. Since the only incomparable pair is
`map2a`/`map2b` (both `< map3`), their join is `map3`. -/

/-- The join (least upper bound) on `MapClass`. Total: the only incomparable pair
    `{map2a, map2b}` joins to `map3` (their least common upper bound). -/
def MapClass.join : MapClass → MapClass → MapClass
  | .map0, b => b
  | a, .map0 => a
  | .map1, b => b
  | a, .map1 => a
  | .map2a, .map2a => .map2a
  | .map2b, .map2b => .map2b
  | .map2a, .map2b => .map3
  | .map2b, .map2a => .map3
  | .map2a, .map3 => .map3
  | .map3, .map2a => .map3
  | .map2b, .map3 => .map3
  | .map3, .map2b => .map3
  | .map2a, .map4 => .map4
  | .map4, .map2a => .map4
  | .map2b, .map4 => .map4
  | .map4, .map2b => .map4
  | .map3, .map3 => .map3
  | .map3, .map4 => .map4
  | .map4, .map3 => .map4
  | .map4, .map4 => .map4

/-- The join is an upper bound (left). -/
theorem MapClass.le_join_left (a b : MapClass) : a ⊑ MapClass.join a b := by
  cases a <;> cases b <;> rfl
/-- The join is an upper bound (right). -/
theorem MapClass.le_join_right (a b : MapClass) : b ⊑ MapClass.join a b := by
  cases a <;> cases b <;> rfl

/-! ## Constraint generation

`genFrom n` annotates `TyShape` with fresh variable ids `≥ n` (a pre-order
traversal: the node itself gets `n`, then its children), returning the root's id,
the next free id, and the emitted constraints. For an `arrow`/`forallT` node, the
emitted constraints implement the `arrowReq`/`forallReq` tables:

* `arrow`: at output forward class `v`, the codomain's forward class is exactly the
  `arrowReq` codomain-forward slot `(.2.2.1)`. This is modeled as the codomain
  occurrence being driven by `v` through that table projection: `geqVar cod v fCod`
  where `fCod v := (arrowReq v).codFwd`. (The domain slot is a *backward* class,
  which the forward-only shape carries trivially as `map0`.)
* `forallT`: at output forward class `v`, the domain backward class is `forallReq v`
  — modeled as `geqVar dom v fDom` with `fDom v := forallReq v`.

A node's own user lower bound `lb` (on `base`) emits `geq id c`. -/

/-- The codomain-forward requirement of `arrowReq` as a total function: at output
    forward class `v`, the codomain occurrence must carry this forward class
    (`arrowReq v |>.2.2.1`). Defaults to `map0` only at the impossible `none` case,
    which `arrowReq` never returns. -/
def arrowCodFwd (v : MapClass) : MapClass :=
  match arrowReq v with
  | some (_, _, codFwd, _) => codFwd
  | none => .map0

/-- The inverse of `arrowCodFwd`: the *least* arrow output class whose
    `arrowReq` codomain-forward slot covers a given codomain demand `c` (i.e. the
    smallest `v` with `c ⊑ arrowCodFwd v`). This is what turns a codomain's lower
    bound into the root's lower bound — the table read "backwards", exactly Trocq's
    per-combinator level arithmetic. Computed by scanning the lattice in ascending
    order and taking the first class that suffices. `map4` is intentionally absent:
    no output class produces a `map4` codomain slot (`arrowReq map4` gives `map3`),
    so a `map4` demand is unreachable and minimization stays below the top. -/
def arrowRootFromCod (c : MapClass) : MapClass :=
  let ascending : List MapClass := [.map0, .map1, .map2a, .map2b, .map3, .map4]
  match ascending.find? (fun v => MapClass.le c (arrowCodFwd v)) with
  | some v => v
  | none   => .map4

/-- The domain (backward) requirement of `forallReq` as a total function (`map0`
    where the output is outside the univalence-free table — those outputs are never
    minimal). At output forward class `v`, the `∀`-domain must carry backward class
    `forallReq v`. -/
def forallDom (v : MapClass) : MapClass :=
  match forallReq v with
  | some d => d
  | none => .map0

/-- The inverse of `forallDom`: the least `∀` output class whose domain
    requirement covers a given domain demand `d`. Used to lift a domain's lower
    bound into the `∀`-root's lower bound. Only `{map0, map1}` are univalence-free
    outputs, so anything beyond a `map2a` domain demand is outside the safe fragment
    and pins to `map4` (never selected, since such a demand never arises in the
    univalence-free shapes). -/
def forallRootFromDom (d : MapClass) : MapClass :=
  let ascending : List MapClass := [.map0, .map1, .map2a, .map2b, .map3, .map4]
  match ascending.find? (fun v => MapClass.le d (forallDom v)) with
  | some v => v
  | none   => .map4

/-- Generate fresh ids `≥ start` and the constraint list for a `TyShape`. Returns
    `(rootId, nextFree, constraints)`. Each `arrow`/`forallT` node emits two
    constraints linking its variable `v` to a child's: the *downward* table read
    (`v` drives the child's required class) and the *upward* inverse read (a child's
    lower bound drives `v`). The upward edge is what propagates a registered leaf
    bound to the root; the downward edge keeps children consistent once the root is
    fixed. Both are monotone, so the least fixpoint is the minimal consistent
    assignment. -/
def genFrom : Nat → TyShape → (Nat × Nat × List Constraint)
  | start, .base lb =>
    let cs := match lb with
      | some c => [Constraint.geq start c]
      | none   => []
    (start, start + 1, cs)
  | start, .arrow dom cod =>
    let v := start
    let (_, n1, cd) := genFrom (start + 1) dom
    let (cid, n2, cc) := genFrom n1 cod
    -- downward: `v` requires codomain-forward class `arrowCodFwd v`;
    -- upward: codomain's class demands root ≥ `arrowRootFromCod codClass`.
    let edges := [Constraint.geqVar cid v arrowCodFwd,
                  Constraint.geqVar v cid arrowRootFromCod]
    (v, n2, edges ++ cd ++ cc)
  | start, .forallT dom cod =>
    let v := start
    let (did, n1, cd) := genFrom (start + 1) dom
    let (_, n2, cc) := genFrom n1 cod
    -- downward: `v` requires domain backward class `forallDom v`;
    -- upward: domain's class demands root ≥ `forallRootFromDom domClass`.
    let edges := [Constraint.geqVar did v forallDom,
                  Constraint.geqVar v did forallRootFromDom]
    (v, n2, edges ++ cd ++ cc)

/-- Total number of variables a shape allocates (its node count). -/
def TyShape.size : TyShape → Nat
  | .base _ => 1
  | .arrow d c => 1 + d.size + c.size
  | .forallT d c => 1 + d.size + c.size

/-! ## The assignment and the fixpoint solver

An assignment is a `varId → MapClass` map (defaulting unmentioned variables to
`map0`, the minimum). One propagation pass raises each variable by the join of its
current value and every constraint's demand. Iterating `size`-many passes reaches
the least fixpoint: each pass can only raise values (monotone), the lattice has
finite height ≤ 6, and there are `size` variables, so the chain stabilizes. -/

/-- An assignment of classes to variable ids; missing ⇒ `map0`. -/
abbrev Assign := HashMap Nat MapClass

/-- Read a variable's current class (default `map0`). -/
def Assign.get (a : Assign) (v : Nat) : MapClass :=
  a.getD v .map0

/-- The demand a single constraint places on the current assignment: the class the
    target variable must be `≥`. -/
def Constraint.demand (a : Assign) : Constraint → (Nat × MapClass)
  | .geq v c      => (v, c)
  | .geqVar v w f => (v, f (a.get w))

/-- One propagation pass: for every constraint, raise its target variable to the
    join of its current value and the constraint's demand. -/
def stepOnce (cs : List Constraint) (a : Assign) : Assign :=
  cs.foldl (fun acc con =>
    let (v, d) := con.demand a
    acc.insert v (MapClass.join (acc.get v) d)) a

/-- Iterate `stepOnce` `fuel` times. With `fuel ≥ size`, this reaches the least
    fixpoint (finite-height lattice, monotone passes). -/
def iterate (cs : List Constraint) : Nat → Assign → Assign
  | 0,         a => a
  | fuel + 1,  a => iterate cs fuel (stepOnce cs a)

/-- The minimal-class solver. From a constraint list and a variable count,
    least-fixpoint-propagate from the all-`map0` assignment. The result assigns each
    variable the *least* class satisfying every constraint. Fuel `= nVars * 6`
    (variables × lattice height) guarantees the fixpoint is reached. -/
def solve (nVars : Nat) (cs : List Constraint) : Assign :=
  iterate cs (nVars * 6) (∅ : Assign)

/-! ## The entry point -/

/-- Infer the minimal `MapClass` per occurrence of a `TyShape`. Generates the
    constraint graph and least-fixpoint-solves it. Returns `(rootId, assignment)`:
    `assignment.get rootId` is the minimal forward class the whole type requires; a
    level-directed resolver synthesizes at that class and `Param.weaken`s down. -/
def inferParamLevels (t : TyShape) : Nat × Assign :=
  let (rootId, nVars, cs) := genFrom 0 t
  (rootId, solve nVars cs)

/-- Convenience: the minimal forward class at the root occurrence of a `TyShape`. -/
def inferRootClass (t : TyShape) : MapClass :=
  let (rootId, a) := inferParamLevels t
  a.get rootId

/-! ## Demos

The three required scenarios. Each is a `#guard` (so it is *checked at elaboration*,
failing the build if the solver regresses), plus an `example` recording the value. -/

/-! ### (a) Unconstrained arrow ⇒ `map0` everywhere -/

/-- An unconstrained arrow `base → base`: no user lower bounds, so the root and both
    children minimize to `map0` (the lattice bottom — nothing forces structure). -/
def demoUnconstrained : TyShape := .arrow .leaf .leaf

-- Root infers `map0`.
#guard inferRootClass demoUnconstrained == MapClass.map0

-- Every occurrence infers `map0`: root (id 0), domain (id 1), codomain (id 2).
#guard
  let (_, a) := inferParamLevels demoUnconstrained
  (a.get 0 == .map0) && (a.get 1 == .map0) && (a.get 2 == .map0)

example : inferRootClass demoUnconstrained = .map0 := by native_decide

/-! ### (b) Arrow whose codomain has a `map3` lower bound ⇒ minimal class set by
`arrowReq`, not higher.

The codomain occurrence is registered at class `map3`. The codomain-forward demand
that propagates back to the root is `arrowCodFwd (root)`; the least root class whose
`arrowReq` codomain-forward slot is `≥ map3` is `map3` itself
(`arrowReq map3 = (map0, map3, map3, map0)`). So the root minimizes to exactly
`map3` — not `map4`. -/

/-- `base → base(map3)`: codomain forced to at least `map3`. -/
def demoCodMap3 : TyShape := .arrow .leaf (.base (some .map3))

-- The codomain (id 2) is at least its registered `map3`.
#guard
  let (_, a) := inferParamLevels demoCodMap3
  MapClass.le .map3 (a.get 2)

-- The root infers exactly `map3` — the minimal class whose `arrowReq` codomain slot
-- covers the `map3` demand — and not `map4`.
#guard inferRootClass demoCodMap3 == MapClass.map3

example : inferRootClass demoCodMap3 = .map3 := by native_decide

-- map4 is never selected by minimization (stays strictly below the lattice top).
#guard inferRootClass demoCodMap3 != MapClass.map4

/-! ### (c) Nested `∀`/`→` picks per-subterm minima (no global over-demand).

A `forallT` whose domain is unconstrained and whose codomain is an `arrow` with a
`map2a`-registered codomain. The inner arrow's root must cover the `map2a` demand
(minimal: `map2a`, since `arrowReq map2a = (map0, map2b, map2a, map0)`), while the
outer `∀`'s domain and the inner arrow's domain stay at `map0` — demonstrating the
solver minimizes *per subterm* rather than globally lifting everything. -/

/-- `∀ (_ : base). (base → base(map2a))`. -/
def demoNested : TyShape :=
  .forallT .leaf (.arrow .leaf (.base (some .map2a)))

-- Per-occurrence minima. Ids (pre-order): 0 = ∀-root, 1 = ∀-domain,
-- 2 = inner-arrow-root, 3 = inner-domain, 4 = inner-codomain.
-- inner codomain (id 4) ≥ its registered map2a; inner arrow root (id 2) minimizes
-- to exactly map2a; the unconstrained domains (ids 1, 3) stay at the bottom.
#guard
  let (_, a) := inferParamLevels demoNested
  (MapClass.le .map2a (a.get 4))
    && (a.get 2 == .map2a)
    && (a.get 1 == .map0) && (a.get 3 == .map0)

-- The inner arrow root is `map2a`, not lifted to `map3`/`map4`.
#guard
  let (_, a) := inferParamLevels demoNested
  (a.get 2 != .map3) && (a.get 2 != .map4)

example :
    let (_, a) := inferParamLevels demoNested
    a.get 2 = .map2a := by native_decide

/-! ## Monotone-correctness / termination notes (checked)

The solver is sound by construction on the lattice `ParamLevel.lean` proves: every
`stepOnce` raises variables by `join` (so the assignment only increases, and stays
the least that satisfies the constraints seen so far), and the iteration count
`nVars * 6` exceeds (variables × lattice height), so the fixpoint is reached. The
demos above `#guard` the minimal values directly; the following records that one
extra pass is a no-op at the fixpoint (idempotence), the operational face of
"least fixpoint reached". -/

-- At the solved fixpoint, one more `stepOnce` changes nothing at the root —
-- idempotence, the operational signature of a reached least fixpoint.
#guard
  let (rootId, nVars, cs) := genFrom 0 demoNested
  let a := solve nVars cs
  (stepOnce cs a).get rootId == a.get rootId

-- The join sends the incomparable pair to their least upper bound.
#guard MapClass.join .map2a .map2b == MapClass.map3

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
