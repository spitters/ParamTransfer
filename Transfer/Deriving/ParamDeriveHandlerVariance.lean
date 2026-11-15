/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public meta import Transfer.Deriving.ParamDeriveHandler
public import Transfer.Deriving.ParamDeriveHandler
public import Transfer.Deriving.ParamDerive
public import Transfer.Combinators.ParamArrow
public import Transfer.Combinators.ParamForall
public import Transfer.Hierarchy.ParamWeaken
public import Transfer.Synthesis.ParamInfer
public import Lean.Meta.Constructions.CasesOn
public import Lean.Meta.Constructions.RecOn

/-!
# The bridge relation of inductives with mixed variance, indices and reflexive fields

The deriving handler of `ParamDeriveHandler.lean` generates the relation `T.R_param` and a
`Param .map3 .map0` instance for inductives whose parameters occur covariantly, without indices,
and with recursion that is uniform or nested under `List`. This file is a second `Param` deriving
handler for the inductives outside that fragment. It computes the bridge of an inductive in the
sense of Narya: the relation with the same constructors over the bridges of the fields, where the
bridge of a field type is its parametricity translation. A field of type `D → C` is related by
the function relation of the bridges of `D` and `C`, a parameter by the supplied relation, the
inductive itself by the relation being defined, a type former with a derived `R_param` by that
relation, `List` by `List.Forall₂`, and a parameter-free type by equality (heterogeneous equality
when its two copies mention different fields, such as `Fin n` and `Fin n'`). An indexed family
gets a relation indexed by pairs of indices.

Variance matters only for the levels. The levels of the derived relation follow from the
occurrences of each parameter: at output forward level `t`, a positive occurrence asks for the
forward structure of the parameter at the level of the arrow rule, a negative occurrence the
backward structure at `arrowDomReq t`. A parameter with both kinds of occurrence therefore needs a
two-sided `Param m n`.

## Main definitions

* `Variance.VShape`: the occurrence shape of a field type.
* `Variance.mkVarianceRelDecl`: the kernel declaration of the relation `T.R_param` and the
  occurrence shapes of the constructor fields.
* `Variance.inductiveReq`, `Variance.paramReq`: the level of each parameter required for an
  output level of the derived relation, one direction and both directions.
* `Variance.mkVarianceHandler`: the deriving handler, registered for `Param`. On an inductive in
  the fragment of the existing handler it returns `false`, so that handler runs.
* `Variance.mapHasLiftFun`, `Variance.mapHasOfIso`, `Variance.mapHasEq`: the level rules on
  relations used by the level theorems.

## Main results

* `Variance.EndoV.mapHas`, `Variance.EndoV.paramAt`: the record `{f : A → A}` with mixed variance
  has `MapHas t` from `Param (arrowCodReq t) (arrowDomReq t)`, and `Param t s` from the join of
  the two directions.
* `Variance.Sel.mapHas`: the record `{g : (A → Bool) → A}` has `MapHas t` from the forward
  structure alone, since a doubly negative occurrence is positive.
* `Variance.FinVec.mapHas`: the `Fin n`-indexed family has `MapHas t` at each index.
* `Variance.EndoV.levels`, `Variance.Sel.levels`, `Variance.FinVec.levels`: the level table
  computed from the occurrence shapes is the one these definitions use.

## Scope

Accepted: mixed and contravariant parameters, parameters under arrows and dependent function
types, indexed families, reflexive fields (`Nat → T A`), recursion under `List` and under a type
former with a derived relation. Declined with an error: mutual inductives, parameters that are not
types or whose types depend on other parameters, a recursive occurrence at other parameters, and
a parameter under a type former with no derived relation.

## References

* Altenkirch, Kaposi, Shulman, Üsküplü, *From parametricity to identity types* (TYPES 2025), and
  the Narya proof assistant: bridges of inductive families.
* Cohen, Crance, Mahboubi, *Trocq: Proof Transfer for Free, With or Without Univalence*
  (ESOP 2024): the level hierarchy and the arrow rule.

## Tags

parametricity, deriving handler, bridge, variance, contravariant, indexed family, reflexive
inductive, Trocq levels, map0 relation
-/

@[expose] public section

set_option autoImplicit false

open Lean Meta Elab Command Term

universe u

namespace Transfer.Param.Variance

/-! ## Occurrence shapes and the level table -/

/-- The occurrence shape of a field type, read by the level computation. -/
inductive VShape
  /-- A type that mentions no parameter and not the inductive: related by equality. -/
  | free
  /-- The `i`-th parameter. -/
  | param (idx : Nat)
  /-- The inductive itself at its parameters. -/
  | self
  /-- A non-dependent function type. -/
  | arrow (dom cod : VShape)
  /-- A dependent function type. -/
  | pi (dom cod : VShape)
  /-- A covariant type former (`List`, or a type with a derived relation) at its arguments. -/
  | cont (args : List VShape)
  deriving Repr, Inhabited, BEq

/-- The position requirement of the arrow rule at an output level: the backward level of the
domain in `arrowReq`. -/
def arrowDomReq (t : MapClass) : MapClass := ((arrowReq t).map fun r => r.2.1).getD .map0

/-- The value requirement of the arrow rule at an output level: the forward level of the
codomain in `arrowReq`. -/
def arrowCodReq (t : MapClass) : MapClass := ((arrowReq t).map fun r => r.2.2.1).getD .map0

/-- The requirement of no structure on any of `k` parameters. -/
def reqBot (k : Nat) : List (MapClass × MapClass) := List.replicate k (.map0, .map0)

/-- The pointwise join of two requirement lists. -/
def reqJoin (u v : List (MapClass × MapClass)) : List (MapClass × MapClass) :=
  List.zipWith (fun p q => (p.1.join q.1, p.2.join q.2)) u v

mutual
/-- The forward and backward level of each of `k` parameters that an occurrence of shape `s`
asks for at output level `t`, read positively when `pos` holds. A negative occurrence asks for
the backward structure; the domain of an arrow is read at `arrowDomReq t` with the polarity
flipped. A recursive occurrence asks nothing beyond the other fields. -/
def VShape.req (k : Nat) : VShape → MapClass → Bool → List (MapClass × MapClass)
  | .free, _, _ => reqBot k
  | .param i, t, pos => (reqBot k).set i (if pos then (t, .map0) else (.map0, t))
  | .self, _, _ => reqBot k
  | .arrow d c, t, pos => reqJoin (d.req k (arrowDomReq t) !pos) (c.req k (arrowCodReq t) pos)
  | .pi d c, t, pos => reqJoin (d.req k (forallReq t) !pos) (c.req k (forallFiberReq t) pos)
  | .cont ss, t, pos => VShape.reqList k ss t pos

/-- The join of `VShape.req` over a list of shapes. -/
def VShape.reqList (k : Nat) : List VShape → MapClass → Bool → List (MapClass × MapClass)
  | [], _, _ => reqBot k
  | s :: ss, t, pos => reqJoin (s.req k t pos) (VShape.reqList k ss t pos)
end

/-- The level of each of `k` parameters that output forward level `t` of the derived relation
asks for, given the occurrence shapes of the fields of each constructor. -/
def inductiveReq (k : Nat) (ctors : List (List VShape)) (t : MapClass) :
    List (MapClass × MapClass) :=
  ctors.foldr (fun fs acc => reqJoin (VShape.reqList k fs t true) acc) (reqBot k)

/-- The two-sided level of each parameter for `Param t s` of the derived relation: the forward
requirement at `t` joined with the flipped requirement at `s`. -/
def paramReq (k : Nat) (ctors : List (List VShape)) (t s : MapClass) :
    List (MapClass × MapClass) :=
  List.zipWith (fun p q => (p.1.join q.2, p.2.join q.1))
    (inductiveReq k ctors t) (inductiveReq k ctors s)

/-! ## The relation builder -/

/-- The data the relation builder carries: the inductive, the relation name, the universe
levels, the left and right parameter copies and the parameter relations. -/
structure RelCtx where
  /-- The inductive. -/
  self : Name
  /-- The name of the derived relation. -/
  relName : Name
  /-- The universe levels of the inductive. -/
  lvls : List Level
  /-- The left parameters. -/
  as : Array Expr
  /-- The right parameters. -/
  as' : Array Expr
  /-- The relations between the parameters. -/
  ps : Array Expr

/-- The relation applied to its parameters. -/
def RelCtx.relHead (c : RelCtx) : Expr :=
  mkAppN (mkConst c.relName c.lvls) (c.as ++ c.as' ++ c.ps)

/-- Does `e` mention a left parameter or the inductive? -/
def RelCtx.mentions (c : RelCtx) (e : Expr) : Bool :=
  e.hasAnyFVar (fun f => c.as.any (·.fvarId! == f)) || (e.find? (·.isConstOf c.self)).isSome

mutual
/-- The bridge of the field type `ty` (left copy) and `ty'` (right copy) at the elements `x`
and `x'`, with its occurrence shape. -/
partial def relOf (c : RelCtx) (ty ty' x x' : Expr) : MetaM (Expr × VShape) := do
  let ty ← instantiateMVars ty
  let ty' ← instantiateMVars ty'
  if !c.mentions ty then
    if ty == ty' then return (← mkEq x x', .free) else return (← mkHEq x x', .free)
  if let some j := c.as.findIdx? (· == ty) then
    return (mkApp2 c.ps[j]! x x', .param j)
  match ty, ty' with
  | .forallE n d b _, .forallE _ d' b' _ =>
    withLocalDeclD n d fun y => withLocalDeclD (n.appendAfter "'") d' fun y' => do
      let (hd, sd) ← relOf c d d' y y'
      withLocalDeclD `h hd fun hy => do
        let (hb, sb) ←
          relOf c (b.instantiate1 y) (b'.instantiate1 y') (mkApp x y) (mkApp x' y')
        let shape := if b.hasLooseBVars then VShape.pi sd sb else VShape.arrow sd sb
        return (← mkForallFVars #[y, y', hy] hb, shape)
  | _, _ =>
    let fn := ty.getAppFn
    let args := ty.getAppArgs
    let args' := ty'.getAppArgs
    let k := c.as.size
    if fn.isConstOf c.self then
      for j in [:k] do
        unless args[j]? == some c.as[j]! do
          throwError "derive Param (variance): a recursive occurrence of {c.self} is applied \
            to other parameters"
      let idx := args.extract k args.size
      let idx' := args'.extract k args'.size
      return (mkAppN c.relHead (idx ++ idx' ++ #[x, x']), .self)
    -- The applications below are built directly, since the bridge of a nested occurrence
    -- mentions the relation under construction, which `mkAppM` cannot type.
    if fn.isConstOf ``List && args.size == 1 then
      let (l, s) ← relLam c args[0]! args'[0]!
      let u := (← getLevel args[0]!).dec.getD Level.zero
      let v := (← getLevel args'[0]!).dec.getD Level.zero
      return (mkAppN (mkConst ``List.Forall₂ [u, v]) #[args[0]!, args'[0]!, l, x, x'],
        .cont [s])
    if let .const F ls := fn then
      let relF := F ++ `R_param
      if (← getEnv).contains relF then
        let np := (← getConstInfoInduct F).numParams
        let mut lams : Array Expr := #[]
        let mut ss : List VShape := []
        for i in [:np] do
          let (l, s) ← relLam c args[i]! args'[i]!
          lams := lams.push l
          ss := ss ++ [s]
        let app := mkAppN (mkConst relF ls) (args.extract 0 np ++ args'.extract 0 np ++ lams ++
          args.extract np args.size ++ args'.extract np args'.size ++ #[x, x'])
        return (app, .cont ss)
    let ty₁ ← whnfR ty
    if ty₁ != ty then
      return ← relOf c ty₁ (← whnfR ty') x x'
    throwError "derive Param (variance): a parameter of {c.self} occurs under {fn}, which has \
      no derived relation"

/-- The bridge of `a` and `a'` as a binary relation, eta-reduced. -/
partial def relLam (c : RelCtx) (a a' : Expr) : MetaM (Expr × VShape) :=
  withLocalDeclD `y a fun y => withLocalDeclD `y' a' fun y' => do
    let (r, s) ← relOf c a a' y y'
    return ((← mkLambdaFVars #[y, y'] r).eta, s)
end

/-- Introduce the binders of `ty` as implicit local variables, with primed names when `prime`
holds, and pass them on. -/
partial def withImplicitBinders {α : Type} (ty : Expr) (prime : Bool)
    (k : Array Expr → MetaM α) (acc : Array Expr := #[]) : MetaM α :=
  match ty with
  | .forallE n d b _ =>
    withLocalDecl (if prime then n.appendAfter "'" else n) .implicit d fun x =>
      withImplicitBinders (b.instantiate1 x) prime k (acc.push x)
  | _ => k acc

/-- The type of the constructor of the relation for the constructor `ctor`, from the left and
right instances `lt`, `rt` of its type: each field pair with the bridge of its type, concluding
the relation between the two constructor applications. Returns the occurrence shapes too. -/
partial def ctorFields (c : RelCtx) (ctor : Name) (lt rt : Expr)
    (xs xs' binders : Array Expr) (shapes : Array VShape) : MetaM (Expr × Array VShape) := do
  match lt, rt with
  | .forallE n d b _, .forallE _ d' b' _ =>
    withLocalDecl n .implicit d fun x => withLocalDecl (n.appendAfter "'") .implicit d' fun x' => do
      let (h, s) ← relOf c d d' x x'
      withLocalDeclD (n.appendBefore "h_") h fun hx =>
        ctorFields c ctor (b.instantiate1 x) (b'.instantiate1 x') (xs.push x) (xs'.push x')
          (binders ++ #[x, x', hx]) (shapes.push s)
  | _, _ =>
    let k := c.as.size
    let la := lt.getAppArgs
    let ra := rt.getAppArgs
    let lhs := mkAppN (mkConst ctor c.lvls) (c.as ++ xs)
    let rhs := mkAppN (mkConst ctor c.lvls) (c.as' ++ xs')
    let concl :=
      mkAppN c.relHead (la.extract k la.size ++ ra.extract k ra.size ++ #[lhs, rhs])
    return (← mkForallFVars binders concl, shapes)

/-- Make the first `n` binders of the telescope `e` implicit. -/
def implicitBinders : Nat → Expr → Expr
  | n + 1, .forallE x d b _ => .forallE x d (implicitBinders n b) .implicit
  | _, e => e

/-- The kernel declaration of the bridge relation `T.R_param` of the inductive `T`, with the
occurrence shapes of the fields of each constructor. The relation takes the left and right
parameters (implicit), a relation per parameter, the left and right indices (implicit) and the
two elements. -/
def mkVarianceRelDecl (declName : Name) : MetaM (Declaration × List (List VShape)) := do
  let iv ← getConstInfoInduct declName
  unless iv.all.length == 1 do
    throwError "derive Param (variance): {declName} is mutual"
  let k := iv.numParams
  let lvls := iv.levelParams.map mkLevelParam
  let relName := declName ++ `R_param
  -- The parameter binders: each a type whose type mentions no other parameter.
  let mut binders : Array (Name × Expr) := #[]
  let mut ty := iv.type
  for _ in [:k] do
    let .forallE n d b _ := ty | throwError "derive Param (variance): malformed type"
    unless !d.hasLooseBVars && d.isSort do
      throwError "derive Param (variance): the parameter {n} of {declName} is not a type"
    binders := binders.push (n, d)
    ty := b
  let leftDecls := binders.map fun (n, d) => (n, BinderInfo.implicit, fun _ => pure d)
  let rightDecls := binders.map fun (n, d) =>
    (n.appendAfter "'", BinderInfo.implicit, fun _ => pure d)
  withLocalDecls leftDecls fun as => withLocalDecls rightDecls fun as' => do
    let relDecls ← (Array.range k).mapM fun i => do
      let rt ← mkArrow as[i]! (← mkArrow as'[i]! (mkSort .zero))
      return ((Name.mkSimple s!"P{i}"), BinderInfo.default, fun (_ : Array Expr) => pure rt)
    withLocalDecls relDecls fun ps => do
      let c : RelCtx := { self := declName, relName, lvls, as, as', ps }
      let params := as ++ as' ++ ps
      let tyL ← instantiateForall iv.type as
      let tyR ← instantiateForall iv.type as'
      let rType ← withImplicitBinders tyL false fun idx =>
          withImplicitBinders tyR true fun idx' => do
        let tL := mkAppN (mkConst declName lvls) (as ++ idx)
        let tR := mkAppN (mkConst declName lvls) (as' ++ idx')
        withLocalDeclD `x tL fun x => withLocalDeclD `x' tR fun x' =>
          mkForallFVars (params ++ idx ++ idx' ++ #[x, x']) (mkSort .zero)
      let mut ctors : List Constructor := []
      let mut shapes : List (List VShape) := []
      for cn in iv.ctors do
        let ci ← getConstInfoCtor cn
        let lt ← instantiateForall ci.type as
        let rt ← instantiateForall ci.type as'
        let (cty, sh) ← ctorFields c cn lt rt #[] #[] #[] #[]
        let short := cn.componentsRev.head!
        let full := implicitBinders (3 * k) (← mkForallFVars params cty)
        ctors := ctors ++ [{ name := relName ++ short, type := full }]
        shapes := shapes ++ [sh.toList]
      let decl := Declaration.inductDecl iv.levelParams (3 * k)
        [{ name := relName, type := rType, ctors }] false
      return (decl, shapes)

/-- The occurrence shapes of the fields of each constructor of `declName`. -/
def shapeOf (declName : Name) : MetaM (List (List VShape)) :=
  return (← mkVarianceRelDecl declName).2

/-- Add the bridge relation `T.R_param` of `declName` to the environment, with its `casesOn`
and `recOn`. -/
def deriveVariance (declName : Name) : CommandElabM Unit := liftTermElabM do
  let (decl, _) ← mkVarianceRelDecl declName
  addDecl decl
  let relName := declName ++ `R_param
  mkCasesOn relName
  mkRecOn relName

/-! ## Registration as a second `Param` deriving handler -/

/-- Is every field of every constructor of `declName` in the fragment of the existing handler: a
parameter, the inductive at its parameters, `List` of that, or a closed type? -/
def fieldsInExistingFragment (declName : Name) : MetaM Bool := do
  let iv ← getConstInfoInduct declName
  for cn in iv.ctors do
    let ci ← getConstInfoCtor cn
    let ok ← forallTelescopeReducing ci.type fun xs _ => do
      let pfids := (xs.extract 0 ci.numParams).map (·.fvarId!)
      for i in [:ci.numFields] do
        let ty ← inferType xs[ci.numParams + i]!
        let isParam := ty.isFVar && pfids.contains ty.fvarId!
        let isSelf := isSelfAppliedToParams declName pfids ty
        let isList := ty.isAppOf ``List && ty.getAppArgs.size == 1 &&
          isSelfAppliedToParams declName pfids ty.getAppArgs[0]!
        unless isParam || isSelf || isList || !ty.hasFVar && !mentions declName ty do
          return false
      return true
    unless ok do return false
  return true

/-- Does the existing handler `mkParamInstanceHandler` derive `declName`? It does on a
non-mutual inductive without indices or reflexive fields whose fields lie in its fragment. -/
def existingHandles (declName : Name) : CommandElabM Bool := do
  let .inductInfo iv ← getConstInfo declName | return false
  if iv.isReflexive || iv.numIndices != 0 || iv.all.length != 1 then return false
  try
    let d ← liftTermElabM (toIndDesc declName)
    if iv.isNested && !isNestedListSupported d then return false
    liftTermElabM (fieldsInExistingFragment declName)
  catch _ => return false

/-- The second `Param` deriving handler. It returns `false` when the existing handler derives
every given inductive; otherwise it derives the bridge relation of each inductive outside that
fragment and passes the others to the existing handler. -/
def mkVarianceHandler (declNames : Array Name) : CommandElabM Bool := do
  let mut mine : Array Name := #[]
  for n in declNames do
    let some (.inductInfo _) := (← getEnv).find? n | return false
    unless ← existingHandles n do mine := mine.push n
  if mine.isEmpty then return false
  for n in declNames do
    if mine.contains n then
      deriveVariance n
    else
      unless ← mkParamInstanceHandler #[n] do
        throwError "derive Param: the existing handler declined {n}"
  return true

initialize
  registerDerivingHandler ``Param mkVarianceHandler

/-! ## Level rules on relations -/

/-- The arrow rule at every output level, on relations: `Map_k_arrow` dispatched on the level. -/
def mapHasLiftFun {D D' V V' : Type u} {PR : D → D' → Prop} {VR : V → V' → Prop} :
    (t : MapClass) → MapHas (arrowDomReq t) (symRel PR) → MapHas (arrowCodReq t) VR →
      MapHas t (Relator.LiftFun PR VR)
  | .map0, _, _ => (⟨⟩ : Map0Has _)
  | .map1, hP, hV => Map1_arrow (⟨PR, ⟨⟩, hP⟩ : Param .map0 .map1 D D') ⟨VR, hV, ⟨⟩⟩
  | .map2a, hP, hV => Map2a_arrow (⟨PR, ⟨⟩, hP⟩ : Param .map0 .map2b D D') ⟨VR, hV, ⟨⟩⟩
  | .map2b, hP, hV => Map2b_arrow (⟨PR, ⟨⟩, hP⟩ : Param .map0 .map2a D D') ⟨VR, hV, ⟨⟩⟩
  | .map3, hP, hV => Map3_arrow (⟨PR, ⟨⟩, hP⟩ : Param .map0 .map3 D D') ⟨VR, hV, ⟨⟩⟩
  | .map4, hP, hV => Map4_arrow (⟨PR, ⟨⟩, hP⟩ : Param .map0 .map3 D D') ⟨VR, hV, ⟨⟩⟩

/-- Equality has structure of every level, with the identity map. -/
def mapHasEq {X : Type u} : (t : MapClass) → MapHas t (@Eq X)
  | .map0 => (⟨⟩ : Map0Has _)
  | .map1 => (⟨id⟩ : Map1Has _)
  | .map2a => (⟨id, fun _ _ h => h⟩ : Map2aHas _)
  | .map2b => (⟨id, fun _ _ h => h⟩ : Map2bHas _)
  | .map3 => (⟨id, fun _ _ h => h, fun _ _ h => h⟩ : Map3Has _)
  | .map4 => (⟨id, fun _ _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩ : Map4Has _)

/-- The flipped equality has structure of every level. -/
def mapHasEqSymm {X : Type u} (t : MapClass) : MapHas t (symRel (@Eq X)) :=
  MapHas.ofIff (fun _ _ => eq_comm) t (mapHasEq t)

/-- Structure of a relation `S` transports to a relation `R` that is `S` read through maps
`e`, `e'`, when `e'` has a two-sided inverse `d'`. -/
def mapHasOfIso {X X' Y Y' : Type u} (e : X → Y) (e' : X' → Y') (d' : Y' → X')
    (hd : ∀ y, e' (d' y) = y) (hd' : ∀ x, d' (e' x) = x)
    {R : X → X' → Prop} {S : Y → Y' → Prop} (h : ∀ x x', R x x' ↔ S (e x) (e' x')) :
    (t : MapClass) → MapHas t S → MapHas t R
  | .map0, _ => (⟨⟩ : Map0Has _)
  | .map1, hS => (⟨fun x => d' ((hS : Map1Has S).map (e x))⟩ : Map1Has _)
  | .map2a, hS =>
    let hS : Map2aHas S := hS
    (⟨fun x => d' (hS.map (e x)), fun x x' hx => by
      subst hx
      exact (h _ _).2 (by rw [hd]; exact hS.map_in_R _ _ rfl)⟩ : Map2aHas _)
  | .map2b, hS =>
    let hS : Map2bHas S := hS
    (⟨fun x => d' (hS.map (e x)), fun x x' hx => by
      rw [hS.R_in_map _ _ ((h _ _).1 hx), hd']⟩ : Map2bHas _)
  | .map3, hS =>
    let hS : Map3Has S := hS
    (⟨fun x => d' (hS.map (e x)), fun x x' hx => by
      subst hx
      exact (h _ _).2 (by rw [hd]; exact hS.map_in_R _ _ rfl), fun x x' hx => by
      rw [hS.R_in_map _ _ ((h _ _).1 hx), hd']⟩ : Map3Has _)
  | .map4, hS =>
    let hS : Map4Has S := hS
    (⟨fun x => d' (hS.map (e x)), fun x x' hx => by
      subst hx
      exact (h _ _).2 (by rw [hd]; exact hS.map_in_R _ _ rfl), fun x x' hx => by
      rw [hS.R_in_map _ _ ((h _ _).1 hx), hd'], fun _ _ _ => rfl⟩ : Map4Has _)

/-! ## Test inductives -/

/-- A record with a field `A → A`: the parameter occurs with both variances. -/
structure EndoV (A : Type) where
  /-- The endomap. -/
  f : A → A

/-- A record with a field `(A → Bool) → A`: the parameter occurs positively and doubly
negatively. -/
structure Sel (A : Type) where
  /-- The selection function. -/
  g : (A → Bool) → A

set_option inductive.autoPromoteIndices false in
/-- A `Fin n`-indexed family of functions, with `n` an index. -/
inductive FinVec (A : Type) : Nat → Type
  | mk {n : Nat} (f : Fin n → A) : FinVec A n

/-- Length-indexed lists: an indexed recursive family. -/
inductive VecV (A : Type) : Nat → Type
  | nil : VecV A 0
  | cons {n : Nat} (a : A) (v : VecV A n) : VecV A (n + 1)

/-- Trees with countable branching: a reflexive inductive. -/
inductive WTree (A : Type) where
  | leaf (a : A) : WTree A
  | node (k : Nat → WTree A) : WTree A

/-- Rose trees whose labels are endomaps: nested under `List` with a mixed parameter. -/
inductive EndoRose (A : Type) where
  | node (f : A → A) (cs : List (EndoRose A)) : EndoRose A

run_cmd do
  for n in [``EndoV, ``Sel, ``FinVec, ``VecV, ``WTree, ``EndoRose] do
    deriveVariance n

/-- The occurrence shapes of `EndoV`. -/
def endoVShape : List (List VShape) := [[.arrow (.param 0) (.param 0)]]

/-- The occurrence shapes of `Sel`. -/
def selShape : List (List VShape) := [[.arrow (.arrow (.param 0) .free) (.param 0)]]

/-- The occurrence shapes of `FinVec`. -/
def finVecShape : List (List VShape) := [[.free, .arrow .free (.param 0)]]

run_cmd liftTermElabM do
  guard ((← shapeOf ``EndoV) == endoVShape)
  guard ((← shapeOf ``Sel) == selShape)
  guard ((← shapeOf ``FinVec) == finVecShape)

run_cmd do
  unless (← existingHandles ``Transfer.Param.Tree) do throwError "Tree"
  unless (← existingHandles ``Transfer.Param.ElGamalCt) do throwError "ElGamalCt"
  for n in [``EndoV, ``Sel, ``FinVec, ``VecV, ``WTree, ``EndoRose] do
    if (← existingHandles n) then throwError "{n}"

/-! ## Levels of the derived relations -/

/-- The level table of `EndoV`: forward structure at the codomain level, backward structure at
the domain level, joined over the two directions. -/
theorem EndoV.levels (t s : MapClass) :
    paramReq 1 endoVShape t s =
      [((arrowCodReq t).join (arrowDomReq s), (arrowDomReq t).join (arrowCodReq s))] := by
  cases t <;> cases s <;> rfl

/-- The derived relation of `EndoV` is the function relation of the field. -/
theorem EndoV.r_iff {A A' : Type} (P : A → A' → Prop) (u : EndoV A) (v : EndoV A') :
    EndoV.R_param P u v ↔ Relator.LiftFun P P u.f v.f := by
  constructor
  · rintro ⟨h⟩
    exact fun a a' haa => h a a' haa
  · intro h
    exact .mk (fun a a' haa => h haa)

/-- `EndoV` at output level `t` from a parameter with forward structure `arrowCodReq t` and
backward structure `arrowDomReq t`. -/
def EndoV.mapHas (t : MapClass) {A A' : Type} (P : Param (arrowCodReq t) (arrowDomReq t) A A') :
    MapHas t (EndoV.R_param P.R) :=
  mapHasOfIso EndoV.f EndoV.f EndoV.mk (fun _ => rfl) (fun _ => rfl) (EndoV.r_iff P.R) t
    (mapHasLiftFun t P.bwd P.fwd)

/-- `EndoV` as a two-sided `Param t s` from a parameter at the levels of `EndoV.levels`. -/
def EndoV.paramAt (t s : MapClass) {A A' : Type}
    (P : Param ((arrowCodReq t).join (arrowDomReq s)) ((arrowDomReq t).join (arrowCodReq s))
      A A') :
    Param t s (EndoV A) (EndoV A') where
  R := EndoV.R_param P.R
  fwd := EndoV.mapHas t ⟨P.R, forgetMapHas _ _ (MapClass.le_join_left _ _) P.fwd,
    forgetMapHas _ _ (MapClass.le_join_left _ _) P.bwd⟩
  bwd := MapHas.ofIff (R := EndoV.R_param (symRel P.R))
    (fun u v => (EndoV.r_iff _ u v).trans
      (Iff.trans ⟨fun h _ _ haa => h haa, fun h _ _ haa => h haa⟩ (EndoV.r_iff P.R v u).symm)) s
    (EndoV.mapHas s ⟨symRel P.R, forgetMapHas _ _ (MapClass.le_join_right _ _) P.bwd,
      forgetMapHas _ _ (MapClass.le_join_right _ _) P.fwd⟩)

/-- The level table of `Sel`: forward structure only, at the codomain level. -/
theorem Sel.levels (t : MapClass) : inductiveReq 1 selShape t = [(arrowCodReq t, .map0)] := by
  cases t <;> rfl

/-- The derived relation of `Sel` is the function relation of the field. -/
theorem Sel.r_iff {A A' : Type} (P : A → A' → Prop) (u : Sel A) (v : Sel A') :
    Sel.R_param P u v ↔ Relator.LiftFun (Relator.LiftFun P Eq) P u.g v.g := by
  constructor
  · rintro ⟨h⟩
    exact fun y y' hy => h y y' (fun a a' haa => hy haa)
  · intro h
    exact .mk (fun y y' hy => h (fun a a' haa => hy a a' haa))

/-- A doubly negative occurrence asks no more than the positive one. -/
theorem arrowDomReq_arrowDomReq_le (t : MapClass) :
    MapClass.le (arrowDomReq (arrowDomReq t)) (arrowCodReq t) = true := by
  cases t <;> rfl

/-- `Sel` at output level `t` from a parameter with forward structure `arrowCodReq t`. -/
def Sel.mapHas (t : MapClass) {A A' : Type} (P : Param (arrowCodReq t) .map0 A A') :
    MapHas t (Sel.R_param P.R) :=
  mapHasOfIso Sel.g Sel.g Sel.mk (fun _ => rfl) (fun _ => rfl) (Sel.r_iff P.R) t
    (mapHasLiftFun t
      (MapHas.ofIff (R := Relator.LiftFun (symRel P.R) (symRel (@Eq Bool)))
        (fun _ _ => ⟨fun h _ _ haa => h haa, fun h _ _ haa => h haa⟩) (arrowDomReq t)
        (mapHasLiftFun (arrowDomReq t)
          (forgetMapHas _ _ (arrowDomReq_arrowDomReq_le t) P.fwd) (mapHasEqSymm _)))
      P.fwd)

/-- The level table of `FinVec`: forward structure only, at the codomain level. -/
theorem FinVec.levels (t : MapClass) :
    inductiveReq 1 finVecShape t = [(arrowCodReq t, .map0)] := by
  cases t <;> rfl

/-- The function of a `FinVec`. -/
def FinVec.get {A : Type} {n : Nat} : FinVec A n → Fin n → A
  | .mk f => f

/-- At equal indices the derived relation of `FinVec` is the function relation of the field. -/
theorem FinVec.r_iff {A A' : Type} (P : A → A' → Prop) (n : Nat) (u : FinVec A n)
    (v : FinVec A' n) :
    FinVec.R_param P u v ↔ Relator.LiftFun (@Eq (Fin n)) P u.get v.get := by
  cases u
  cases v
  constructor
  · rintro ⟨_, h⟩
    exact fun i i' hi => h i i' (heq_of_eq hi)
  · intro h
    exact .mk rfl (fun i i' hi => h (eq_of_heq hi))

/-- `FinVec` at index `n` and output level `t` from a parameter with forward structure
`arrowCodReq t`. -/
def FinVec.mapHas (t : MapClass) (n : Nat) {A A' : Type} (P : Param (arrowCodReq t) .map0 A A') :
    MapHas t (fun (u : FinVec A n) (v : FinVec A' n) => FinVec.R_param P.R u v) :=
  mapHasOfIso FinVec.get FinVec.get FinVec.mk (fun _ => rfl) (fun x => by cases x; rfl)
    (FinVec.r_iff P.R n) t (mapHasLiftFun t (mapHasEqSymm _) P.fwd)

/-! ## Examples -/

/-- A parameter under `Option`, which has no derived relation. -/
inductive OptEndo (A : Type) where
  | mk (o : Option (A → A)) : OptEndo A

/-- error: derive Param (variance): a parameter of Transfer.Param.Variance.OptEndo occurs under
Option, which has no derived relation -/
#guard_msgs in
run_cmd deriveVariance ``OptEndo

/-- Two length-indexed lists are related elementwise. -/
example {A A' : Type} (P : A → A' → Prop) (a : A) (a' : A') (h : P a a') :
    VecV.R_param P (VecV.cons a VecV.nil) (VecV.cons a' VecV.nil) :=
  .cons rfl h .nil

/-- Two countably branching trees are related when their branches are related at equal
indices. -/
example {A A' : Type} (P : A → A' → Prop) (a : A) (a' : A') (h : P a a') :
    WTree.R_param P (WTree.node fun _ => .leaf a) (WTree.node fun _ => .leaf a') :=
  .node (fun _ _ _ => .leaf h)

/-- Two rose trees of endomaps are related when the labels are related as functions. -/
example {A A' : Type} (P : A → A' → Prop) (f : A → A) (f' : A' → A')
    (h : ∀ a a', P a a' → P (f a) (f' a')) :
    EndoRose.R_param P (EndoRose.node f []) (EndoRose.node f' []) :=
  .node h .nil

/-- The identity relation of `EndoV` at level `map3` both ways transports along `castViaParam`. -/
example : castViaParam (EndoV.paramAt .map3 .map3 (paramId Nat)) ⟨Nat.succ⟩ = ⟨Nat.succ⟩ :=
  rfl

end Transfer.Param.Variance
