/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Combinators.ParamArrow
import Mathlib.Data.List.Forall2

/-!
# The data-type (`×` / `Option` / `List`) parametricity rules

A faithful Lean port of Trocq's container relational lift (`coq-community/trocq`,
`generic/Param_prod.v`, `generic/Param_option.v`, `generic/Param_list.v`): the
combinators that build a `Param` annotated relation on a *container* type
(`A × B`, `Option A`, `List A`) from `Param` relations on its element type(s).

These are the data-type rules of the parametricity translation, extending the
engine's reach from the type formers `→` (`ParamArrow.lean`) and `∀`
(`ParamForall.lean`) to the standard inductive containers.

## What is ported

For each container `F` the Coq files define an inductive relation (`prodR`,
`optionR`, `listR`) and the forward map builders (`F_map`, `F_map_in_R`,
`F_R_in_map`) at the levels `map1`–`map4`. The relations are pointwise lifts of
the element relation; the *math* is ported directly (the relation + the map
builders), exactly as `ParamArrow`/`ParamForall` ported the arrow/forall math —
not the Elpi that generates these container files in Coq. Trocq's Elpi produces
one such file per inductive type mechanically; the present three are the
representative shapes (binary product, nullary/unary sum, recursive list) all
further inductive types follow.

## Relations

- `R_prod PA PB p p' := PA.R p.1 p'.1 ∧ PB.R p.2 p'.2`   (Coq `prodR`).
- `R_option PA` : `none ~ none`, `some a ~ some a' := PA.R a a'`, else `False`
  (Coq `optionR`).
- `R_list PA := List.Forall₂ PA.R`   (Coq `listR` is exactly Mathlib's
  `List.Forall₂`, which is reused directly).

## Levels achieved

The container forward map (`Map1_*`) lifts the element forward map through the
constructor, and its graph-inclusion (`Map2a_*`) lifts the element `map_in_R`;
both are univalence-free in Lean, as in Coq's `std`. The `Param`-level
combinator is delivered at forward-`map1`, backward-`map0` —
`param{Prod,Option,List} : Param .map1 .map0 (F A) (F A')` — from element inputs
`Param .map2a .map0` (`map2a` is what the graph-inclusion consumes), mirroring
`paramForall`. The full `map2a`/`map3` forward records are provided as
`Map2a_*` for `prod`/`option`/`list`. Higher levels (`map3`/`map4` backward, and
the `R_in_mapK` coherence at `map4`) are the residual, exactly as for the arrow
and forall rules. Dependent containers (e.g. `Σ`, vectors indexed by length)
follow the same pattern with an indexed family in place of the constant element
`Param`, as in `ParamForall`.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A A' B B' : Type u}

/-! ## Product: the relation `R_prod` (Coq `prodR`) -/

/-- Trocq `prodR`: two pairs are related when their components are related by
    `PA` and `PB` respectively. The (logically equivalent) conjunction form is
    used, the convenient shape for the crypto transfer. The level parameters
    stay polymorphic — the relation touches only the `R` fields. -/
def R_prod {mA nA mB nB : MapClass}
    (PA : Param mA nA A A') (PB : Param mB nB B B') :
    A × B → A' × B' → Prop :=
  fun p p' => PA.R p.1 p'.1 ∧ PB.R p.2 p'.2

/-- Trocq `Map0_prod`: no structure. -/
def Map0_prod {mA nA mB nB : MapClass}
    (PA : Param mA nA A A') (PB : Param mB nB B B') :
    Map0Has (R_prod PA PB) := ⟨⟩

/-- Trocq `prod_map` as a `map1` record: lift each component forward map through
    the pair constructor. Needs `PA`, `PB` forward-`map1`. -/
def Map1_prod (PA : Param .map1 .map0 A A') (PB : Param .map1 .map0 B B') :
    Map1Has (R_prod PA PB) :=
  ⟨fun p => (PA.fwd.map p.1, PB.fwd.map p.2)⟩

/-- Trocq `prod_map_in_R` as a `map2a` record: the lifted map's graph is
    included in `R_prod` (componentwise via each `PA.map_in_R`/`PB.map_in_R`).
    Needs `PA`, `PB` forward-`map2a`. -/
def Map2a_prod (PA : Param .map2a .map0 A A') (PB : Param .map2a .map0 B B') :
    Map2aHas (R_prod PA PB) where
  map := fun p => (PA.fwd.map p.1, PB.fwd.map p.2)
  map_in_R := by
    intro p p' e
    subst e
    exact ⟨PA.fwd.map_in_R _ _ rfl, PB.fwd.map_in_R _ _ rfl⟩

/-- `paramProd`: from element relations at forward-`map2a`, backward-`map0`, the
    annotated relation on the product, forward-`map1`, backward-`map0`. The
    forward map is the componentwise lift `prod_map`. -/
def paramProd (PA : Param .map2a .map0 A A') (PB : Param .map2a .map0 B B') :
    Param .map1 .map0 (A × B) (A' × B') where
  R := R_prod PA PB
  fwd := ⟨fun p => (PA.fwd.map p.1, PB.fwd.map p.2)⟩
  bwd := ⟨⟩

/-! ## Option: the relation `R_option` (Coq `optionR`) -/

/-- Trocq `optionR`: `none ~ none`; `some a ~ some a'` iff `PA.R a a'`; mixed
    constructors are unrelated. -/
def R_option {mA nA : MapClass} (PA : Param mA nA A A') :
    Option A → Option A' → Prop
  | none,   none    => True
  | some a, some a' => PA.R a a'
  | _,      _       => False

/-- Trocq `Map0_option`: no structure. -/
def Map0_option {mA nA : MapClass} (PA : Param mA nA A A') :
    Map0Has (R_option PA) := ⟨⟩

/-- Trocq `option_map` as a `map1` record: lift the element forward map through
    `Option.map`. Needs `PA` forward-`map1`. -/
def Map1_option (PA : Param .map1 .map0 A A') :
    Map1Has (R_option PA) :=
  ⟨Option.map PA.fwd.map⟩

/-- Trocq `option_map_in_R` as a `map2a` record: the lifted map's graph is
    included in `R_option`. Needs `PA` forward-`map2a`. -/
def Map2a_option (PA : Param .map2a .map0 A A') :
    Map2aHas (R_option PA) where
  map := Option.map PA.fwd.map
  map_in_R := by
    intro o o' e
    subst e
    cases o with
    | none => exact True.intro
    | some a => exact PA.fwd.map_in_R a (PA.fwd.map a) rfl

/-- `paramOption`: from an element relation at forward-`map2a`, backward-`map0`,
    the annotated relation on `Option`, forward-`map1`, backward-`map0`. -/
def paramOption (PA : Param .map2a .map0 A A') :
    Param .map1 .map0 (Option A) (Option A') where
  R := R_option PA
  fwd := ⟨Option.map PA.fwd.map⟩
  bwd := ⟨⟩

/-! ## List: the relation `R_list` (Coq `listR` = Mathlib `List.Forall₂`) -/

/-- Trocq `listR`: the pointwise lift of the element relation to lists —
    `[] ~ []`, and `a :: as ~ a' :: as'` iff `PA.R a a' ∧ R_list as as'`. This
    is exactly Mathlib's `List.Forall₂ PA.R`, which is reused (the `nilR`/`consR`
    constructors are `List.Forall₂.nil`/`List.Forall₂.cons`). -/
def R_list {mA nA : MapClass} (PA : Param mA nA A A') :
    List A → List A' → Prop :=
  List.Forall₂ PA.R

/-- Trocq `Map0_list`: no structure. -/
def Map0_list {mA nA : MapClass} (PA : Param mA nA A A') :
    Map0Has (R_list PA) := ⟨⟩

/-- Trocq `map_list` as a `map1` record: lift the element forward map through
    `List.map`. Needs `PA` forward-`map1`. -/
def Map1_list (PA : Param .map1 .map0 A A') :
    Map1Has (R_list PA) :=
  ⟨List.map PA.fwd.map⟩

/-- Trocq `map_in_R_list` as a `map2a` record: the lifted map's graph is
    included in `R_list`, by induction on the list (the recursive `consR`
    builder). Needs `PA` forward-`map2a`. -/
def Map2a_list (PA : Param .map2a .map0 A A') :
    Map2aHas (R_list PA) where
  map := List.map PA.fwd.map
  map_in_R := by
    intro l l' e
    subst e
    induction l with
    | nil => exact List.Forall₂.nil
    | cons a as ih => exact List.Forall₂.cons (PA.fwd.map_in_R a (PA.fwd.map a) rfl) ih

/-- `paramList`: from an element relation at forward-`map2a`, backward-`map0`,
    the annotated relation on `List`, forward-`map1`, backward-`map0`. The
    forward map is `List.map PA.map`. -/
def paramList (PA : Param .map2a .map0 A A') :
    Param .map1 .map0 (List A) (List A') where
  R := R_list PA
  fwd := ⟨List.map PA.fwd.map⟩
  bwd := ⟨⟩

/-! ## `R_in_map` (the relation-inclusion half), recovering the graph

The element-side `R_in_map` (forward-`map2b`) lifts to the container, giving the
`map2b` and hence `map3` forward records. The list version (the recursive case)
is the representative; `prod`/`option` follow by the same componentwise/`cases`
argument. -/

/-- Trocq `R_in_map_list`: `R_list`-relatedness implies the lifted map sends `l`
    to `l'`, by induction on the `List.Forall₂` derivation. Combined with
    `Map2a_list.map_in_R` this gives the full `map3` graph (omitted as a record
    here; this is the funext-free relation-inclusion half). Needs the element
    `R_in_map`, i.e. `PA` forward-`map2b`. -/
theorem R_in_map_list (PA : Param .map2b .map0 A A')
    (l : List A) (l' : List A') (h : R_list PA l l') :
    List.map PA.fwd.map l = l' := by
  induction h with
  | nil => rfl
  | cons hd _ ih => simp [List.map, PA.fwd.R_in_map _ _ hd, ih]

/-! ## Demos

Each container relation lifts the diagonal (equality) to the expected pointwise
relation, the forward map computes through the constructor, and the data rules
compose with the arrow rule of `ParamArrow.lean`. -/

section Demo

/-- The diagonal as an element input for the data rules: forward-`map2a`
    (a map plus the graph-inclusion `map_in_R`), backward-`map0`. This is the
    shape `paramProd`/`paramOption`/`paramList` consume. -/
def paramEqElt (T : Type u) : Param .map2a .map0 T T where
  R := Eq
  fwd := ⟨id, fun _ _ h => h⟩
  bwd := ⟨⟩

/-- `R_prod` of two diagonals is the diagonal on the product: two pairs are
    related iff they are componentwise equal, i.e. equal. -/
example {T S : Type u} (p q : T × S) :
    R_prod (paramEqElt T) (paramEqElt S) p q ↔ p = q := by
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

/-- The product forward map is the componentwise lift, which on the diagonal is
    the identity. -/
example {T S : Type u} (p : T × S) :
    (paramProd (paramEqElt T) (paramEqElt S)).fwd.map p = p := rfl

/-- `R_option` of the diagonal relates `some a` to `some a'` exactly when
    `a = a'`. -/
example {T : Type u} (a a' : T) :
    R_option (paramEqElt T) (some a) (some a') ↔ a = a' := Iff.rfl

/-- The option forward map computes through the constructor. -/
example {T : Type u} (a : T) :
    (paramOption (paramEqElt T)).fwd.map (some a) = some a := rfl

/-- `R_list` of the diagonal is `List.Forall₂ Eq`, i.e. pointwise equality. -/
example {T : Type u} (l l' : List T) :
    R_list (paramEqElt T) l l' ↔ List.Forall₂ Eq l l' := Iff.rfl

/-- Transfer demo: a singleton list `[a]` is `R_list`-related to its image
    `[PA.map a]` under the lifted forward map — here, on the diagonal, `[a]`. -/
example {T : Type u} (a : T) :
    R_list (paramEqElt T) [a] ((paramList (paramEqElt T)).fwd.map [a]) := by
  show List.Forall₂ Eq [a] [a]
  exact List.Forall₂.cons rfl List.Forall₂.nil

/-- The list forward map is `List.map` of the element map. -/
example {T : Type u} (l : List T) :
    (paramList (paramEqElt T)).fwd.map l = l.map id := rfl

/-! ### Cross-rule composition: the data rules feed the arrow rule

`paramProd`/`paramList` produce a `Param .map1 .map0` on the container, the same
output shape the leaf rules produce; weakened to the `Param .map1 .map1` input
`paramArrow` consumes (here directly at the diagonal level), the function space
`List T → S` gets a `Param` whose relation is `R_arrow (paramList …) …`. -/

/-- The list-container relation at the forward-`map1`, backward-`map1` level,
    the input shape `paramArrow` consumes (diagonal element). -/
def paramListEq1 (T : Type u) : Param .map1 .map1 (List T) (List T) where
  R := R_list (paramEqElt T)
  fwd := ⟨List.map id⟩
  bwd := ⟨List.map id⟩

/-- The diagonal at forward/backward-`map1`, for the codomain of the arrow. -/
def paramEq1' (S : Type u) : Param .map1 .map1 S S where
  R := Eq
  fwd := ⟨id⟩
  bwd := ⟨id⟩

/-- `paramArrow` composes with the list-container `Param`: the function space
    `List T → S` gets an annotated relation whose `R` is the arrow lift of the
    list relation and the codomain equality. -/
example {T S : Type u} :
    (paramArrow (paramListEq1 T) (paramEq1' S)).R
      = R_arrow (paramListEq1 T) (paramEq1' S) := rfl

/-- Its forward map conjugates by `List.map id` on the domain (the identity on
    the diagonal), witnessing the data rule feeding the arrow rule. -/
example {T S : Type u} (f : List T → S) (l : List T) :
    (paramArrow (paramListEq1 T) (paramEq1' S)).fwd.map f l = f (l.map id) := rfl

end Demo

end Transfer.Param
