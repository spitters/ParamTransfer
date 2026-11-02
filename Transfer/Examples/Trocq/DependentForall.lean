/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Combinators.ParamForall

/-!
# The dependent-Π rule at the top level on a nontrivial family

The index relation is the graph of `not` on `Bool`, and the family is
`a ↦ Fin (a.toNat + 1)`, whose fibers differ in size across the index. Related fibers are
related by their values. `finForall` is the relation between the two dependent function
types at `(map4, map4)`, from a domain and a family at `(map3, map3)`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.Examples.Trocq.DependentForall

open Transfer.Param

/-- The family on the source index. -/
abbrev Src (a : Bool) : Type := Fin (a.toNat + 1)

/-- The family on the target index, reindexed along `not`. -/
abbrev Tgt (a' : Bool) : Type := Fin ((!a').toNat + 1)

/-- The index relation: the graph of `not`, at `map3` in both directions. -/
def notDom : Param .map3 .map3 Bool Bool where
  R a a' := (!a) = a'
  fwd := ⟨fun a => !a, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨fun a' => !a', fun a' a h => by subst h; exact Bool.not_not a',
    fun a' a (h : (!a) = a') => by subst h; simp⟩

/-- The fiber relation at a related pair of indices: equality of values. -/
def finFiber (a a' : Bool) (h : (!a) = a') : Param .map3 .map3 (Src a) (Tgt a') where
  R x y := x.val = y.val
  fwd := ⟨Fin.cast (by subst h; simp), fun _ _ e => by subst e; rfl,
    fun _ _ e => Fin.ext e⟩
  bwd := ⟨Fin.cast (by subst h; simp), fun _ _ e => by subst e; rfl,
    fun _ _ e => Fin.ext e.symm⟩

/-- The dependent function types are related at the top level in both directions. -/
def finForall : Param .map4 .map4 (∀ a, Src a) (∀ a', Tgt a') :=
  paramForallAt .map4 .map4 notDom finFiber

/-- The forward structure of `finForall`'s rule at the top level. -/
abbrev finForallFwd : Map4Has (R_forall (B := Src) (B' := Tgt) notDom finFiber) :=
  Map4_forall notDom finFiber

/-- The forward map reads the source function at the image of the index under `not`. -/
example (f : ∀ a, Src a) (a' : Bool) : (finForallFwd.map f a').val = (f (!a')).val := rfl

/-- The image of a function is related to it at an arbitrary related pair of indices: the
    field `map_in_R`, which reads the domain backward at `map3`. -/
example (f : ∀ a, Src a) (a a' : Bool) (h : (!a) = a') :
    (f a).val = (finForallFwd.map f a').val :=
  finForallFwd.map_in_R f _ rfl a a' h

/-- A function related to `f` is the image of `f`: the field `R_in_map`. -/
example (f : ∀ a, Src a) (g : ∀ a', Tgt a')
    (r : ∀ a a', (!a) = a' → (f a).val = (g a').val) : finForallFwd.map f = g :=
  finForallFwd.R_in_map f g r

end Transfer.Examples.Trocq.DependentForall
