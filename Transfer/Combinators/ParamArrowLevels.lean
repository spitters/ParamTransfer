/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Hierarchy.ParamLevel
public import Transfer.Combinators.ParamArrow

/-!
# The level table of the arrow rule on relations

`arrowDomReq` and `arrowCodReq` project the domain and codomain requirements out of `arrowReq`,
and `mapHasLiftFun` is the arrow rule dispatched on the output level, stated on relations.

## Main definitions

* `Variance.arrowDomReq`, `Variance.arrowCodReq`: the position and value requirements of the
  arrow rule at an output level.
* `Variance.mapHasLiftFun`: structure of `Relator.LiftFun PR VR` at every level from structure of
  `symRel PR` at `arrowDomReq t` and of `VR` at `arrowCodReq t`.

## Tags

parametricity, arrow rule, Trocq levels
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Transfer.Param.Variance

/-- The position requirement of the arrow rule at an output level: the backward level of the
domain in `arrowReq`. -/
def arrowDomReq (t : MapClass) : MapClass := ((arrowReq t).map fun r => r.2.1).getD .map0

/-- The value requirement of the arrow rule at an output level: the forward level of the
codomain in `arrowReq`. -/
def arrowCodReq (t : MapClass) : MapClass := ((arrowReq t).map fun r => r.2.2.1).getD .map0

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

end Transfer.Param.Variance
