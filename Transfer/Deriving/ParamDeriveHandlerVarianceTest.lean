/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public meta import Transfer.Deriving.ParamDeriveHandlerVariance
public import Transfer.Deriving.ParamDeriveHandlerVariance

/-!
# Tests of the two `Param` deriving handlers

`deriving Param` clauses on inductives inside and outside the fragment of the handler of
`ParamDeriveHandler.lean`. The handler of `ParamDeriveHandlerVariance.lean` derives the bridge
relation `T.R_param` of a mixed-variance record, an indexed family and a reflexive inductive, and
passes a covariant record to the first handler, which derives `T.param_instance` as well.

## Tags

deriving handler, parametricity, bridge, variance, indexed family, test
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.Param.VarianceTest

/-- A record with a field `A → A`. -/
structure EndoT (A : Type) where
  /-- The endomap. -/
  f : A → A
  deriving Param

/-- Length-indexed lists. -/
inductive VecT (A : Type) : Nat → Type
  | nil : VecT A 0
  | cons {n : Nat} (a : A) (v : VecT A n) : VecT A (n + 1)
  deriving Param

/-- Trees with countable branching. -/
inductive WTreeT (A : Type) where
  | leaf (a : A) : WTreeT A
  | node (k : Nat → WTreeT A) : WTreeT A
  deriving Param

/-- A covariant record, in the fragment of the first handler. -/
structure PairT (A B : Type) where
  /-- The first component. -/
  fst : A
  /-- The second component. -/
  snd : B

/-- A record with a field `(A → Bool) → A`. -/
structure SelT (A : Type) where
  /-- The selection function. -/
  g : (A → Bool) → A

deriving instance Param for PairT, SelT

/-- The derived relation of `EndoT` relates endomaps that preserve the parameter relation. -/
example {A A' : Type} (P : A → A' → Prop) (f : A → A) (f' : A' → A')
    (h : ∀ a a', P a a' → P (f a) (f' a')) : EndoT.R_param P ⟨f⟩ ⟨f'⟩ :=
  .mk h

/-- The derived relation of `VecT` is indexed by pairs of lengths. -/
example {A A' : Type} (P : A → A' → Prop) (a : A) (a' : A') (h : P a a') :
    VecT.R_param P (VecT.cons a VecT.nil) (VecT.cons a' VecT.nil) :=
  .cons rfl h .nil

/-- The derived relation of `WTreeT` relates branches at equal indices. -/
example {A A' : Type} (P : A → A' → Prop) (a : A) (a' : A') (h : P a a') :
    WTreeT.R_param P (WTreeT.node fun _ => .leaf a) (WTreeT.node fun _ => .leaf a') :=
  .node (fun _ _ _ => .leaf h)

/-- The first handler derives the forward map of `PairT`. -/
example {A A' B B' : Type} (PA : Param .map3 .map3 A A') (PB : Param .map3 .map3 B B')
    (a : A) (b : B) :
    castViaParam (PairT.param_instance PA PB) ⟨a, b⟩ = ⟨PA.fwd.map a, PB.fwd.map b⟩ :=
  rfl

/-- The second handler derives the relation of `SelT` in the same clause. -/
example {A A' : Type} (P : A → A' → Prop) (g : (A → Bool) → A) (g' : (A' → Bool) → A')
    (h : ∀ y y', (∀ a a', P a a' → y a = y' a') → P (g y) (g' y')) :
    SelT.R_param P ⟨g⟩ ⟨g'⟩ :=
  .mk h

end Transfer.Param.VarianceTest
