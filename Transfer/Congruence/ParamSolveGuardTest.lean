/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedFunTest

/-!
# Tests of the leaf hook in `param_solve` and `rcongr`

Goals of `Transfer.Base.RelatedFunTest`, whose two sides have different carriers,
closed by `param_solve` and by `rcongr` through the leaf rules of
`transfer_guard_leaf`: the accessors and the constructor of a record, a guarded
square whose guard `transfer_guard_disch` closes, conditionals whose condition is
descended through a guarded relation square, and the data squares of `Option`,
pairs, lists and `Except`. The equation goals of that module are stated here in
their `Related` form.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.ParamSolveGuardTest

open Transfer Transfer.RelatedFunTest

/-- An accessor. -/
example (r : Rec) (w : RecW) [Related encRec r w] : Related enc8 r.y w.y := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] : Related enc8 r.y w.y := by
  rcongr

/-- The guarded square, with the guard closed by the discharger. -/
example (r : Rec) (w : RecW) [Related encRec r w] (h : r.x < 256 ∧ r.y < 256) :
    Related (id : ℕ → ℕ) (total r) (sumNat w) := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] (h : r.x < 256 ∧ r.y < 256) :
    Related (id : ℕ → ℕ) (total r) (sumNat w) := by
  rcongr

/-- The guarded square under `some`. -/
example (r : Rec) (w : RecW) [Related encRec r w] (hx : r.x < 256) (hy : r.y < 256) :
    Related (Option.map (id : ℕ → ℕ)) (some (total r)) (some (sumNat w)) := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] (hx : r.x < 256) (hy : r.y < 256) :
    Related (Option.map (id : ℕ → ℕ)) (some (total r)) (some (sumNat w)) := by
  rcongr

/-- A conditional with an `Option` result. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Option.map enc8) (if r.flag then some r.x else none)
      (if w.flag then some w.x else none) := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Option.map enc8) (if r.flag then some r.x else none)
      (if w.flag then some w.x else none) := by
  rcongr

/-- The constructor of the record. -/
example (a b : ℕ) (x y : BitVec 8) [Related enc8 a x] [Related enc8 b y] (c : Bool) :
    Related encRec (Rec.mk a b c) (RecW.mk x y c) := by
  param_solve

example (a b : ℕ) (x y : BitVec 8) [Related enc8 a x] [Related enc8 b y] (c : Bool) :
    Related encRec (Rec.mk a b c) (RecW.mk x y c) := by
  rcongr

/-- Pairs and their projections. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Prod.map enc8 enc8) (r.x, r.y) (w.x, w.y) := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Prod.map enc8 enc8) (r.x, r.y) (w.x, w.y) := by
  rcongr

example (p : ℕ × ℕ) (p' : BitVec 8 × BitVec 8) [Related (Prod.map enc8 enc8) p p'] :
    Related enc8 p.2 p'.2 := by
  param_solve

example (p : ℕ × ℕ) (p' : BitVec 8 × BitVec 8) [Related (Prod.map enc8 enc8) p p'] :
    Related enc8 p.2 p'.2 := by
  rcongr

/-- Lists: length and conversion to an array. -/
example (l : List ℕ) (l' : List (BitVec 8)) [Related (List.map enc8) l l'] :
    Related (id : ℕ → ℕ) l.length l'.length := by
  param_solve

example (l : List ℕ) (l' : List (BitVec 8)) [Related (List.map enc8) l l'] :
    Related (id : ℕ → ℕ) l.length l'.length := by
  rcongr

example (l : List ℕ) (l' : List (BitVec 8)) [Related (List.map enc8) l l'] :
    Related (Array.map enc8) l.toArray l'.toArray := by
  param_solve

example (l : List ℕ) (l' : List (BitVec 8)) [Related (List.map enc8) l l'] :
    Related (Array.map enc8) l.toArray l'.toArray := by
  rcongr

/-- `Except` results. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Except.map (ε := String) enc8) (Except.ok r.x) (Except.ok w.x) := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Except.map (ε := String) enc8) (Except.ok r.x) (Except.ok w.x) := by
  rcongr

example (r : Rec) (w : RecW) [Related encRec r w] (e : String) :
    Related (Except.map enc8) (if r.flag then Except.ok r.x else Except.error e)
      (if w.flag then Except.ok w.x else Except.error e) := by
  param_solve

example (r : Rec) (w : RecW) [Related encRec r w] (e : String) :
    Related (Except.map enc8) (if r.flag then Except.ok r.x else Except.error e)
      (if w.flag then Except.ok w.x else Except.error e) := by
  rcongr

end Transfer.ParamSolveGuardTest
