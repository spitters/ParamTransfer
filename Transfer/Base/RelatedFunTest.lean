/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedFun
public import Transfer.Congruence.ParamGuard

/-!
# Tests of the carrier-changing squares

A record `Rec` of two natural numbers and a flag is encoded as a record `RecW` of
two bytes and the flag. The accessors and the constructor are registered as
`RelatedFun` and `RelatedFun3` squares, and the sum of the two fields read as
natural numbers is a guarded square, which holds when both fields are below `256`.
`param_guard` closes goals whose two sides have different carriers: through the
accessors, the guarded square, a conditional with an `Option` result, and the
data squares of pairs, lists and `Except`.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer.RelatedFunTest

open Transfer

/-- The abstract record. -/
structure Rec where
  /-- The first field. -/
  x : ℕ
  /-- The second field. -/
  y : ℕ
  /-- The flag. -/
  flag : Bool

/-- The encoded record, with bytes in place of the natural numbers. -/
structure RecW where
  /-- The first field. -/
  x : BitVec 8
  /-- The second field. -/
  y : BitVec 8
  /-- The flag. -/
  flag : Bool

/-- The byte encoding of a natural number. -/
abbrev enc8 : ℕ → BitVec 8 := BitVec.ofNat 8

/-- The encoding of a record, field by field. -/
def encRec (r : Rec) : RecW := ⟨enc8 r.x, enc8 r.y, r.flag⟩

instance xSquare : RelatedFun encRec enc8 Rec.x RecW.x where
  comm _ := rfl

instance ySquare : RelatedFun encRec enc8 Rec.y RecW.y where
  comm _ := rfl

instance flagSquare : RelatedFun encRec (id : Bool → Bool) Rec.flag RecW.flag where
  comm _ := rfl

instance mkSquare : RelatedFun3 enc8 enc8 (id : Bool → Bool) encRec Rec.mk RecW.mk where
  comm _ _ _ := rfl

/-- The sum of the fields. -/
def total (r : Rec) : ℕ := r.x + r.y

/-- The sum of the fields of an encoded record, read as natural numbers. -/
def sumNat (w : RecW) : ℕ := w.x.toNat + w.y.toNat

/-- The sums agree when both fields are below `256`. -/
instance totalSquare :
    RelatedFunOn encRec (id : ℕ → ℕ) (fun r => r.x < 256 ∧ r.y < 256) total sumNat where
  comm r h := by
    simp [total, sumNat, encRec, Nat.mod_eq_of_lt h.1, Nat.mod_eq_of_lt h.2]

/-- Equality of flags is equality of their identity encodings. -/
instance boolEqSquare : RelatedRelOn (id : Bool → Bool) (fun _ _ => True) (· = ·) (· = ·) where
  iff _ _ _ := Iff.rfl

/-- An accessor, from an equation goal across carriers. -/
example (r : Rec) (w : RecW) [Related encRec r w] : enc8 r.y = w.y := by
  param_guard

/-- The guarded square, with the guard closed by the discharger. -/
example (r : Rec) (w : RecW) [Related encRec r w] (h : r.x < 256 ∧ r.y < 256) :
    Related (id : ℕ → ℕ) (total r) (sumNat w) := by
  param_guard

/-- The guarded square under `some`: the guard is closed by `omega` from the two
    hypotheses. -/
example (r : Rec) (w : RecW) [Related encRec r w] (hx : r.x < 256) (hy : r.y < 256) :
    Related (Option.map (id : ℕ → ℕ)) (some (total r)) (some (sumNat w)) := by
  param_guard

/-- A conditional with an `Option` result: the condition goal is descended through
    `boolEqSquare` and the accessor of the flag. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    Option.map enc8 (if r.flag then some r.x else none) =
      (if w.flag then some w.x else none) := by
  param_guard

/-- The constructor of the record. -/
example (a b : ℕ) (x y : BitVec 8) [Related enc8 a x] [Related enc8 b y] (c : Bool) :
    encRec (Rec.mk a b c) = RecW.mk x y c := by
  param_guard

/-- Pairs and their projections. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Prod.map enc8 enc8) (r.x, r.y) (w.x, w.y) := by
  param_guard

example (p : ℕ × ℕ) (p' : BitVec 8 × BitVec 8) [Related (Prod.map enc8 enc8) p p'] :
    Related enc8 p.2 p'.2 := by
  param_guard

/-- Lists: concatenation, reversal, length and conversion to an array. -/
example (r : Rec) (w : RecW) [Related encRec r w] (l : List ℕ) (l' : List (BitVec 8))
    [Related (List.map enc8) l l'] :
    Related (List.map enc8) (r.x :: l ++ [r.y]).reverse (w.x :: l' ++ [w.y]).reverse := by
  param_guard

example (l : List ℕ) (l' : List (BitVec 8)) [Related (List.map enc8) l l'] :
    Related (id : ℕ → ℕ) l.length l'.length := by
  param_guard

example (l : List ℕ) (l' : List (BitVec 8)) [Related (List.map enc8) l l'] :
    Related (Array.map enc8) l.toArray l'.toArray := by
  param_guard

/-- `Except` results. -/
example (r : Rec) (w : RecW) [Related encRec r w] :
    Related (Except.map (ε := String) enc8) (Except.ok r.x) (Except.ok w.x) := by
  param_guard

example (r : Rec) (w : RecW) [Related encRec r w] (e : String) :
    Related (Except.map enc8) (if r.flag then Except.ok r.x else Except.error e)
      (if w.flag then Except.ok w.x else Except.error e) := by
  param_guard

end Transfer.RelatedFunTest
