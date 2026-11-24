/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedFamily

/-!
# Carrier-changing squares

The squares of `Transfer.Base.Related` and `Transfer.Base.RelatedOn` relate an
operation on one abstract carrier to an operation on one encoded carrier. This
file relates a function `f : A → B` to a function `g : α → β` along two
encodings, `encA : A → α` on the arguments and `encB : B → β` on the results:

* `RelatedFun encA encB f g`: `encB (f a) = g (encA a)`;
* `RelatedFun2`, `RelatedFun3`: the same for functions of two and three
  arguments, each with its own encoding;
* `RelatedFunOn`, `RelatedFun2On`, `RelatedFun3On`: the guarded forms, which
  hold on the abstract arguments satisfying a guard `P`.

The argument encodings and the guard are `outParam`s: a goal
`Related encB (f a) (g x)` names only the result encoding, and the registered
square of `(f, g)` supplies the others.

## Main results

* `RelatedFun.toOn`, `RelatedFun2.toOn`, `RelatedFun3.toOn`: a total square is a
  guarded square with guard `True`.
* `rcongrFunOn`, `rcongrFun2On`, `rcongrFun3On`: from related arguments and the
  guard, the results are related. The guard is the last hypothesis.
* `rcongrFun`, `rcongrFun2`, `rcongrFun3`: the same for total squares.
* `composeFun`, `composeFun2`, `composeFun3`: the composition as instances, so that
  instance resolution relates closed terms built from total squares.
* Data squares: `some` and `none` along `Option.map enc`; `Prod.mk`, `Prod.fst`
  and `Prod.snd` along `Prod.map`; `Except.ok` and `Except.error` along
  `Except.map` and `Except.mapError`; `[]`, `List.cons`, `++`, `List.reverse`,
  `List.length` and `List.toArray` along `List.map enc`; the projections and the
  length are `Related` instances, since their result encoding does not determine
  the argument encoding; the functorial squares
  `Option.map`, `List.map`; the related array `(l.map enc).toArray` of
  `Transfer.Base.RelatedFamily`.
* `rcongrIte`: a conditional is related to a conditional on an equivalent
  condition with related branches; `rcongrIteLeaf` is its form with a trailing
  guard `True`.

`transfer_guard_leaf` receives the rules `rcongrFunOn`, `rcongrFun2On`,
`rcongrFun3On` and `rcongrIteLeaf` as alternatives. `param_guard` applies them at a
`Related` goal that no same-carrier square closes, recurses into the argument
goals (for `rcongrIteLeaf` also into the condition goal, an `Iff`), and runs the
guard discharger on the last goal.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

universe u v w x

/-! ## The square classes -/

/-- `RelatedFun encA encB f g`: along the argument encoding `encA` and the result
    encoding `encB`, the function `g` realizes `f`. -/
class RelatedFun {A α : Type u} {B β : Type v} (encA : outParam (A → α)) (encB : B → β)
    (f : A → B) (g : α → β) : Prop where
  /-- The commuting square. -/
  comm : ∀ a, encB (f a) = g (encA a)

/-- `RelatedFun2 encA encB encC f g`: the square of a function of two arguments. -/
class RelatedFun2 {A α : Type u} {B β : Type v} {C γ : Type w} (encA : outParam (A → α))
    (encB : outParam (B → β)) (encC : C → γ) (f : A → B → C) (g : α → β → γ) : Prop where
  /-- The commuting square. -/
  comm : ∀ a b, encC (f a b) = g (encA a) (encB b)

/-- `RelatedFun3 encA encB encC encD f g`: the square of a function of three
    arguments. -/
class RelatedFun3 {A α : Type u} {B β : Type v} {C γ : Type w} {D δ : Type x}
    (encA : outParam (A → α)) (encB : outParam (B → β)) (encC : outParam (C → γ))
    (encD : D → δ) (f : A → B → C → D) (g : α → β → γ → δ) : Prop where
  /-- The commuting square. -/
  comm : ∀ a b c, encD (f a b c) = g (encA a) (encB b) (encC c)

/-- `RelatedFunOn encA encB P f g`: the square of `RelatedFun` on the arguments
    satisfying the guard `P`. -/
class RelatedFunOn {A α : Type u} {B β : Type v} (encA : outParam (A → α)) (encB : B → β)
    (P : outParam (A → Prop)) (f : A → B) (g : α → β) : Prop where
  /-- The commuting square under the guard. -/
  comm : ∀ a, P a → encB (f a) = g (encA a)

/-- `RelatedFun2On encA encB encC P f g`: the square of `RelatedFun2` on the
    arguments satisfying the guard `P`. -/
class RelatedFun2On {A α : Type u} {B β : Type v} {C γ : Type w} (encA : outParam (A → α))
    (encB : outParam (B → β)) (encC : C → γ) (P : outParam (A → B → Prop))
    (f : A → B → C) (g : α → β → γ) : Prop where
  /-- The commuting square under the guard. -/
  comm : ∀ a b, P a b → encC (f a b) = g (encA a) (encB b)

/-- `RelatedFun3On encA encB encC encD P f g`: the square of `RelatedFun3` on the
    arguments satisfying the guard `P`. -/
class RelatedFun3On {A α : Type u} {B β : Type v} {C γ : Type w} {D δ : Type x}
    (encA : outParam (A → α)) (encB : outParam (B → β)) (encC : outParam (C → γ))
    (encD : D → δ) (P : outParam (A → B → C → Prop)) (f : A → B → C → D)
    (g : α → β → γ → δ) : Prop where
  /-- The commuting square under the guard. -/
  comm : ∀ a b c, P a b c → encD (f a b c) = g (encA a) (encB b) (encC c)

section Classes

variable {A α : Type u} {B β : Type v} {C γ : Type w} {D δ : Type x}

/-- A total square is a guarded square with guard `True`. -/
instance RelatedFun.toOn (encA : A → α) (encB : B → β) (f : A → B) (g : α → β)
    [h : RelatedFun encA encB f g] : RelatedFunOn encA encB (fun _ => True) f g where
  comm a _ := h.comm a

/-- A total binary square is a guarded square with guard `True`. -/
instance RelatedFun2.toOn (encA : A → α) (encB : B → β) (encC : C → γ) (f : A → B → C)
    (g : α → β → γ) [h : RelatedFun2 encA encB encC f g] :
    RelatedFun2On encA encB encC (fun _ _ => True) f g where
  comm a b _ := h.comm a b

/-- A total ternary square is a guarded square with guard `True`. -/
instance RelatedFun3.toOn (encA : A → α) (encB : B → β) (encC : C → γ) (encD : D → δ)
    (f : A → B → C → D) (g : α → β → γ → δ) [h : RelatedFun3 encA encB encC encD f g] :
    RelatedFun3On encA encB encC encD (fun _ _ _ => True) f g where
  comm a b c _ := h.comm a b c

/-! ## Composition with `Related` -/

/-- Guarded composition: from a related argument and the guard on the abstract
    argument, `g x` is the encoding of `f a`. -/
theorem rcongrFunOn {encA : A → α} (encB : B → β) {P : A → Prop} (f : A → B) (g : α → β)
    {a : A} {x : α} [h : RelatedFunOn encA encB P f g] (ha : Related encA a x) (hg : P a) :
    Related encB (f a) (g x) where
  rel := by rw [h.comm a hg, ha.rel]

/-- Guarded binary composition. -/
theorem rcongrFun2On {encA : A → α} {encB : B → β} (encC : C → γ) {P : A → B → Prop}
    (f : A → B → C) (g : α → β → γ) {a : A} {b : B} {x : α} {y : β}
    [h : RelatedFun2On encA encB encC P f g] (ha : Related encA a x) (hb : Related encB b y)
    (hg : P a b) : Related encC (f a b) (g x y) where
  rel := by rw [h.comm a b hg, ha.rel, hb.rel]

/-- Guarded ternary composition. -/
theorem rcongrFun3On {encA : A → α} {encB : B → β} {encC : C → γ} (encD : D → δ)
    {P : A → B → C → Prop} (f : A → B → C → D) (g : α → β → γ → δ) {a : A} {b : B} {c : C}
    {x : α} {y : β} {z : γ} [h : RelatedFun3On encA encB encC encD P f g]
    (ha : Related encA a x) (hb : Related encB b y) (hc : Related encC c z) (hg : P a b c) :
    Related encD (f a b c) (g x y z) where
  rel := by rw [h.comm a b c hg, ha.rel, hb.rel, hc.rel]

/-- Total composition: from a related argument, `g x` is the encoding of `f a`. -/
theorem rcongrFun {encA : A → α} (encB : B → β) (f : A → B) (g : α → β) {a : A} {x : α}
    [h : RelatedFun encA encB f g] (ha : Related encA a x) : Related encB (f a) (g x) where
  rel := by rw [h.comm a, ha.rel]

/-- Total binary composition. -/
theorem rcongrFun2 {encA : A → α} {encB : B → β} (encC : C → γ) (f : A → B → C)
    (g : α → β → γ) {a : A} {b : B} {x : α} {y : β} [h : RelatedFun2 encA encB encC f g]
    (ha : Related encA a x) (hb : Related encB b y) : Related encC (f a b) (g x y) where
  rel := by rw [h.comm a b, ha.rel, hb.rel]

/-- Total ternary composition. -/
theorem rcongrFun3 {encA : A → α} {encB : B → β} {encC : C → γ} (encD : D → δ)
    (f : A → B → C → D) (g : α → β → γ → δ) {a : A} {b : B} {c : C} {x : α} {y : β} {z : γ}
    [h : RelatedFun3 encA encB encC encD f g] (ha : Related encA a x) (hb : Related encB b y)
    (hc : Related encC c z) : Related encD (f a b c) (g x y z) where
  rel := by rw [h.comm a b c, ha.rel, hb.rel, hc.rel]

/-- Composition as an instance: resolution relates `f a` to `g x` from a total
    square and related arguments. -/
instance composeFun {encA : A → α} (encB : B → β) (f : A → B) (g : α → β) (a : A) (x : α)
    [hf : RelatedFun encA encB f g] [ha : Related encA a x] : Related encB (f a) (g x) :=
  rcongrFun encB f g ha

/-- Binary composition as an instance. -/
instance composeFun2 {encA : A → α} {encB : B → β} (encC : C → γ) (f : A → B → C)
    (g : α → β → γ) (a : A) (b : B) (x : α) (y : β) [hf : RelatedFun2 encA encB encC f g]
    [ha : Related encA a x] [hb : Related encB b y] : Related encC (f a b) (g x y) :=
  rcongrFun2 encC f g ha hb

/-- Ternary composition as an instance. -/
instance composeFun3 {encA : A → α} {encB : B → β} {encC : C → γ} (encD : D → δ)
    (f : A → B → C → D) (g : α → β → γ → δ) (a : A) (b : B) (c : C) (x : α) (y : β) (z : γ)
    [hf : RelatedFun3 encA encB encC encD f g] [ha : Related encA a x] [hb : Related encB b y]
    [hc : Related encC c z] : Related encD (f a b c) (g x y z) :=
  rcongrFun3 encD f g ha hb hc

end Classes

/-! ## Conditionals -/

/-- A conditional is related to a conditional whose condition is equivalent and
    whose branches are related. -/
theorem rcongrIte {A α : Type u} {enc : A → α} {p q : Prop} [Decidable p] [Decidable q]
    {a b : A} {a' b' : α} (hpq : p ↔ q) (ha : Related enc a a') (hb : Related enc b b') :
    Related enc (if p then a else b) (if q then a' else b') where
  rel := (apply_ite enc p a b).trans (if_congr hpq ha.rel hb.rel)

/-- `rcongrIte` with a trailing guard `True`, the form of a leaf rule of
    `transfer_guard_leaf`: `param_guard` descends into the condition and the two
    branches and closes the guard. -/
theorem rcongrIteLeaf {A α : Type u} {enc : A → α} {p q : Prop} [Decidable p] [Decidable q]
    {a b : A} {a' b' : α} (hpq : p ↔ q) (ha : Related enc a a') (hb : Related enc b b')
    (_hg : True) : Related enc (if p then a else b) (if q then a' else b') :=
  rcongrIte hpq ha hb

/-! ## Data squares -/

section Data

variable {A α : Type u} {B β : Type v}

/-- `some` along `Option.map enc`. -/
instance someRelatedFun (enc : A → α) : RelatedFun enc (Option.map enc) some some where
  comm _ := rfl

/-- `none` along `Option.map enc`. -/
instance noneRelated (enc : A → α) : Related (Option.map enc) none none where
  rel := rfl

/-- `Option.map` is functorial in the square: a square of `(f, g)` gives a square
    of `(Option.map f, Option.map g)`. -/
instance optionMapRelatedFun (encA : A → α) (encB : B → β) (f : A → B) (g : α → β)
    [h : RelatedFun encA encB f g] :
    RelatedFun (Option.map encA) (Option.map encB) (Option.map f) (Option.map g) where
  comm o := by cases o <;> simp [h.comm]

/-- `Prod.mk` along `Prod.map encA encB`. -/
instance prodMkRelatedFun2 (encA : A → α) (encB : B → β) :
    RelatedFun2 encA encB (Prod.map encA encB) Prod.mk Prod.mk where
  comm _ _ := rfl

set_option synthInstance.checkSynthOrder false in
/-- `Prod.fst` along `Prod.map encA encB`. The result encoding `encA` does not
    determine `encB`, so the square is stated on `Related` and not as a
    `RelatedFun` instance; resolution finds `encB` from a related pair in the
    context. -/
instance prodFstRelated (encA : A → α) (encB : B → β) (p : A × B) (p' : α × β)
    [h : Related (Prod.map encA encB) p p'] : Related encA p.1 p'.1 where
  rel := by rw [← h.rel]; rfl

set_option synthInstance.checkSynthOrder false in
/-- `Prod.snd` along `Prod.map encA encB`, stated on `Related` as `prodFstRelated`. -/
instance prodSndRelated (encA : A → α) (encB : B → β) (p : A × B) (p' : α × β)
    [h : Related (Prod.map encA encB) p p'] : Related encB p.2 p'.2 where
  rel := by rw [← h.rel]; rfl

/-- `Except.ok` along `Except.map enc`. -/
instance exceptOkRelatedFun {ε : Type v} (enc : A → α) :
    RelatedFun enc (Except.map (ε := ε) enc) Except.ok Except.ok where
  comm _ := rfl

/-- `Except.error` along `Except.map enc`: the error is unchanged. -/
instance exceptErrorRelatedFun {ε : Type v} (enc : A → α) :
    RelatedFun (id : ε → ε) (Except.map enc) (Except.error (α := A)) Except.error where
  comm _ := rfl

/-- `Except.error` along `Except.mapError enc`. -/
instance exceptErrorMapErrorRelatedFun {E : Type v} (enc : A → α) :
    RelatedFun enc (Except.mapError (α := E) enc) Except.error Except.error where
  comm _ := rfl

/-- `Except.ok` along `Except.mapError enc`: the value is unchanged. -/
instance exceptOkMapErrorRelatedFun {E : Type v} (enc : A → α) :
    RelatedFun (id : E → E) (Except.mapError enc) (Except.ok (ε := A)) Except.ok where
  comm _ := rfl

/-- `[]` along `List.map enc`. -/
instance listNilRelated (enc : A → α) : Related (List.map enc) [] [] where
  rel := rfl

/-- `List.cons` along `List.map enc`. -/
instance listConsRelatedFun2 (enc : A → α) :
    RelatedFun2 enc (List.map enc) (List.map enc) List.cons List.cons where
  comm _ _ := rfl

/-- Concatenation along `List.map enc`. -/
instance listAppendRelatedFun2 (enc : A → α) :
    RelatedFun2 (List.map enc) (List.map enc) (List.map enc) (· ++ ·) (· ++ ·) where
  comm _ _ := List.map_append

/-- `List.reverse` along `List.map enc`. -/
instance listReverseRelatedFun (enc : A → α) :
    RelatedFun (List.map enc) (List.map enc) List.reverse List.reverse where
  comm _ := List.map_reverse

set_option synthInstance.checkSynthOrder false in
/-- `List.length` along `List.map enc`, with the identity encoding on lengths. The
    result encoding does not determine `enc`, so the square is stated on
    `Related`. -/
instance listLengthRelated (enc : A → α) (l : List A) (l' : List α)
    [h : Related (List.map enc) l l'] : Related (id : ℕ → ℕ) l.length l'.length where
  rel := by rw [← h.rel, List.length_map]; rfl

/-- `List.toArray` along `List.map enc` and `Array.map enc`. -/
instance listToArrayRelatedFun (enc : A → α) :
    RelatedFun (List.map enc) (Array.map enc) List.toArray List.toArray where
  comm l := by simp

/-- `List.map` is functorial in the square: a square of `(f, g)` gives a square of
    `(List.map f, List.map g)`. -/
instance listMapRelatedFun (encA : A → α) (encB : B → β) (f : A → B) (g : α → β)
    [h : RelatedFun encA encB f g] :
    RelatedFun (List.map encA) (List.map encB) (List.map f) (List.map g) where
  comm l := by simp [Function.comp_def, h.comm]

/-- The array of the encodings of a list is related to the list, read as a family
    over its positions. -/
instance listMapToArrayRelatedArray (enc : A → α) (l : List A) :
    RelatedArray enc (fun i : Fin l.length => l[i]) (l.map enc).toArray where
  getElem?_eq i := by simp

end Data

/-! ## Registration in the guarded descent -/

/-- Leaf rule: the unary guarded composition `rcongrFunOn`. -/
macro_rules
  | `(tactic| transfer_guard_leaf) => `(tactic| refine rcongrFunOn _ _ _ ?_ ?_)

/-- Leaf rule: the binary guarded composition `rcongrFun2On`. -/
macro_rules
  | `(tactic| transfer_guard_leaf) => `(tactic| refine rcongrFun2On _ _ _ ?_ ?_ ?_)

/-- Leaf rule: the ternary guarded composition `rcongrFun3On`. -/
macro_rules
  | `(tactic| transfer_guard_leaf) => `(tactic| refine rcongrFun3On _ _ _ ?_ ?_ ?_ ?_)

/-- Leaf rule: the conditional `rcongrIteLeaf`. -/
macro_rules
  | `(tactic| transfer_guard_leaf) => `(tactic| refine rcongrIteLeaf ?_ ?_ ?_ ?_)

end Transfer
