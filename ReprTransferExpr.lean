/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import ReprTransfer

/-!
# Tier-3: compositional transfer via the abstraction theorem

The per-op `BinOpRealization` (`Bridges/ReprTransfer.lean`) transfers a single
operation's equation. Real verifier equations are composite — e.g. Groth16's
pairing product `e(αG1,βG2)·e(L,γG2)·e(C,δG2)` is two `GT` products over three
pairings. A parametricity/relational-model translation automates the transfer of
each composite.

This module is the internalized relational-model core for a homogeneous
operation fragment: an expression algebra over one binary operation, with an
abstract and a computational denotation tied by the abstraction theorem
(`denote_commutes` — by induction, the single-op commuting square lifts to whole
terms), from which composite equation transfer (`expr_eq_transfer`) follows. This
is the payload a paramcoq/Trocq translation produces; here it is a finite,
fully-proved Lean construction for the op-algebra fragment the emit-realization
bridges use. A native `Expr`-level translation that generates this for arbitrary
terms (rather than the fixed op-algebra here) is the greenfield "Lean Trocq" —
this module is the semantic kernel it targets.

## Main definitions

* `EndoOpRealization op bop` — a homogeneous binary op `op : A → A → A` realized
  by `bop : α → α → α` via an equality-reflecting encoding.
* `OpExpr` — the expression algebra (leaves + binary nodes).
* `OpExpr.denote_commutes` — the abstraction theorem.
* `OpExpr.expr_eq_transfer` — composite equation transfer.
-/

set_option autoImplicit false

namespace ReprTransfer

universe u

/-- A homogeneous binary-op realization: `op : A → A → A` realized by
    `bop : α → α → α` via an equality-reflecting encoding `enc`. The homogeneous
    (single-carrier) specialization of `BinOpRealization`, on which the
    expression algebra below is built. -/
structure EndoOpRealization {A α : Type u} (op : A → A → A) (bop : α → α → α) where
  /-- The equality-reflecting encoding of abstract values. -/
  enc : A → α
  /-- The encoding reflects equality. -/
  enc_inj : Function.Injective enc
  /-- The single-op commuting square. -/
  commutes : ∀ a b, enc (op a b) = bop (enc a) (enc b)

namespace EndoOpRealization
variable {A α : Type u} {op : A → A → A} {bop : α → α → α}

/-- The codomain embedding underlying an `EndoOpRealization`. -/
def toReprEmbedding (R : EndoOpRealization op bop) : ReprEmbedding A α :=
  ⟨R.enc, R.enc_inj⟩

end EndoOpRealization

/-! ## The operation expression algebra -/

/-- Expressions over a single binary operation: abstract leaves and binary
    nodes. The shape of a pairing-product / field-arithmetic tree. -/
inductive OpExpr (A : Type u) where
  /-- An abstract leaf value (e.g. a single pairing output `e(P,Q) : GT`). -/
  | leaf : A → OpExpr A
  /-- A binary node (e.g. a `GT` product `a · b`). -/
  | node : OpExpr A → OpExpr A → OpExpr A

namespace OpExpr
variable {A α : Type u}

/-- Abstract denotation: fold the tree with the abstract operation. -/
def denoteAbs (op : A → A → A) : OpExpr A → A
  | leaf a => a
  | node l r => op (denoteAbs op l) (denoteAbs op r)

/-- Computational denotation: encode the leaves and fold with the computational
    operation `bop`. -/
def denoteComp {op : A → A → A} {bop : α → α → α}
    (R : EndoOpRealization op bop) : OpExpr A → α
  | leaf a => R.enc a
  | node l r => bop (denoteComp R l) (denoteComp R r)

/-- The abstraction theorem. For any composite expression, encoding its
    abstract value equals its computational denotation. Proved by induction: the
    single-op commuting square lifts to whole terms. This is the relational-model
    payload — the reason the transfer composes. -/
theorem denote_commutes {op : A → A → A} {bop : α → α → α}
    (R : EndoOpRealization op bop) (e : OpExpr A) :
    R.enc (e.denoteAbs op) = e.denoteComp R := by
  induction e with
  | leaf a => rfl
  | node l r ihl ihr =>
    simp only [denoteAbs, denoteComp, R.commutes, ihl, ihr]

/-- Composite equation transfer. An equation between two abstract composite
    expressions holds iff their computational denotations agree. The whole
    (multi-op) verifier equation transfers from the single-op realization `R`. -/
theorem expr_eq_transfer {op : A → A → A} {bop : α → α → α}
    (R : EndoOpRealization op bop) (e₁ e₂ : OpExpr A) :
    e₁.denoteAbs op = e₂.denoteAbs op ↔ e₁.denoteComp R = e₂.denoteComp R := by
  rw [← denote_commutes, ← denote_commutes]
  exact ⟨fun h => by rw [h], fun h => R.enc_inj h⟩

end OpExpr

/-! ## Two-sorted: a whole pairing-product verifier tree

The homogeneous `OpExpr` handles a single op. A pairing-product verifier (Groth16
LHS) mixes two operations of different sorts: the pairing `e : A → B → C`
(heterogeneous) and the `C`-product `mul` (homogeneous). `PExpr` is the
two-sorted tree — pairing leaves and product nodes — so the entire verifier
LHS is one term, and `PExpr.expr_eq_transfer` transfers the whole verifier
equation from a single abstraction theorem. Here the pairings are nodes of the
same tree the transfer ranges over, rather than opaque leaf-values supplied by
hand. -/

/-- A bilinear-operation realization: an abstract pairing `e : A → B → C` and
    an abstract `C`-product `mul`, realized by computational `bpair`/`bmul` via
    domain maps `encA`/`encB`, a `C`-embedding `encC`, and two commuting squares.
    The data a whole pairing-product verifier tree needs (the KZG
    `ByteGroupRealization` is an instance). -/
structure PairingRealization {A B C : Type u} {α β γ : Type u}
    (e : A → B → C) (mul : C → C → C) (bpair : α → β → γ)
    (bmul : γ → γ → γ) where
  /-- Encoding of `A` (first pairing operand). -/
  encA : A → α
  /-- Encoding of `B` (second pairing operand). -/
  encB : B → β
  /-- Equality-reflecting encoding of `C` (the target group). -/
  encC : C → γ
  /-- `C`-equality reflection. -/
  encC_inj : Function.Injective encC
  /-- The pairing commuting square. -/
  pair_commutes : ∀ a b, encC (e a b) = bpair (encA a) (encB b)
  /-- The `C`-product commuting square. -/
  mul_commutes  : ∀ x y, encC (mul x y) = bmul (encC x) (encC y)

/-- A two-sorted pairing-product expression: pairing leaves `e(a,b)` and
    product nodes. One `PExpr` captures a whole pairing-product verifier LHS. -/
inductive PExpr (A B : Type u) where
  /-- A pairing leaf `e(a, b)`. -/
  | pair : A → B → PExpr A B
  /-- A product node combining two sub-expressions. -/
  | node : PExpr A B → PExpr A B → PExpr A B

namespace PExpr
variable {A B C : Type u} {α β γ : Type u}

/-- Abstract denotation of a pairing-product tree (pairings via `e`, nodes via `mul`). -/
def denoteAbs (e : A → B → C) (mul : C → C → C) : PExpr A B → C
  | pair a b => e a b
  | node l r => mul (denoteAbs e mul l) (denoteAbs e mul r)

/-- Computational denotation: pairing leaves via `bpair` on encoded operands,
    nodes via `bmul`. -/
def denoteComp {e : A → B → C} {mul : C → C → C}
    {bpair : α → β → γ} {bmul : γ → γ → γ}
    (R : PairingRealization e mul bpair bmul) : PExpr A B → γ
  | pair a b => bpair (R.encA a) (R.encB b)
  | node l r => bmul (denoteComp R l) (denoteComp R r)

/-- Abstraction theorem (two-sorted). Encoding the abstract value of a whole
    pairing-product tree equals its computational denotation — by induction, both
    commuting squares lifting through the tree. -/
theorem denote_commutes {e : A → B → C} {mul : C → C → C}
    {bpair : α → β → γ} {bmul : γ → γ → γ}
    (R : PairingRealization e mul bpair bmul) (x : PExpr A B) :
    R.encC (x.denoteAbs e mul) = x.denoteComp R := by
  induction x with
  | pair a b => exact R.pair_commutes a b
  | node l r ihl ihr => simp only [denoteAbs, denoteComp, R.mul_commutes, ihl, ihr]

/-- Whole-verifier equation transfer. An equation between two abstract
    pairing-product trees holds iff their computational denotations agree — the
    entire pairing-product verifier equation, transferred from the per-op
    commuting squares with no bespoke composite proof. -/
theorem expr_eq_transfer {e : A → B → C} {mul : C → C → C}
    {bpair : α → β → γ} {bmul : γ → γ → γ}
    (R : PairingRealization e mul bpair bmul) (x y : PExpr A B) :
    x.denoteAbs e mul = y.denoteAbs e mul ↔ x.denoteComp R = y.denoteComp R := by
  rw [← denote_commutes, ← denote_commutes]
  exact ⟨fun h => by rw [h], fun h => R.encC_inj h⟩

end PExpr

end ReprTransfer
