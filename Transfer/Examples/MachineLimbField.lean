/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Statements.ParamTransferTac
import Transfer.Combinators.ParamForall
import Transfer.Congruence.HCongrConnection
import Mathlib.Data.ZMod.Basic

/-!
# Machine limbs ↔ prime field: a strong non-diagonal heterogeneous dependent example

This module is a worked end-to-end example of the `Param` engine on a *real crypto
representation change*: the machine-limb view of a prime field element and its
abstract `ZMod p` view. It exercises the engine at full strength — the domain is

* **non-diagonal** (the two sides are genuinely different types: `BitVec 64` /
  `Fin n → BitVec 64` on the left, `ZMod p` on the right),
* **heterogeneous** (the value leaf relates terms living in *different* types via a
  decoder, closed by `hcongr_hetero`, not native `congr`), and
* **dependent** (the multi-limb section is the `R_forall` dependent-Π relation over
  the `Fin n`-indexed limb family).

It builds, in dependency order, two retractions and their store-refinement leaves:

1. the **single-limb** split surjection `BitVec 64 ↠ ZMod p`
   (`limbFieldParam`, `instTransferDomLimbField`, `dec_add`/`dec_mul`,
   `LimbStoreRefines`, `limbLeaf_hcongr`) — one 64-bit word per field element
   (BabyBear, Goldilocks, Mersenne-31);
2. the **multi-limb** split surjection `(Fin n → BitVec 64) ↠ ZMod p`
   (`limbVal`/`toLimbs`/`limbVal_toLimbs`, `multiLimbFieldParam`,
   `limbVal_congr`/`limbVal_hcongr`/`limbVal_hcongr_field`, `MultiLimbStoreRefines`,
   `multiLimbLeaf_hcongr`) — a base-`2^64` limb array per field element
   (Curve25519 `n = 4`, P-384 `n = 6`, every multi-limb prime).

Both are asymmetric retractions `Param .map0 .map2a … (ZMod p)`, mirroring
`Transfer.Param.natZModDom` / the `ℤ ↠ ZMod p` example in `ParamRetraction`, but
with the machine-limb type as the concrete source — the value-abstraction layer of
a verified compiler's store refinement.

## Why a retraction, not an equivalence

The decoder `dec w := (w.toNat : ZMod p)` (single-limb) resp.
`dec limbs := (limbVal n limbs : ZMod p)` (multi-limb) is surjective (every field
element is some limb('s array)'s reduction) but not injective when
`p < 2^64` resp. `p < 2^(64·n)` — distinct limbs reduce equally. So the round-trip
holds on the `ZMod p` side only:

* **Forward** is trivial (`map0`): the relation is the graph of the decoder, but at
  the `∀`-rule level the forward structure is forgotten to `⟨⟩`.
* **Backward** is `map2a`: the section picks the canonical limb (single-limb) resp.
  splits into base-`2^64` digits (multi-limb), and `map_in_R` is the retraction law.
  It is *not* `map2b`, because that would force every reducing limb to be the
  canonical one, which is false.

This is the "Way 2" construction: the no-overflow condition is absorbed into the
section, which always lands a canonical representative in range, so the section law
holds unconditionally on the `ZMod p` side.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Transfer.Param

open Transfer Transfer.Param

/-! ## The single-limb split surjection `BitVec 64 ↠ ZMod p` -/

/-- The limb→field split surjection `BitVec 64 ↠ ZMod p` as a
    `Param .map0 .map2a` retraction (for a single-64-bit-limb prime,
    `hp : p ≤ 2 ^ 64`).

    Relation `R w x := ((w.toNat : ZMod p) = x)` (graph of the limb decoder).
    Forward is the trivial `map0`. Backward is `map2a`: section
    `sec x := BitVec.ofNat 64 x.val` with `map_in_R` the retraction
    `((BitVec.ofNat 64 x.val).toNat : ZMod p) = x`. The section law reduces
    (via `BitVec.toNat_ofNat` then `Nat.mod_eq_of_lt` from `x.val < p ≤ 2^64`) to
    `ZMod.natCast_rightInverse`. It is *not* `map2b`: the decoder is not
    injective, so the class is asymmetric. -/
def limbFieldParam (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64) :
    Param .map0 .map2a (BitVec 64) (ZMod p) where
  R := fun w x => ((w.toNat : ZMod p) = x)
  fwd := ⟨⟩
  bwd :=
    ⟨fun x => BitVec.ofNat 64 x.val,
     fun x w (h : BitVec.ofNat 64 x.val = w) => by
       subst h
       show ((BitVec.ofNat 64 x.val).toNat : ZMod p) = x
       rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt x) hp)]
       exact ZMod.natCast_rightInverse x⟩

/-- `TransferDom` accepts the limb→field split surjection: the `BitVec 64 ↠ ZMod p`
    change of representation resolves automatically for `param_transfer`. This is a
    *non-diagonal* `TransferDom` (machine limb type ≠ abstract field), the
    Phase-2 value-abstraction analogue of `instTransferDomNatZMod`. The
    single-limb bound `p ≤ 2^64` is carried as a `Fact` so instance resolution can
    discharge it. -/
instance instTransferDomLimbField (p : ℕ) [NeZero p] [Fact (p ≤ 2 ^ 64)] :
    TransferDom (BitVec 64) (ZMod p) where
  dom := limbFieldParam p Fact.out

/-! ## Operation squares: `feAdd`/`feMul` transfer through the decoder

Under a no-overflow hypothesis on the 64-bit limb sum/product, the machine
word operation commutes with the abstract field operation across the decoder
`dec w := (w.toNat : ZMod p)`. These are the value-level commuting squares that
justify transferring `feAdd`/`feMul` from the field to the limb store: the
decoder is a (partial, overflow-guarded) ring homomorphism.

The overflow guard is essential — without it, `BitVec` addition wraps mod
`2^64` before the field reduction, which need not agree with reducing the true
integer sum mod `p`. -/

/-- Decoder-addition square: on limbs whose true integer sum stays below `2^64`,
    the decoder of the (wrapping) word sum equals the field sum of the decoders.
    The no-overflow hypothesis collapses the `% 2^64` wrap so `BitVec` addition
    lines up with `ℕ` addition before reduction mod `p`. -/
theorem dec_add (p : ℕ) [NeZero p] (w1 w2 : BitVec 64)
    (h : w1.toNat + w2.toNat < 2 ^ 64) :
    (((w1 + w2).toNat : ZMod p)) = (w1.toNat : ZMod p) + (w2.toNat : ZMod p) := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h, Nat.cast_add]

/-- Decoder-multiplication square: on limbs whose true integer product stays
    below `2^64`, the decoder of the (wrapping) word product equals the field
    product of the decoders. -/
theorem dec_mul (p : ℕ) [NeZero p] (w1 w2 : BitVec 64)
    (h : w1.toNat * w2.toNat < 2 ^ 64) :
    (((w1 * w2).toNat : ZMod p)) = (w1.toNat : ZMod p) * (w2.toNat : ZMod p) := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h, Nat.cast_mul]

/-! ## Store refinement as heterogeneous congruence over `limbFieldParam`

A machine store `s : V → BitVec 64` (limb per variable) and its abstract
field-store view `s' : V → ZMod p` are related exactly when they are
`Transfer.Param.R_forall`-related over the single-limb decoder fiber
`limbFieldParam` — the dependent-Π relation whose (constant) fiber is the
limb→field split surjection. Reading any one variable is then an instance of
`hcongr_hetero`: the machine value `s v : BitVec 64` and the field value
`s' v' : ZMod p` live in *different* types and are related by the decoder, i.e.
the value leaf `((s v).toNat : ZMod p) = s' v'` is UA-free heterogeneous
congruence across the limb→field change of representation, not native `congr`.

The *transport* form of heterogeneous congruence (`hcongr_hetero_transport`)
does not apply here: it requires a `map2b` fiber (a forward map carrying its own
graph), whereas `limbFieldParam`'s forward structure is `map0` by design — the
decoder is recorded as the relation graph and forgotten to `⟨⟩` (the asymmetric
"Way 2" retraction). Only the relation form `hcongr_hetero` is available, which
is the correct reading: the leaf is a *relation* between representations, not a
transportable forward map. -/

/-- The single-limb store-refinement relation: a machine store `s : V → BitVec 64`
    refines an abstract field store `s' : V → ZMod p` when they are
    `R_forall`-related over the (constant) `limbFieldParam` fiber — every
    variable's machine limb decodes to its abstract field value. Unfolds to
    `∀ v v' (_ : v = v'), ((s v).toNat : ZMod p) = s' v'`. -/
def LimbStoreRefines (V : Type) (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64)
    (s : V → BitVec 64) (s' : V → ZMod p) : Prop :=
  Transfer.Param.R_forall (B := fun _ => BitVec 64) (B' := fun _ => ZMod p)
    (Transfer.Param.HCongrConnection.paramEqDom V)
    (fun _ _ _ => limbFieldParam p hp) s s'

/-- **Single-limb value leaf as heterogeneous congruence.** From a store
    refinement `LimbStoreRefines` and equal variables `v = v'`, the machine value
    `s v : BitVec 64` and the field value `s' v' : ZMod p` — living in *different*
    types — are related by the decoder: `((s v).toNat : ZMod p) = s' v'`. This is
    `hcongr_hetero` at the `limbFieldParam` fiber, exhibiting the
    machine-value↔field-value relation as UA-free heterogeneous congruence across
    the limb→field change of representation. -/
theorem limbLeaf_hcongr {V : Type} (p : ℕ) [NeZero p] (hp : p ≤ 2 ^ 64)
    {s : V → BitVec 64} {s' : V → ZMod p}
    (hs : LimbStoreRefines V p hp s s') {v v' : V} (hv : v = v') :
    ((s v).toNat : ZMod p) = s' v' :=
  Transfer.Param.HCongrConnection.hcongr_hetero (B := fun _ => BitVec 64)
    (B' := fun _ => ZMod p) (Transfer.Param.HCongrConnection.paramEqDom V)
    (fun _ _ _ => limbFieldParam p hp) hs hv

/-! ## The base-`2^64` limb-array value and its digit section

`limbFieldParam` above builds the single-limb split surjection
`BitVec 64 ↠ ZMod p` (one 64-bit word per field element — BabyBear, Goldilocks,
Mersenne-31). The remainder of this module lifts it to **multi-word** field
elements: a limb array `Fin n → BitVec 64`, read as its base-`2^64` (radix-64,
little-endian) value, projects onto `ZMod p`. This is the representation of
Curve25519 field elements (`n = 4`), P-384 (`n = 6`), and every multi-limb prime
field.

The witness is again a retraction `Param .map0 .map2a (Fin n → BitVec 64) (ZMod p)`:

* **Forward** (`map0`): the relation `R limbs x := ((limbVal n limbs : ZMod p) = x)`
  is the graph of the limb-array decoder `limbs ↦ (limbVal n limbs : ZMod p)`,
  forgotten to `⟨⟩` at the `∀`-rule level.
* **Backward** (`map2a`): the section `sec x := toLimbs n x.val` splits `x.val`
  into its base-`2^64` digits, and `map_in_R` is the retraction law
  `((limbVal n (toLimbs n x.val) : ZMod p) = x)`. This is *not* `map2b` — the
  decoder is not injective (distinct limb arrays reduce equally when
  `p < 2^(64·n)`), so the class stays asymmetric, exactly as in the single-limb
  case.

The crux is the base-`2^64` **recomposition** lemma `limbVal_toLimbs`: for
`v < 2^(64·n)`, splitting `v` into digits and Horner-recomposing recovers `v`. -/

/-- Little-endian base-`2^64` value of a limb array, `∑ᵢ (limbs i).toNat · 2^(64·i)`,
    written as the structural Horner fold
    `(limbs 0).toNat + 2^64 · limbVal n (Fin.tail limbs)`. This is the `Fin`-indexed
    analogue of `Cios4LimbProven.valLimbs` / `FormosaSpecBridge.limbsNat`. -/
def limbVal : (n : ℕ) → (Fin n → BitVec 64) → ℕ
  | 0,     _ => 0
  | n + 1, f => (f 0).toNat + 2 ^ 64 * limbVal n (Fin.tail f)

/-- The canonical section: split `v` into its base-`2^64` little-endian digits,
    limb `i` being `(v / 2^(64·i)) % 2^64`. -/
def toLimbs (n : ℕ) (v : ℕ) : Fin n → BitVec 64 :=
  fun i => BitVec.ofNat 64 (v / 2 ^ (64 * i.val) % 2 ^ 64)

@[simp] theorem limbVal_zero (f : Fin 0 → BitVec 64) : limbVal 0 f = 0 := rfl

theorem limbVal_succ (n : ℕ) (f : Fin (n + 1) → BitVec 64) :
    limbVal (n + 1) f = (f 0).toNat + 2 ^ 64 * limbVal n (Fin.tail f) := rfl

/-- The tail of `toLimbs (n+1) v` is `toLimbs n (v / 2^64)`: dropping the low limb
    is dividing out the low `2^64`. -/
theorem toLimbs_tail (n : ℕ) (v : ℕ) :
    Fin.tail (toLimbs (n + 1) v) = toLimbs n (v / 2 ^ 64) := by
  funext i
  simp only [Fin.tail, toLimbs, Fin.val_succ]
  have h : (64 : ℕ) * (i.val + 1) = 64 + 64 * i.val := by omega
  rw [h, pow_add, ← Nat.div_div_eq_div_mul]

/-! ## The recomposition (retraction) lemma -/

/-- **Base-`2^64` recomposition.** For `v < 2^(64·n)`, splitting `v` into its
    base-`2^64` digits and Horner-recomposing recovers `v` exactly. This is the
    crux retraction law behind the multi-limb section. Proved by induction on `n`
    with the little-endian peel `v = v % 2^64 + 2^64 · (v / 2^64)`. -/
theorem limbVal_toLimbs (n : ℕ) (v : ℕ) (hv : v < 2 ^ (64 * n)) :
    limbVal n (toLimbs n v) = v := by
  induction n generalizing v with
  | zero =>
    have hv0 : v = 0 := by simpa using hv
    simp [limbVal_zero, hv0]
  | succ n ih =>
    have hlt : v / 2 ^ 64 < 2 ^ (64 * n) := by
      apply Nat.div_lt_of_lt_mul
      calc v < 2 ^ (64 * (n + 1)) := hv
        _ = 2 ^ 64 * 2 ^ (64 * n) := by rw [← pow_add]; congr 1; omega
    rw [limbVal_succ, toLimbs_tail, ih (v / 2 ^ 64) hlt]
    show (toLimbs (n + 1) v 0).toNat + 2 ^ 64 * (v / 2 ^ 64) = v
    simp only [toLimbs, Fin.val_zero, Nat.mul_zero, pow_zero, Nat.div_one,
      BitVec.toNat_ofNat, Nat.mod_mod]
    exact Nat.mod_add_div v (2 ^ 64)

/-! ## The multi-limb split surjection `(Fin n → BitVec 64) ↠ ZMod p` -/

/-- The multi-limb limb-array→field split surjection as a `Param .map0 .map2a`
    retraction. `p ≤ 2^(64·n)` is the multi-limb no-overflow bound (`n` 64-bit
    limbs hold every residue).

    Relation `R limbs x := ((limbVal n limbs : ZMod p) = x)` (graph of the
    base-`2^64` limb-array decoder). Forward is the trivial `map0`. Backward is
    `map2a`: section `sec x := toLimbs n x.val` with `map_in_R` the retraction
    `((limbVal n (toLimbs n x.val) : ZMod p) = x)`. The section law reduces (via
    `limbVal_toLimbs`, applicable since `x.val < p ≤ 2^(64·n)`) to
    `ZMod.natCast_rightInverse`. It is *not* `map2b`: the decoder is not
    injective, so the class is asymmetric. Generalizes `limbFieldParam` (the
    `n = 1` case). -/
def multiLimbFieldParam (n p : ℕ) [NeZero p] (hp : p ≤ 2 ^ (64 * n)) :
    Param .map0 .map2a (Fin n → BitVec 64) (ZMod p) where
  R := fun limbs x => ((limbVal n limbs : ZMod p) = x)
  fwd := ⟨⟩
  bwd :=
    ⟨fun x => toLimbs n x.val,
     fun x limbs (h : toLimbs n x.val = limbs) => by
       subst h
       show ((limbVal n (toLimbs n x.val) : ZMod p) = x)
       rw [limbVal_toLimbs n x.val (lt_of_lt_of_le (ZMod.val_lt x) hp)]
       exact ZMod.natCast_rightInverse x⟩

/-! ## Multi-limb store congruence (the `R_forall`-over-`Fin n` view)

A multi-limb store *is* a dependent function `Fin n → BitVec 64`. Two stores
that agree limb-by-limb — packaged as a `Transfer.Param.R_forall` over the
diagonal on `Fin n` with the equality fiber on `BitVec 64` — decode to the same
base-`2^64` value. This reads `limbVal` congruence off the store relation: it is
the `R_forall`-over-`Fin n` view of the limb store, the multi-limb analogue of
the single-limb `LimbStoreRefines`/`limbLeaf_hcongr` leaf.

Note this is a *decoder congruence* (equal inputs, equal output), a fundamentally
different fact from `limbVal_toLimbs`, which is the base-`2^64` *recomposition*
identity `limbVal ∘ toLimbs = id` on the in-range interval — not a congruence and
not `R_forall`-shaped. -/

/-- **`limbVal` respects limb-by-limb agreement.** Two limb stores that agree at
    every index decode to the same base-`2^64` value. The base lemma behind the
    `R_forall` store-congruence view. -/
theorem limbVal_congr {n : ℕ} {s1 s2 : Fin n → BitVec 64}
    (h : ∀ i, s1 i = s2 i) : limbVal n s1 = limbVal n s2 := by
  have heq : s1 = s2 := funext h
  rw [heq]

/-- **Multi-limb store congruence, the `R_forall`-over-`Fin n` view.** Two limb
    stores related by `R_forall` over the diagonal on `Fin n` with the equality
    fiber on `BitVec 64` (i.e. agreeing limb-by-limb, expressed relationally)
    decode to the same base-`2^64` value. The store relation is precisely the
    dependent-Π relation `R_forall` at the `Fin n`-indexed limb family. -/
theorem limbVal_hcongr {n : ℕ} {s1 s2 : Fin n → BitVec 64}
    (hs : Transfer.Param.R_forall
            (B := fun _ => BitVec 64) (B' := fun _ => BitVec 64)
            (Transfer.Param.HCongrConnection.paramEqDom (Fin n))
            (Transfer.Param.HCongrConnection.paramEqFam (BitVec 64)) s1 s2) :
    limbVal n s1 = limbVal n s2 :=
  limbVal_congr (fun i => hs i i rfl)

/-- Field-level form of `limbVal_hcongr`: limb-by-limb agreeing stores decode to
    the same field element `ZMod p`. -/
theorem limbVal_hcongr_field {n p : ℕ} [NeZero p] {s1 s2 : Fin n → BitVec 64}
    (hs : Transfer.Param.R_forall
            (B := fun _ => BitVec 64) (B' := fun _ => BitVec 64)
            (Transfer.Param.HCongrConnection.paramEqDom (Fin n))
            (Transfer.Param.HCongrConnection.paramEqFam (BitVec 64)) s1 s2) :
    ((limbVal n s1 : ZMod p)) = ((limbVal n s2 : ZMod p)) := by
  rw [limbVal_hcongr hs]

/-! ## Multi-limb store↔field leaf as heterogeneous congruence

The multi-limb analogue of the single-limb `limbLeaf_hcongr`: an environment-view
of stores `S : E → (Fin n → BitVec 64)` (a whole limb array per environment) and
its abstract field view `X : E → ZMod p`, related over the `multiLimbFieldParam`
fiber, exhibit the machine-store↔field-value relation
`((limbVal n (S e) : ZMod p) = X e)` as `hcongr_hetero` across the
multi-limb-array→field change of representation (a genuinely different source
type `Fin n → BitVec 64` on the left). -/

/-- The multi-limb store-refinement relation: an environment-indexed limb store
    `S : E → (Fin n → BitVec 64)` refines a field store `X : E → ZMod p` when they
    are `R_forall`-related over the `multiLimbFieldParam` fiber. Unfolds to
    `∀ e e' (_ : e = e'), (limbVal n (S e) : ZMod p) = X e'`. -/
def MultiLimbStoreRefines (E : Type) (n p : ℕ) [NeZero p] (hp : p ≤ 2 ^ (64 * n))
    (S : E → (Fin n → BitVec 64)) (X : E → ZMod p) : Prop :=
  Transfer.Param.R_forall (B := fun _ => (Fin n → BitVec 64)) (B' := fun _ => ZMod p)
    (Transfer.Param.HCongrConnection.paramEqDom E)
    (fun _ _ _ => multiLimbFieldParam n p hp) S X

/-- **Multi-limb value leaf as heterogeneous congruence.** From a multi-limb store
    refinement and equal environments `e = e'`, the machine limb store `S e` and
    the field value `X e'` are related by the base-`2^64` decoder:
    `(limbVal n (S e) : ZMod p) = X e'`. This is `hcongr_hetero` at the
    `multiLimbFieldParam` fiber. -/
theorem multiLimbLeaf_hcongr {E : Type} (n p : ℕ) [NeZero p] (hp : p ≤ 2 ^ (64 * n))
    {S : E → (Fin n → BitVec 64)} {X : E → ZMod p}
    (hs : MultiLimbStoreRefines E n p hp S X) {e e' : E} (he : e = e') :
    ((limbVal n (S e) : ZMod p) = X e') :=
  Transfer.Param.HCongrConnection.hcongr_hetero (B := fun _ => (Fin n → BitVec 64))
    (B' := fun _ => ZMod p) (Transfer.Param.HCongrConnection.paramEqDom E)
    (fun _ _ _ => multiLimbFieldParam n p hp) hs he

end Transfer.Param
