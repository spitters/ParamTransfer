/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
import Transfer.Hierarchy.ParamHierarchy
import Transfer.Hierarchy.ParamEquiv

/-!
# Relation **composition** (`Param_trans`)

A faithful Lean port of Trocq's `std/generic/Param_trans.v`
(`coq-community/trocq`) — the rule that composes two annotated relations
`Param m n A B` and `Param m n B C` into one on `A C`. It is the transitivity
half of the relational-PER structure (`Param.symm` in `ParamHierarchy.lean` is
the symmetry half), and the mechanism behind the paper's bitvector-encoding
*chaining* (`A ↪ B ↪ C`).

## The composite relation

For `R : A → B → Prop` and `S : B → C → Prop` the composite is the usual
existential glue

```
R_trans R S a c := ∃ b, R a b ∧ S b c
```

(Coq's `Param_trans` uses the `Σ`-glued relation; over `Prop`-valued `R` the
`∃` form is the right one — proof irrelevance collapses the choice of witness
that would otherwise matter at `map4`.)

## Which classes compose

The forward map of the composite is the function composition `S.map ∘ R.map`,
and every `MapHas` field lifts **without univalence**:

| level | forward field | how it lifts |
|---|---|---|
| `map0` | (none)         | trivial |
| `map1` | `map`          | `S.fwd.map ∘ R.fwd.map` |
| `map2a`| `map_in_R`     | witness `b := R.map a`, then chase both inclusions |
| `map2b`| `R_in_map`     | `R.R_in_map` then `S.R_in_map` (no funext needed: maps, not functions) |
| `map3` | both           | combine the two above |

So `Param_trans` covers map0–map3 in both directions (the backward
direction is the same construction on `symRel`, which is itself a composition —
`symRel (R_trans R S) = R_trans (symRel S) (symRel R)`, the order flips). The
`map4` coherence `R_in_mapK` is the only field that does not compose for
free even on `Prop`: the round-trip `map_in_R (R_in_map r)` of the composite
mixes the two witnesses, and recovering `r` needs the equivalence
coherence (univalence territory). So `map0`–`map3` are fully proved and
`map4` is documented as the residual, exactly as the arrow/forall/data rules do.
-/

set_option autoImplicit false

universe u

namespace Transfer.Param

variable {A B C : Type u}

/-! ## The composite relation `R_trans` (Coq `Param_trans` relation) -/

/-- Trocq composite relation: `a` relates to `c` when there is an intermediate
    `b` with `R a b` and `S b c`. The level parameters stay polymorphic — the
    relation touches only the `R` fields. -/
def R_trans {mR nR mS nS : MapClass}
    (P : Param mR nR A B) (Q : Param mS nS B C) : A → C → Prop :=
  fun a c => ∃ b, P.R a b ∧ Q.R b c

/-- The flip of a composite is the composite of the flips, with order reversed:
    `symRel (R_trans P Q) = R_trans (symRel S) (symRel R)`. This is the
    bookkeeping lemma that lets the backward map reuse the same forward
    construction. -/
theorem symRel_R_trans {mR nR mS nS : MapClass}
    (P : Param mR nR A B) (Q : Param mS nS B C) :
    symRel (R_trans P Q) = (fun c a => ∃ b, Q.R b c ∧ P.R a b) := by
  funext c a
  simp only [symRel, R_trans]
  apply propext
  constructor
  · rintro ⟨b, hab, hbc⟩; exact ⟨b, hbc, hab⟩
  · rintro ⟨b, hbc, hab⟩; exact ⟨b, hab, hbc⟩

/-! ## The forward `MapHas` records compose (map0–map3) -/

/-- `map0`: nothing to compose. -/
def Map0_trans {mR nR mS nS : MapClass}
    (P : Param mR nR A B) (Q : Param mS nS B C) :
    Map0Has (R_trans P Q) := ⟨⟩

/-- `map1`: the forward map of the composite is `S.map ∘ R.map`. Needs both
    forward maps. -/
def Map1_trans {nR nS : MapClass}
    (P : Param .map1 nR A B) (Q : Param .map1 nS B C) :
    Map1Has (R_trans P Q) :=
  ⟨fun a => Q.fwd.map (P.fwd.map a)⟩

/-- `map2a`: the composite map's graph is included in `R_trans`. Pick the
    intermediate witness `b := R.map a`; then `R a b` by `R.map_in_R rfl`, and
    `S b c` by `S.map_in_R` (since `S.map b = c`). Needs both forward
    `map2a`. -/
def Map2a_trans {nR nS : MapClass}
    (P : Param .map2a nR A B) (Q : Param .map2a nS B C) :
    Map2aHas (R_trans P Q) where
  map := fun a => Q.fwd.map (P.fwd.map a)
  map_in_R := by
    intro a c e
    subst e
    exact ⟨P.fwd.map a, P.fwd.map_in_R a (P.fwd.map a) rfl,
      Q.fwd.map_in_R (P.fwd.map a) (Q.fwd.map (P.fwd.map a)) rfl⟩

/-- `map2b`: `R_trans`-relatedness implies the composite map sends `a` to `c`.
    From the witness `b`: `R.R_in_map` gives `R.map a = b`, `S.R_in_map` gives
    `S.map b = c`; compose. No funext is needed — these are maps on data,
    not function spaces, so this lifts univalence-free (unlike Coq's funext
    gate on the arrow rule). Needs both forward `map2b`. -/
def Map2b_trans {nR nS : MapClass}
    (P : Param .map2b nR A B) (Q : Param .map2b nS B C) :
    Map2bHas (R_trans P Q) where
  map := fun a => Q.fwd.map (P.fwd.map a)
  R_in_map := by
    rintro a c ⟨b, hab, hbc⟩
    have h1 : P.fwd.map a = b := P.fwd.R_in_map a b hab
    have h2 : Q.fwd.map b = c := Q.fwd.R_in_map b c hbc
    rw [h1, h2]

/-- `map3`: both inclusions; the composite is the graph of `S.map ∘ R.map`.
    Needs both forward `map3`. -/
def Map3_trans {nR nS : MapClass}
    (P : Param .map3 nR A B) (Q : Param .map3 nS B C) :
    Map3Has (R_trans P Q) where
  map := fun a => Q.fwd.map (P.fwd.map a)
  map_in_R := by
    intro a c e
    subst e
    exact ⟨P.fwd.map a, P.fwd.map_in_R a (P.fwd.map a) rfl,
      Q.fwd.map_in_R (P.fwd.map a) (Q.fwd.map (P.fwd.map a)) rfl⟩
  R_in_map := by
    rintro a c ⟨b, hab, hbc⟩
    have h1 : P.fwd.map a = b := P.fwd.R_in_map a b hab
    have h2 : Q.fwd.map b = c := Q.fwd.R_in_map b c hbc
    rw [h1, h2]

/-! ## The backward records compose

`symRel (R_trans P Q)` is the composite of the flipped relations (in reverse
order). The backward `MapHas` is therefore built from `Q.bwd` then `P.bwd`,
mirroring the forward construction. The `map0`–`map3` backward builders are
parameterised by the backward levels. -/

/-- Backward `map1`: the backward map of the composite is `R.comap ∘ S.comap`
    (the flip of `S.map ∘ R.map`). Needs both backward maps. -/
def Map1_trans_bwd {mR mS : MapClass}
    (P : Param mR .map1 A B) (Q : Param mS .map1 B C) :
    Map1Has (symRel (R_trans P Q)) :=
  ⟨fun c => P.bwd.map (Q.bwd.map c)⟩

/-- Backward `map2a`. `P.bwd : MapHas .map2a (symRel P.R)`, so
    `P.bwd.map : B → A` and `P.bwd.map_in_R : ∀ b a, P.bwd.map b = a → P.R a b`.
    Pick the witness `b := S.comap c`. Needs both backward `map2a`. -/
def Map2a_trans_bwd {mR mS : MapClass}
    (P : Param mR .map2a A B) (Q : Param mS .map2a B C) :
    Map2aHas (symRel (R_trans P Q)) where
  map := fun c => P.bwd.map (Q.bwd.map c)
  map_in_R := by
    intro c a e
    subst e
    -- goal: symRel (R_trans P Q) c (P.bwd.map (Q.bwd.map c))
    -- i.e. R_trans P Q (P.bwd.map (Q.bwd.map c)) c = ∃ b, P.R … b ∧ Q.R b c
    exact ⟨Q.bwd.map c,
      P.bwd.map_in_R (Q.bwd.map c) (P.bwd.map (Q.bwd.map c)) rfl,
      Q.bwd.map_in_R c (Q.bwd.map c) rfl⟩

/-- Backward `map2b`. `P.bwd.R_in_map : ∀ b a, P.R a b → P.bwd.map b = a`.
    Needs both backward `map2b`. -/
def Map2b_trans_bwd {mR mS : MapClass}
    (P : Param mR .map2b A B) (Q : Param mS .map2b B C) :
    Map2bHas (symRel (R_trans P Q)) where
  map := fun c => P.bwd.map (Q.bwd.map c)
  R_in_map := by
    rintro c a ⟨b, hab, hbc⟩
    -- hab : P.R a b, hbc : Q.R b c
    have h2 : Q.bwd.map c = b := Q.bwd.R_in_map c b hbc
    have h1 : P.bwd.map b = a := P.bwd.R_in_map b a hab
    rw [h2, h1]

/-- Backward `map3`. -/
def Map3_trans_bwd {mR mS : MapClass}
    (P : Param mR .map3 A B) (Q : Param mS .map3 B C) :
    Map3Has (symRel (R_trans P Q)) where
  map := fun c => P.bwd.map (Q.bwd.map c)
  map_in_R := by
    intro c a e
    subst e
    exact ⟨Q.bwd.map c,
      P.bwd.map_in_R (Q.bwd.map c) (P.bwd.map (Q.bwd.map c)) rfl,
      Q.bwd.map_in_R c (Q.bwd.map c) rfl⟩
  R_in_map := by
    rintro c a ⟨b, hab, hbc⟩
    have h2 : Q.bwd.map c = b := Q.bwd.R_in_map c b hbc
    have h1 : P.bwd.map b = a := P.bwd.R_in_map b a hab
    rw [h2, h1]

/-! ## `Param_trans`: the composition combinator

The combinator is exposed at the four diagonal levels `map0`–`map3` (forward and
backward equal), the shape the chaining demo and the registry use. Off-diagonal
mixes (`Param m n` with `m ≠ n`) compose by the same field builders above with
the appropriate level arguments; the diagonal instances are the
canonical entry points (with `Param_trans_map3_map0`, the embedding-chaining
shape, given explicitly). -/

/-- **`Param_trans` at `map0`** — relation composition with no structure. -/
def Param_trans_map0 (P : Param .map0 .map0 A B) (Q : Param .map0 .map0 B C) :
    Param .map0 .map0 A C where
  R := R_trans P Q
  fwd := ⟨⟩
  bwd := ⟨⟩

/-- **`Param_trans` at `map1`** — compose two forward+backward maps. -/
def Param_trans_map1 (P : Param .map1 .map1 A B) (Q : Param .map1 .map1 B C) :
    Param .map1 .map1 A C where
  R := R_trans P Q
  fwd := Map1_trans P Q
  bwd := Map1_trans_bwd P Q

/-- **`Param_trans` at `map2a`** — compose graph-inclusions both ways. -/
def Param_trans_map2a (P : Param .map2a .map2a A B) (Q : Param .map2a .map2a B C) :
    Param .map2a .map2a A C where
  R := R_trans P Q
  fwd := Map2a_trans P Q
  bwd := Map2a_trans_bwd P Q

/-- **`Param_trans` at `map2b`** — compose relation-inclusions both ways. -/
def Param_trans_map2b (P : Param .map2b .map2b A B) (Q : Param .map2b .map2b B C) :
    Param .map2b .map2b A C where
  R := R_trans P Q
  fwd := Map2b_trans P Q
  bwd := Map2b_trans_bwd P Q

/-- **`Param_trans` at `map3`** — the composite of two full graph relations is
    itself a full graph relation, in both directions, univalence-free. -/
def Param_trans_map3 (P : Param .map3 .map3 A B) (Q : Param .map3 .map3 B C) :
    Param .map3 .map3 A C where
  R := R_trans P Q
  fwd := Map3_trans P Q
  bwd := Map3_trans_bwd P Q

/-- **`Param_trans` for the embedding shape `map3 / map0`** — the exact level of
    `paramOfEmbedding`/`paramOfEquiv`-without-decoder. Composing two encodings
    `A ↪ B ↪ C` yields the chained encoding `A ↪ C` (forward `map3`, backward
    `map0`), the paper's bitvector-chaining pattern. -/
def Param_trans_map3_map0 (P : Param .map3 .map0 A B) (Q : Param .map3 .map0 B C) :
    Param .map3 .map0 A C where
  R := R_trans P Q
  fwd := Map3_trans P Q
  bwd := ⟨⟩

/-! ## Demos: chaining registered relations -/

section Demo

open Transfer

/-- Chaining two `ReprEmbeddingClass` encodings `A ↪ α ↪ β` into a single
    annotated relation `A ↔ β` (forward `map3`, backward `map0`) — the
    bitvector-chaining pattern: encode through an intermediate representation,
    then through the final one. -/
def paramChainEmbed {A α β : Type u}
    [ReprEmbeddingClass A α] [ReprEmbeddingClass α β] :
    Param .map3 .map0 A β :=
  Param_trans_map3_map0 (paramOfEmbedding (A := A) (α := α))
    (paramOfEmbedding (A := α) (α := β))

/-- The chained relation is the existential glue of the two encoding graphs:
    `A`-value `a` relates to `β`-value `c` iff some intermediate `α`-value `b`
    is `enc a` and `c` is `enc b`. -/
example {A α β : Type u} [ReprEmbeddingClass A α] [ReprEmbeddingClass α β]
    (a : A) (c : β) :
    (paramChainEmbed (A := A) (α := α) (β := β)).R a c ↔
      ∃ b, (ReprMapClass.enc a : α) = b ∧ (ReprMapClass.enc b : β) = c :=
  Iff.rfl

/-- The chained forward map is the composition of the two encoders, so it sends
    `a` to `enc (enc a)`. -/
example {A α β : Type u} [ReprEmbeddingClass A α] [ReprEmbeddingClass α β]
    (a : A) :
    (paramChainEmbed (A := A) (α := α) (β := β)).fwd.map a
      = (ReprMapClass.enc (ReprMapClass.enc a : α) : β) := rfl

/-- The chained forward map's graph is the composite relation (the `map3`
    `map_in_R` direction), so `a` relates to its double-encoding. -/
example {A α β : Type u} [ReprEmbeddingClass A α] [ReprEmbeddingClass α β]
    (a : A) :
    (paramChainEmbed (A := A) (α := α) (β := β)).R a
      ((ReprMapClass.enc (ReprMapClass.enc a : α) : β)) :=
  (paramChainEmbed (A := A) (α := α) (β := β)).fwd.map_in_R a _ rfl

/-! ### Diagonal (equality) chaining — `A ≃ B ≃ C` style at `map3` -/

/-- The diagonal at full `map3` both ways: `Eq` is the graph of `id`, with both
    inclusions identities. -/
def paramEqFull (T : Type u) : Param .map3 .map3 T T where
  R := Eq
  fwd := ⟨id, fun _ _ h => h, fun _ _ h => h⟩
  bwd := ⟨id, fun _ _ h => h.symm, fun _ _ h => h.symm⟩

/-- Composing the diagonal with itself stays the (existentially-presented)
    diagonal: `a` relates to `c` iff some `b` equals both, i.e. `a = c`. -/
example {T : Type u} (a c : T) :
    (Param_trans_map3 (paramEqFull T) (paramEqFull T)).R a c ↔ a = c := by
  constructor
  · rintro ⟨b, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, rfl⟩

/-- The composite of two diagonals has forward map `id ∘ id = id`. -/
example {T : Type u} (a : T) :
    (Param_trans_map3 (paramEqFull T) (paramEqFull T)).fwd.map a = a := rfl

/-- Symmetry and transitivity cohere: flipping a composite is a composite of
    flips. The relation underlying `(Param_trans_map3 P Q).symm` is `symRel`
    of the composite, which `symRel_R_trans` identifies. -/
example {T : Type u} :
    (Param_trans_map3 (paramEqFull T) (paramEqFull T)).symm.R
      = symRel (R_trans (paramEqFull T) (paramEqFull T)) := rfl

end Demo

end Transfer.Param
