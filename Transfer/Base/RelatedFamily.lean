/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: Bas Spitters
-/
module

public import Transfer.Base.RelatedOn

/-!
# Element-wise related families and arrays

A square of `Transfer.Base.Related` relates one abstract value to one encoded
value. This file relates a finite family `s : Fin n → A` to a container of
encoded values, entry by entry, and gives the rule for reading an entry.

* `RelatedFamily enc s f`: the reader `f : ℕ → α` returns `enc (s i)` at every
  `i : Fin n`. The reader is any function of the position, for example
  `fun k => a[k]!`, or a read of a table at an offset `fun k => get t (o + k)`.
* `RelatedArray enc s a`: the array `a` holds `enc (s i)` at every position
  `i : Fin n`.

The encoding, the family and its length are `outParam`s: the container determines
them, so a rewriting rule whose left-hand side mentions only the container obtains
the family by instance resolution.

## Main results

* `RelatedFamily.apply_eq`: `f k = enc (s ⟨k, hk⟩)`, the rewriting form.
* `rcongrFamily`, `rcongrGetElem`: reading position `k` of a related reader or
  array gives a value related to `s i`, under the guard `k = i`. They are the leaf
  rules of the guarded descent.
* `RelatedArray.getElem_eq`, `RelatedArray.eq_ofFn`: the entries of a related
  array, and the array itself when its size is `n`.
* `RelatedArray.ofFn`, `RelatedArray.setIfInBounds`: the array of encodings is
  related to the family, and a functional update of the family is related to the
  update of the array.
* `RelatedArray.getElem!_family`: a related array read by `a[k]!` is a related
  reader.

`transfer_guard_leaf` is the extensible tactic of leaf rules that `param_guard`
tries on a `Related` goal after the operation squares. Each alternative closes the
goal up to one guard goal. A `macro_rules` for it registers the reading rule of
another container.
-/

@[expose] public section

set_option autoImplicit false

namespace Transfer

universe u

/-- `RelatedFamily enc s f`: the reader `f` returns at every position `i : Fin n`
    the encoding of `s i`. -/
class RelatedFamily {A : outParam (Type u)} {α : Type u} {n : outParam ℕ}
    (enc : outParam (A → α)) (s : outParam (Fin n → A)) (f : ℕ → α) : Prop where
  /-- The reader agrees with the encoded family at every position. -/
  comm : ∀ i : Fin n, enc (s i) = f i

/-- Reading a related reader at an in-range position gives the encoding of the
    entry. -/
theorem RelatedFamily.apply_eq {A α : Type u} {n : ℕ} {enc : A → α} {s : Fin n → A}
    (f : ℕ → α) [h : RelatedFamily enc s f] (k : ℕ) (hk : k < n) :
    f k = enc (s ⟨k, hk⟩) := (h.comm ⟨k, hk⟩).symm

/-- Reading rule for a related reader: under the guard `k = i`, the value `f k` is
    related to `s i`. -/
theorem rcongrFamily {A α : Type u} {n : ℕ} {enc : A → α} {s : Fin n → A}
    (f : ℕ → α) [h : RelatedFamily enc s f] {i : Fin n} {k : ℕ} (hg : k = i) :
    Related enc (s i) (f k) where
  rel := by subst hg; exact h.comm i

/-- `RelatedArray enc s a`: the array `a` holds at every position `i : Fin n` the
    encoding of `s i`. -/
class RelatedArray {A : outParam (Type u)} {α : Type u} {n : outParam ℕ}
    (enc : outParam (A → α)) (s : outParam (Fin n → A)) (a : Array α) : Prop where
  /-- Position `i` of the array is in range and holds `enc (s i)`. -/
  getElem?_eq : ∀ i : Fin n, a[i.val]? = some (enc (s i))

namespace RelatedArray

variable {A α : Type u} {n : ℕ} {enc : A → α} {s : Fin n → A} {a : Array α}

/-- A related array has at least `n` entries. -/
theorem lt_size [h : RelatedArray enc s a] {k : ℕ} (hk : k < n) : k < a.size := by
  have := h.getElem?_eq ⟨k, hk⟩
  by_contra hc
  simp [Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at this

/-- Entry `k` of a related array is the encoding of `s ⟨k, hk⟩`. -/
theorem getElem_eq [h : RelatedArray enc s a] (k : ℕ) (hk : k < n) :
    a[k]'(lt_size (enc := enc) (s := s) hk) = enc (s ⟨k, hk⟩) := by
  have := h.getElem?_eq ⟨k, hk⟩
  rw [Array.getElem?_eq_getElem (lt_size (enc := enc) (s := s) hk)] at this
  exact Option.some.inj this

/-- The array of encodings of a family is related to the family. -/
instance ofFn (enc : A → α) (s : Fin n → A) :
    RelatedArray enc s (Array.ofFn fun i => enc (s i)) where
  getElem?_eq i := by simp

/-- A related array of size `n` is the array of encodings of the family. -/
theorem eq_ofFn [RelatedArray enc s a] (hs : a.size = n) :
    a = Array.ofFn fun i => enc (s i) := by
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    rw [getElem_eq (enc := enc) (s := s) i (hs ▸ h1)]; simp

/-- Functional update: writing a value related to `x` at position `i` gives an
    array related to the family updated at `i` with `x`. -/
theorem setIfInBounds [RelatedArray enc s a] (i : Fin n) {x : A} {x' : α}
    (hx : Related enc x x') :
    RelatedArray enc (Function.update s i x) (a.setIfInBounds i x') where
  getElem?_eq j := by
    have hi := lt_size (enc := enc) (s := s) (a := a) i.isLt
    have hj := getElem?_eq (enc := enc) (s := s) (a := a) j
    by_cases hij : j = i
    · subst hij; simp [hi, hx.rel]
    · have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h.symm)
      simp [hne, hij, hj]

/-- A related array read by `a[k]!` is a related reader. -/
instance getElem!_family [Inhabited α] [RelatedArray enc s a] :
    RelatedFamily enc s (fun k => a[k]!) where
  comm i := by
    have h := lt_size (enc := enc) (s := s) (a := a) i.isLt
    simp [getElem!_pos, h, getElem_eq (enc := enc) (s := s) i.val i.isLt]

end RelatedArray

/-- Reading rule for a related array: under the guard `k = i`, the entry `a[k]` is
    related to `s i`. -/
theorem rcongrGetElem {A α : Type u} {n : ℕ} {enc : A → α} {s : Fin n → A} {a : Array α}
    [RelatedArray enc s a] {i : Fin n} {k : ℕ} {hk : k < a.size} (hg : k = i) :
    Related enc (s i) (a[k]'hk) where
  rel := by
    subst hg
    exact (RelatedArray.getElem_eq (enc := enc) (s := s) i.val i.isLt).symm

/-- The leaf rules of the guarded descent for reading a container. Each
    alternative closes a goal `Related enc (s i) t'` up to one guard goal.
    Extensible: a `macro_rules` for `transfer_guard_leaf` adds an alternative
    tried before the default one, `refine rcongrGetElem ?_`. -/
syntax "transfer_guard_leaf" : tactic

macro_rules
  | `(tactic| transfer_guard_leaf) => `(tactic| refine rcongrGetElem ?_)

end Transfer
