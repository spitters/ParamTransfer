/-
Copyright (c) 2026 ParamTransfer Contributors. All rights reserved.
Released under the GNU Lesser General Public License v3.0 (LGPL-3.0) as described in the file LICENSE.
Authors: ParamTransfer Contributors
-/
import Transfer.Integrations.ParamTripleTransfer
import Mathlib.Tactic

/-!
# An effectful transfer across a value-type change, proved by `mvcgen`

A self-contained companion to `Examples/HexEffectful.lean`. Where that example
transfers a triple across a *storage* change at the same value type (`ℤ`, related
by equality), this one changes the value *type*: a `do`-block over `ℕ` transfers to
the same computation over `ℤ`, related by the cast `Rα a a' := ((a : ℤ) = a')`.

The recipe is the one the library runs everywhere, here at the monad level:

1. write the concrete program and prove its triple with `mvcgen` (`natProg_spec`);
2. build the Kleisli witness `RComp Rα` relating the two programs, assembled
   from `RComp.pure` / `RComp.bind` and mirroring the `do`-block
   (`natIntProg_RComp`);
3. move the triple to the other representation with `triple_transfer`, deriving
   the target spec instead of re-proving it (`intProg_spec`).

The witness is assembled by hand from the `pure` / `bind` rules — the discipline a
`param`-style tactic would automate. The effectful-loop / early-exit case (a `for`
loop rather than straight-line `bind`s) is `RComp.forIn_list` in
`Integrations/ParamForIn.lean`.
-/

set_option autoImplicit false

open Std.Do

namespace Transfer.Param

/-! ## Two programs, one shape, different value types -/

/-- The concrete program over `ℕ`: a two-`bind` `do`-block. -/
def natProg (n m : Nat) : Id Nat := do
  let a ← pure (n + 1)
  let b ← pure (m + 1)
  pure (a + b)

/-- The same program over `ℤ`. -/
def intProg (n m : Int) : Id Int := do
  let a ← pure (n + 1)
  let b ← pure (m + 1)
  pure (a + b)

/-! ## Step 1 — the source triple, by `mvcgen` -/

/-- Correctness of the `ℕ` program, discharged by `mvcgen`. -/
theorem natProg_spec (n m : Nat) :
    ⦃⌜True⌝⦄ (natProg n m) ⦃⇓r => ⌜r = (n + 1) + (m + 1)⌝⦄ := by
  mvcgen [natProg]

/-! ## Step 2 — the `RComp` witness across the cast relation

Assembled leaf-by-leaf from `RComp.pure` / `RComp.bind`, mirroring the `do`-block:
each `pure` read is related by the cast on that value, and the final combination
by the cast being additive. -/

/-- The two programs are `RComp`-related at the cast relation
    `Rα a a' := ((a : ℤ) = a')`: reading `n + 1` on the left decodes to `↑n + 1` on
    the right, likewise `m + 1`, and their sums agree under the cast. -/
theorem natIntProg_RComp (n m : Nat) :
    RComp (M := Id) (fun (a : Nat) (a' : Int) => (a : Int) = a')
      (natProg n m) (intProg (n : Int) (m : Int)) :=
  RComp.bind (RComp.pure _ (by push_cast; ring))
    (fun a a' (ha : (a : Int) = a') =>
      RComp.bind (RComp.pure _ (by push_cast; ring))
        (fun b b' (hb : (b : Int) = b') =>
          RComp.pure _ (by
            show ((a + b : Nat) : Int) = a' + b'
            rw [← ha, ← hb]; push_cast; ring)))

/-! ## Step 3 — the transferred triple, derived not re-proved

`triple_transfer` carries `natProg_spec` across the witness. The postcondition
relatedness turns the `ℕ` postcondition `r = (n+1)+(m+1)` into the `ℤ` one along
the cast; nothing about `intProg` is re-verified. -/

/-- The `ℤ` program's triple, obtained from the `ℕ` one by transfer. -/
theorem intProg_spec (n m : Nat) :
    ⦃⌜True⌝⦄ (intProg (n : Int) (m : Int))
      ⦃⇓r => ⌜r = ((n : Int) + 1) + ((m : Int) + 1)⌝⦄ := by
  refine triple_transfer (Rα := fun (a : Nat) (a' : Int) => (a : Int) = a')
    (natIntProg_RComp n m) ?_ (natProg_spec n m)
  intro a a' (haa : (a : Int) = a') (hc : a = n + 1 + (m + 1))
  refine (?_ : a' = (n : Int) + 1 + ((m : Int) + 1))
  subst haa; subst hc; push_cast; ring

/-! ## Axiom audit -/

section AxiomAudit

/-- info: 'Transfer.Param.intProg_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms intProg_spec

end AxiomAudit

end Transfer.Param
