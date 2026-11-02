# ParamTransfer — scope and extension points

This note is for contributors. It states the boundaries of the engine and the
place in the source where each one can be extended.

## Scope and extension points

* **The universe-valued boundary.** The engine is univalence-free. Between values, the
  arrow and dependent-Π rules reach every level up to `map4` with inputs at `map3` at
  most (`arrowReq`, `forallReq`), because the relations are `Prop`-valued. A statement
  quantifying over a motive `P : A → Type` needs a relation on `Type`; universe-valued
  fibers of heterogeneous congruence sit there too. The `equiv` level (`map4`) is
  refused with a report (`Base/LevelRefusal.lean`), because type-level univalence
  stated through Lean's `Eq` is inconsistent
  (`UnivalenceStatus.univalence_inconsistent`). The fragment is wider than Coq's
  univalence-free cap, because `funext` is a theorem in Lean.
  Relating universes in Lean would need an internal bridge or parametric interval in
  place of `Eq`, as in the internal-parametricity line of work (Cavallo–Harper,
  `agda --bridges`).
* **Level inference** runs over a type spine and an `Expr` front end
  (non-dependent `→` vs dependent `Π`, constant-head leaves, registry lower
  bounds). Operator and higher-order application spines and universe polymorphism
  are outside the traversal; `Synthesis/ParamInfer.lean` is where they would be
  added.
* **The term translator** is registry-bound: `#transfer` / `translateAll` raise an
  error on an unregistered constant and do not guess names.
  `Mathlib.Tactic.Translate`, the framework under `@[to_additive]`, is the
  reference design for that traversal.
* **`deriving Param`** covers non-recursive and uniform-recursive inductives. It
  declines nested, reflexive, and indexed families up front, so that another
  handler can take them (`Deriving/ParamDeriveHandler.lean`).
* **`TransferDom`** covers diagonal domains and retractions (`ℤ ↠ ZMod p`). Other
  non-diagonal domains (`F ↔ limbs`, group ↔ bytes) have the same shape: a
  registered backward decoder plus the predicate that the `∀`-rule emits.
* **The `param_auto` dispatch strategy** is the coordinator's single tuning point.
  It is a `first`-cascade (`rfl`, `param_solve`, `rcongr`, `norm_cast`, `gcongr`,
  `grind`, `assumption`). A goal-directed router that inspects the relation head
  and calls the matching solver can replace the cascade behind the same call site
  without changing any proof (`Congruence/ParamAuto.lean`).

## Related material

- Attribution and provenance: `ATTRIBUTION.md`.
- Build, manual, and API-reference instructions: `BUILDING.md`.
- Axiom-ledger hygiene check: `Transfer/Audit.lean` (CI builds `Transfer.Audit`).
