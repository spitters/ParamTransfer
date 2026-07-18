# ParamTransfer — internal notes

Contributor-facing notes kept out of the public README. Scope boundaries and
extension points live here.

## Scope & frontier

Each boundary marks a natural extension point.

* **The `map4` / universe-valued boundary.** The engine is univalence-free, capped
  at `map3`. Transfer into a `Type`-valued motive (rather than `Prop`) needs
  `Map2a_forall`, whose domain `Param` sits at `map4`; universe-valued fibers of
  heterogeneous congruence sit there too. The `equiv` level (`map4`) is refused with
  a report (`Base/LevelRefusal.lean`), because type-level univalence stated through
  Lean's `Eq` is inconsistent (`UnivalenceStatus.univalence_inconsistent`). This is
  the defining boundary of the approach: `map0`–`map3` is the whole consistent space,
  and it is wider than Coq's univalence-free cap because Lean's `funext` is a theorem.
  Recovering `map4` in Lean would need an internal bridge/parametric interval rather
  than `Eq` (see the internal-parametricity lineage: Cavallo–Harper, `agda --bridges`).
* **Level inference** runs over a type spine and an `Expr` front-end (non-dependent
  `→` vs dependent `Π`, const-head leaves, registry lower bounds). Not yet walked:
  operator and higher-order application spines, and universe polymorphism
  (`Synthesis/ParamInfer.lean`).
* **The term translator** is registry-bound: `#transfer` / `translateAll` raise on an
  unregistered constant, and do not name-guess. `Mathlib.Tactic.Translate`, the
  framework `@[to_additive]` rests on, is the reference for that walk.
* **`deriving Param`** covers non-recursive and uniform-recursive inductives. Nested,
  reflexive, and indexed families are declined up front so another handler can take
  over (`Deriving/ParamDeriveHandler.lean`).
* **`TransferDom`** covers diagonal domains and retractions (`ℤ ↠ ZMod p`). Other
  non-diagonal domains (`F ↔ limbs`, group ↔ bytes) follow the same shape: a
  registered backward decoder plus the predicate the `∀`-rule emits.

## Related internal material

- Attribution and provenance: `ATTRIBUTION.md`.
- Build, manual, and API-reference instructions: `BUILDING.md`.
- Axiom-ledger hygiene tripwire: `Transfer/Audit.lean` (CI builds `Transfer.Audit`).
