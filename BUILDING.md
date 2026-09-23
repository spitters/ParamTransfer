# Building

All build instructions for the library, the manual, and the API reference live
here. Other documents link to this file rather than repeat the commands.

## Prerequisites

The Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.33.1`),
installed via [elan](https://github.com/leanprover/elan). The lakefile requires
two packages, both at tag `v4.33.1`: Mathlib, and
[CompPoly](https://github.com/Verified-zkEVM/CompPoly), which the CoqEAL example
library `TransferCoqEAL` uses. `lake-manifest.json` pins the resolved versions of
these, of their transitive dependencies (among them cslib), and of PolyFun and
loom2.

## The library

```sh
lake exe cache get            # fetch prebuilt Mathlib oleans — run this FIRST
LEAN_NUM_THREADS=6 lake build Transfer
```

The `lake exe cache get` step downloads Mathlib's compiled `.olean`s, which avoids
a Mathlib source rebuild. `LEAN_NUM_THREADS` bounds the number of concurrent Lean
workers and so bounds peak memory on small machines; a large machine can omit it.
Lake has no jobs flag and ignores `LAKE_JOBS`. The sibling libraries build with
`lake build ReprTransfer ReprTransferExpr`, and the axiom-ledger hygiene check with
`lake build Transfer.Audit`.

## Using the library in another package

```lean
require paramTransfer from git
  "https://github.com/spitters/ParamTransfer.git" @ "main"
```

Then `import Transfer`. The `Transfer` library imports Mathlib and not CompPoly;
CompPoly is built only for the `TransferCoqEAL` examples. The documentation
toolchain lives in the separate `docs/` and `docbuild/` packages.

## The manual

The Verso manual is its own package under `docs/`:

```sh
cd docs && lake build && lake exe transfer-manual --output _out
```

The output `docs/_out/html-single/index.html` is a single self-contained page that
opens in a browser without a server. Published copy:
[spitters.github.io/ParamTransfer](https://spitters.github.io/ParamTransfer/).

## The API reference

Per-declaration signatures and docstrings (no proof bodies) come from doc-gen4, in
the separate `docbuild/` package. A fresh clone builds it with:

```sh
cd docbuild && lake update && lake exe cache get && lake build Transfer:docs
```

The output is `docbuild/.lake/build/doc/`. Deploying it under `api/` next to the
manual keeps the manual's API-reference links resolvable. Published copy:
[spitters.github.io/ParamTransfer/api](https://spitters.github.io/ParamTransfer/api/).

## Continuous integration

The GitHub Actions workflow (`.github/workflows/ci.yml`) builds the library, runs
the axiom-ledger check (`Transfer.Audit`), and renders the manual, publishing the
manual and API reference to GitHub Pages from `main`.
