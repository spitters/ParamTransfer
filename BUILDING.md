# Building

All build instructions for the library, the manual, and the API reference live
here. Other documents link to this file rather than repeat the commands.

## Prerequisites

The Lean toolchain pinned in `lean-toolchain`, installed via
[elan](https://github.com/leanprover/elan). The library's only dependency is
Mathlib.

## The library

```sh
lake exe cache get            # fetch prebuilt Mathlib oleans — run this FIRST
LAKE_JOBS=6 lake build Transfer
```

The `lake exe cache get` step downloads Mathlib's compiled `.olean`s, which avoids
a Mathlib source rebuild. The `LAKE_JOBS` cap holds peak memory down on small
machines; a large machine can drop it. The sibling libraries build with
`lake build ReprTransfer ReprTransferExpr`, and the axiom-ledger hygiene check with
`lake build Transfer.Audit`.

## Using the library in another package

```lean
require paramTransfer from git
  "https://github.com/spitters/ParamTransfer.git" @ "main"
```

Then `import Transfer`. The library requires only Mathlib; the documentation
toolchain lives in the separate `docs/` package.

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
