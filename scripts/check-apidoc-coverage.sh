#!/usr/bin/env bash
# Fail if any library module lacks a doc-gen4 HTML page in the built doc output.
#
# Guards against a stale or incomplete API-reference deploy: a module can be in
# source (and in the search index) while its per-module page is missing, so the
# manual links a declaration whose reference page 404s. This turns that silent
# drift into a loud CI failure.
#
# Usage: check-apidoc-coverage.sh <doc-output-dir>   (e.g. .lake/build/doc)
# Page path scheme: module Transfer/Combinators/ParamArray -> <dir>/Transfer/Combinators/ParamArray.html
set -euo pipefail

DOC_DIR="${1:?usage: check-apidoc-coverage.sh <doc-output-dir>}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

if [ ! -d "$DOC_DIR" ]; then
  echo "FAIL: doc output dir '$DOC_DIR' does not exist — the API build produced nothing."
  exit 1
fi

missing=0
checked=0
while IFS= read -r f; do
  rel="${f#"$ROOT"/}"          # e.g. Transfer/Combinators/ParamArray.lean
  page="${rel%.lean}.html"     # e.g. Transfer/Combinators/ParamArray.html
  checked=$((checked + 1))
  if [ ! -f "$DOC_DIR/$page" ]; then
    echo "MISSING API page: $page  (module $rel)"
    missing=$((missing + 1))
  fi
done < <(find "$ROOT/Transfer" -name '*.lean' -not -path "$ROOT/Transfer/Audit.lean")
# Transfer/Audit.lean is the CI axiom-ledger tripwire (only `#print axioms` /
# `#guard_msgs` commands, no declarations), so doc-gen4 emits no page for it and it
# is not part of the public API — exclude it from the coverage guard.
# Transfer/Examples/CoqEAL/* is the separate `TransferCoqEAL` lib (depends on
# CompPoly). The API job builds `TransferCoqEAL:docs` alongside `Transfer:docs`, so
# its pages land in the same doc output and are covered by this guard too.

if [ "$missing" -gt 0 ]; then
  echo "FAIL: $missing of $checked library modules have no API page — the deploy would be incomplete."
  exit 1
fi
echo "OK: all $checked library modules have an API page in $DOC_DIR."
