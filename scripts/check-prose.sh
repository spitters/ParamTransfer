#!/usr/bin/env bash
# Pre-commit prose guard for docstrings and docs.
#
# Two checks on newly-ADDED lines of `.lean` / `.md` files (pre-existing text
# never blocks an unrelated commit):
#
#   1. changelog / self-talk / roadmap-marker phrasing  (high-precision patterns)
#   2. citation authors not present in ATTRIBUTION.md    (the verified bibliography)
#
# A shell hook cannot judge subtle tone or verify a citation is real. For tone,
# run  /writing-clearly-and-concisely  and  /cleanup . For citations, the rule is
# that ATTRIBUTION.md is the single human-verified reference list: any author named
# in a docstring must appear there, so a fabricated name (e.g. an LLM-invented
# author) is blocked until someone adds — and thereby checks — the real reference.
set -u

root="$(git rev-parse --show-toplevel 2>/dev/null)" || exit 0

added="$(git diff --cached --unified=0 --no-color -- '*.lean' '*.md' 2>/dev/null \
  | grep -E '^\+' | grep -vE '^\+\+\+' | sed 's/^+//' || true)"
[ -z "$added" ] && exit 0

fail=0

# --- 1. changelog / self-talk / roadmap markers ----------------------------
roadmap='Lean-Trocq[^|]*(item|Stage|Phase|track)[ ]?[0-9A-E]|[ ,(]Stage [A-E]([0-9][a-z]?)?\b|\bPhase [0-9][a-z-]*\b|\bitem [0-9] of\b'
changelog='\bwhat is shipped\b|\bnot shipped\b|specified[, ]+not shipped|\bnext increment\b|\bscaffolding\b|what runs vs|\bfirst cut\b|both stacks now\b'
selftalk="the user'?s (question|premise)|\\bworkhorse\\b|confluence of ideas|facets of one idea"
phrasing="$roadmap|$changelog|$selftalk"

hits="$(printf '%s\n' "$added" | grep -nE "$phrasing" || true)"
if [ -n "$hits" ]; then
  echo "✖ prose guard: staged changes add changelog / self-talk / roadmap phrasing:" >&2
  printf '%s\n' "$hits" | sed 's/^/    /' >&2
  echo "  → state what the code IS and DOES (not what changed, is planned, or which" >&2
  echo "    development stage it is). Drop Stage/Phase/item markers and hype." >&2
  fail=1
fi

# --- 2. citation authors must be in the verified bibliography --------------
attr="$root/ATTRIBUTION.md"
if [ -f "$attr" ]; then
  # Author names appear in conjunction / et-al citation patterns: "X & Y",
  # "X and Y", "X et al". High-precision: these are almost always author lists.
  frags="$(printf '%s\n' "$added" \
    | grep -oE "[A-Z][A-Za-zà-ÿ’'.-]+ (&|and) [A-Z][A-Za-zà-ÿ’'.-]+|[A-Z][A-Za-zà-ÿ’'.-]+ et al\.?" \
    || true)"
  # Capitalised non-author tokens that occur in such lines in this codebase.
  stop='^(AdapTT|Trocq|CoqEAL|Lean|Mathlib|Coq|Rocq|Param|Map|Type|Prop|Bool|Nat|List|Tree|The|This|These|Each|Both|With|Without|From|And|Stage|Phase|Item|Elpi|HoTT|UIP|ESOP|TOPLAS|POPL|CPP|JFR|Proof|Transfer|Free|Univalence|Equivalence|Beyond|Functoriality|Dependent|Casts|Real|Numbers|Classical|Computing|Refinements|Two|Level|Theory|Baby|Bear|Section|Lemma|Theorem)$'
  names="$(printf '%s\n' "$frags" | grep -oE "[A-Z][A-Za-zà-ÿ’'.-]{2,}(-[A-Z][A-Za-zà-ÿ]+)?" \
    | grep -vE "$stop" | sort -u || true)"
  bad=""
  while IFS= read -r n; do
    [ -z "$n" ] && continue
    grep -qF "$n" "$attr" && continue
    bad="$bad $n"
  done <<< "$names"
  if [ -n "$bad" ]; then
    echo "✖ prose guard: cited author(s) not found in ATTRIBUTION.md:" >&2
    for n in $bad; do echo "    $n" >&2; done
    echo "  → every cited author must be in the verified bibliography. If the reference" >&2
    echo "    is real, add it to ATTRIBUTION.md; if it is wrong/invented, fix it." >&2
    fail=1
  fi
fi

if [ "$fail" -ne 0 ]; then
  echo "" >&2
  echo "Run /writing-clearly-and-concisely and /cleanup, then re-stage." >&2
  echo "(Override a false positive with: git commit --no-verify)" >&2
  exit 1
fi
exit 0
