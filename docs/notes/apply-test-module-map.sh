#!/usr/bin/env bash
# Apply docs/notes/test-module-map.tsv to a checkout: rewrite every reference to an old test module (its module name
# `ConsensusLeanTest.X` and its path `ConsensusLeanTest/X`, with or without `.lean`), move the files that still have
# an old name, and regenerate the test root. Idempotent: a second run changes nothing. For branches started before
# the move: rebase onto it, then run this once from the repository root:
#   bash docs/notes/apply-test-module-map.sh [map.tsv]
# Not part of the check stack (no step of scripts/check.sh runs it).
set -euo pipefail
map="${1:-docs/notes/test-module-map.tsv}"
# Whole names only: `GoldilocksFG` never touches `GoldilocksFGStore`, and an old name that is a prefix of its new
# name (`ConsensusLeanTest.Shape` -> `ConsensusLeanTest.Shape.Basic`) is not rewritten again.
rules="$(awk -F'\t' '!/^#/ && NF >= 2 {
  o = $1; n = $2; op = o; gsub(/\./, "/", op); np = n; gsub(/\./, "/", np); gsub(/\./, "\\.", o)
  printf "s{\\b%s\\b(?![.][A-Z]|/)}{%s}g;\n", o, n
  printf "s{\\b%s\\b(?!/)}{%s}g;\n", op, np
}' "$map")"
# Tracked text files, except symlinks (CLAUDE.md), the map and this script, the historical approval record,
# docs/decisions.md (owned by a separate edit) and archive/.
git ls-files -z -- '*.lean' '*.md' '*.toml' '*.yml' '*.sh' '*.py' '*.tex' ':!:docs/notes/test-module-map.tsv' ':!:docs/notes/apply-test-module-map.sh' \
  ':!:docs/notes/spec-review.md' ':!:docs/spec-review.md' ':!:docs/decisions.md' ':!:archive/**' |
  while IFS= read -r -d '' f; do [[ -L "$f" ]] || printf '%s\0' "$f"; done |
  xargs -0 perl -pi -e "$rules"
# Move the files that still have an old name (rows for modules not on this branch are skipped).
while IFS=$'\t' read -r o n _; do
  [[ "$o" == \#* || -z "$n" ]] && continue
  of="${o//.//}.lean"; nf="${n//.//}.lean"
  if [[ -f "$of" ]]; then mkdir -p "$(dirname "$nf")"; git mv "$of" "$nf"; fi
done <"$map"
lake exe mk_all --lib ConsensusLeanTest --module
# The new paths are longer: list the lines the rewrite pushed past the 100-character limit (`lake build --wfail`
# fails on them), to rewrap by hand. Comments may also name a test module without its prefix (`GoldilocksWitness`);
# `git grep -w <old leaf>` finds them.
git diff --name-only -- '*.lean' | while IFS= read -r f; do
  if [[ -f "$f" ]]; then awk -v f="$f" 'length > 100 { print "  over 100 characters: " f ":" FNR }' "$f"; fi
done
