#!/usr/bin/env bash
# Fails if a .lean file of the two FG libraries uses native evaluation outside
# a comment: the token native_decide, `+native` (decide +native), a `native :=
# true` option, or the names ofReduceBool / ofReduceNat. Block comments /- … -/
# and line comments -- are removed first (Lean block comments nest; the FG
# files do not nest them). A `/-` or `--` inside a string literal is also
# removed, so this check can miss a token after one; CheckFGAxioms.lean and the
# linter linter.style.nativeDecide (under lake build --wfail) are the other
# gates. Exit codes: 0 clean; 1 a token found; 2 a library directory or root
# file is missing, or no files.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
for lib in AvailableChainSimplexFG AvailableChainKitFG AvailableChainFGCompose; do
  d=$(gate_source_dir "$lib")
  f=$(gate_source_path "$lib")
  [ -d "$d" ] || { echo "MISSING DIRECTORY: $d"; exit 2; }
  [ -f "$f" ] || { echo "MISSING ROOT FILE: $f"; exit 2; }
done
files=$(python3 -B scripts/source_layout.py --lines files \
  AvailableChainSimplexFG AvailableChainKitFG AvailableChainFGCompose)
[ -n "$files" ] || { echo "NO FILES"; exit 2; }
pat='(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native *:= *true|ofReduceBool|ofReduceNat'
status=0
for f in $files; do
  if perl -0777 -pe 's{/-.*?-/}{}gs; s{--[^\n]*}{}g' "$f" | grep -nE "$pat" >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
exit $status
