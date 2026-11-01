#!/usr/bin/env bash
# Self-test of the shake-report keep filter: runs scripts/shake-report.sh on
# saved `lake shake` output (SHAKE_RAW) for a fixture file; no Lean, no lake.
# A removal of an import line with `-- shake: keep` is KEPT (exit 0); a removal
# of a line without it is NEW under --fail-on-new (exit 1). Run from anywhere.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake
T=$(mktemp -d "$PWD/.lake/shake-selftest.XXXXXX")
trap 'rm -rf "$T"' EXIT
cat > "$T/Fix.lean" <<'LEAN'
module
public import Fix.Kept -- shake: keep (fixture: a use shake cannot see)
public import Fix.Unkept
-- public import Fix.Commented -- shake: keep (a comment line keeps nothing)
public import Fix.Commented
LEAN
fail=0
check() {  # <name> <expected rc> <expected output pattern> <removed import>
  printf '%s:\n  remove #[%s]\n' "$T/Fix.lean" "$4" > "$T/raw"
  set +e
  out=$(SHAKE_RAW="$T/raw" SHAKE_REPORT="$T/report" bash scripts/shake-report.sh --fail-on-new Fix 2>&1)
  rc=$?
  set -e
  if [ "$rc" = "$2" ] && grep -qE "$3" <<<"$out"; then echo "PASS $1 (exit $rc)"
  else echo "FAIL $1: exit $rc, expected $2 and /$3/"; echo "$out"; fail=1; fi
}
check kept 0 '0 NEW, 0 B1 downgrades, 1 kept' 'public import Fix.Kept'
check unkept 1 '^NEW remove .*Fix.lean public import Fix.Unkept$' 'public import Fix.Unkept'
check comment-only 1 '^NEW remove .*Fix.lean public import Fix.Commented$' 'public import Fix.Commented'
# A private nested layout must keep logical baseline keys and read physical annotations.
mkdir -p "$T/nested/scripts/baselines" "$T/nested/src/Fix"
cp scripts/shake-report.sh scripts/shake_scope.py scripts/check_common.py \
  scripts/source_layout.py "$T/nested/scripts/"
printf '[[lean_lib]]\nname="Fix"\nsrcDir="src"\n' > "$T/nested/lakefile.toml"
cp "$T/Fix.lean" "$T/nested/src/Fix/Control.lean"
printf 'remove Fix/Control.lean public import Fix.Unkept\n' \
  > "$T/nested/scripts/baselines/shake-report.txt"
printf '%s:\n  remove #[public import Fix.Kept, public import Fix.Unkept]\n' \
  "$T/nested/src/Fix/Control.lean" > "$T/raw"
set +e
out=$(SHAKE_RAW="$T/raw" SHAKE_REPORT="$T/report" \
  bash "$T/nested/scripts/shake-report.sh" --fail-on-new Fix 2>&1)
rc=$?
set -e
if [ "$rc" = 0 ] && grep -q '0 NEW, 0 B1 downgrades, 1 kept' <<<"$out" &&
    grep -qx 'remove Fix/Control.lean public import Fix.Unkept' "$T/report"; then
  echo 'PASS nested shake keys and physical keep lookup (exit 0)'
else echo "$out"; echo 'FAIL nested shake mapping'; fail=1; fi
[ "$fail" = 0 ] && echo "PASS shake-report self-test: 3 controls" || { echo "FAIL shake-report self-test"; exit 1; }
