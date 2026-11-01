#!/usr/bin/env bash
# The mechanical build checks of BUILD §7.3, (a)–(j), in order:
#   (a) check-module-headers.py   (b) check-expose.py
#   (c) rebuild-cone-test.sh <CONE_MODULE> (default
#       AvailableChainGridCO.Proofs.Map; a throwaway copy and one Lean build)
#   (d) CheckProofEqns.lean       (e) check-layers.py
#   (f) shake-report.sh (REPORT only; never fails the run unless it cannot run)
#   (g) chain-depth.py (REPORT only) (h) check-transparency.py
#   (i) check-gly-rules.sh       (includes compiled CheckGenFirst.lean)
#   (j) source, shell, pool, policy and compiled proof-equation self-tests.
#       Each B2a addition reports its elapsed time.
# B1 import review: retain public exports and explicit tactic/test environments.
# The count 224 is historical; use the current report for the live inventory.
# (d) and (e) run when their script exists; else "SKIPPED: not yet present".
# SKIP_CONE=1 skips (c) (it needs a built tree and a Lean build).
# Every check runs; the summary lists each result. Exit 0: every check that
# ran passed; 1: a check failed.
# Heavy steps share GATE_SLOTS (default Mac 3, Linux 4; env wins).
# JOBS bounds each control pool; it does not set machine concurrency.
set -uo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
gate_slots_init || exit $?
CONE_MODULE=${CONE_MODULE:-AvailableChainGridCO.Proofs.Map}
RESULTS=(); FAILED=0
run() {  # run <id> <name> <command...>
  local id=$1 name=$2; shift 2
  echo "=== ($id) $name"
  "$@"; local rc=$?
  if [ $rc -eq 0 ]; then RESULTS+=("($id) $name: PASS"); else RESULTS+=("($id) $name: FAIL (rc $rc)"); FAILED=1; fi
}
skip() { echo "=== ($1) $2"; echo "SKIPPED: $3"; RESULTS+=("($1) $2: SKIPPED: $3"); }

checks_only=0; selftests_only=0
case "${1:-}" in
  --selftests-only) selftests_only=1 ;;
  --checks-only) checks_only=1 ;;
  '') ;;
  *) echo "unknown option: $1" >&2; exit 2 ;;
esac
if [ "$selftests_only" = 0 ]; then
run a check-module-headers python3 scripts/check-module-headers.py
run b check-expose python3 scripts/check-expose.py
if [ "${SKIP_CONE:-0}" = 1 ]; then skip c rebuild-cone-test "SKIP_CONE=1"
else run c "rebuild-cone-test $CONE_MODULE" gate_with_slot bash scripts/rebuild-cone-test.sh "$CONE_MODULE"; fi
if [ -f scripts/CheckProofEqns.lean ]; then
  run d CheckProofEqns gate_with_slot bash -c 'source scripts/gate-common.sh; gate_build AvailableChainCheckSupport && lake env lean --run scripts/CheckProofEqns.lean --baseline scripts/baselines/check-proof-eqns.txt'
else skip d CheckProofEqns "not yet present"; fi
if [ -f scripts/check-layers.py ]; then run e check-layers python3 scripts/check-layers.py
else skip e check-layers "not yet present"; fi
echo "=== (f) shake-report"
if gate_with_slot bash scripts/shake-report.sh; then RESULTS+=("(f) shake-report: REPORT"); else RESULTS+=("(f) shake-report: FAIL (could not run)"); FAILED=1; fi
echo "=== (g) chain-depth"
if python3 scripts/chain-depth.py; then RESULTS+=("(g) chain-depth: REPORT"); else RESULTS+=("(g) chain-depth: FAIL (could not run)"); FAILED=1; fi
run h check-transparency python3 scripts/check-transparency.py
run i check-gly-rules gate_with_slot bash -c 'source scripts/gate-common.sh; targets=$(lake env lean --run scripts/CheckGenFirst.lean --libraries) && gate_build $targets && bash scripts/check-gly-rules.sh'
fi
timed_selftest() {
  local start=$SECONDS rc
  "$@"; rc=$?
  echo "self-test time: $* wall=$((SECONDS-start))s rc=$rc"
  return "$rc"
}
checker_selftests() {
  python3 -B scripts/unported-selftest.py &&
  python3 -B scripts/gate-neg-selftest.py &&
  python3 -B scripts/gate-integration-selftest.py &&
  bash scripts/check-layers-selftest.sh &&
  bash scripts/shake-report-selftest.sh &&
  bash scripts/precheck-selftest.sh &&
  python3 scripts/policy-controls.py &&
  python3 scripts/audit-pool-selftest.py &&
  timed_selftest python3 scripts/gate-shell-controls.py &&
  timed_selftest gate_with_slot python3 scripts/check-proof-eqns-controls.py &&
  p13_selftests &&
  sleep_selftests
}
# Sleep checker controls use isolated fixtures; run under the FULL tier too.
sleep_selftests() {
  [ "${NEG:-1}" = 0 ] && { echo "Sleep selftests: SKIPPED (NEG=0)"; return 0; }
  timed_selftest gate_with_slot python3 -B scripts/dev-check-controls.py
}
# P13 isolated selftests: checker changes or override (NEG=1). The package history check
# (--packages) reads old revisions; it is not a gate check.
p13_selftests() {
  [ "${NEG:-1}" = 0 ] && { echo "P13 selftests: SKIPPED (NEG=0)"; return 0; }
  timed_selftest python3 -B scripts/check-fg-finality-coverage.py --selftest &&
  timed_selftest gate_with_slot python3 -B scripts/check-fgsa-blueprint.py --selftest
}
if [ "$checks_only" = 0 ] && [ "${NEG:-1}" = 1 ]; then
  run j checker-self-tests checker_selftests
else skip j checker-self-tests "controls not selected"; fi
echo "=== summary"
printf '%s\n' "${RESULTS[@]}"
[ $FAILED -eq 0 ] && echo "check-build: PASS" || echo "check-build: FAIL"
exit $FAILED
