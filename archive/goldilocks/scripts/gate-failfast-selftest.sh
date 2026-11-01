#!/usr/bin/env bash
# Self-test of gate_parallel_failfast (scripts/gate-common.sh): stub steps, no Lean.
# Run from the repo root with the gate's shell (Bash 3.2 or later). Exit 0 = PASS.
set -uo pipefail
source scripts/gate-common.sh
work=$(mktemp -d "${TMPDIR:-/tmp}/gate-ff.XXXXXX"); trap 'rm -rf "$work"' EXIT
stub() (  # <name>: behaviour from the name prefix; writes "<rc> <wall>" like gate.sh step
  set +e
  case "$1" in
    ok*)   sleep 1; rc=0 ;;
    slow*) sleep 30 & echo $! > "$work/$1.child"; wait; rc=0 ;;
    fail*) sleep 2; rc=3 ;;
    nores*) sleep 2; exit 0 ;;   # exits with no result file
    tidy*) trap 'sleep 1; echo cleaned > "$work/$1.clean"; exit 143' TERM; sleep 30 & wait; rc=0 ;;
    stub*) ( trap '' TERM; exec sh -c 'echo $$ > "$0"; trap "" TERM; while :; do sleep 1; done' "$work/$1.pid" ) ;;   # a child that ignores TERM
  esac
  printf '%s %s\n' "$rc" 0 > "$work/$1.result"
)
fails=0
check() { if eval "$2"; then echo "ok: $1"; else echo "FAIL: $1"; fails=$((fails+1)); fi; }
export GATE_FF_GRACE=2

# 1. all pass
rm -f "$work"/*.result
if gate_parallel_failfast stub "$work" ok1 ok2 ok3; then r=0; else r=1; fi
check "all pass returns 0" '[ "$r" = 0 ] && [ -z "$GATE_FF_FAILED" ]'

# 2. one fails early: the slow steps (and their child sleeps) are killed, fast
rm -f "$work"/*.result "$work"/*.child
t0=$(date +%s)
if gate_parallel_failfast stub "$work" slowA fail1 slowB; then r=0; else r=1; fi
t1=$(date +%s)
check "failure returns 1" '[ "$r" = 1 ]'
check "failing step named" '[ "$GATE_FF_FAILED" = fail1 ]'
check "both slow steps stopped" 'case "$GATE_FF_KILLED" in *slowA*slowB*|*slowB*slowA*) true ;; *) false ;; esac'
check "returns well before the slow steps end" '[ $((t1-t0)) -lt 15 ]'
alive=0; for c in "$work"/slow*.child; do p=$(cat "$c"); kill -0 "$p" 2>/dev/null && alive=$((alive+1)); done
check "child processes of killed steps are gone" '[ "$alive" = 0 ]'
check "caller survives" 'kill -0 $$'

# 3. a step that exits without a result file counts as a failure
rm -f "$work"/*.result
if gate_parallel_failfast stub "$work" nores1 ok1; then r=0; else r=1; fi
check "missing result is a failure" '[ "$r" = 1 ] && [ "$GATE_FF_FAILED" = nores1 ]'

# 4. a step with a TERM cleanup trap finishes it (no KILL inside the grace);
#    a step that ignores TERM is KILLed after the grace
rm -f "$work"/*.result "$work"/*.clean
t0=$(date +%s)
if gate_parallel_failfast stub "$work" tidyA stubborn fail1; then r=0; else r=1; fi
t1=$(date +%s)
check "failure with trap steps returns 1" '[ "$r" = 1 ] && [ "$GATE_FF_FAILED" = fail1 ]'
check "TERM cleanup trap ran" '[ -f "$work/tidyA.clean" ]'
check "TERM-ignoring step killed after the grace" '[ $((t1-t0)) -ge 3 ] && [ $((t1-t0)) -lt 15 ]'
check "TERM-ignoring child gone" '! kill -0 "$(cat "$work/stubborn.pid")" 2>/dev/null'

if [ "$fails" = 0 ]; then echo "gate-failfast-selftest: PASS"; else echo "gate-failfast-selftest: FAIL ($fails)"; exit 1; fi
