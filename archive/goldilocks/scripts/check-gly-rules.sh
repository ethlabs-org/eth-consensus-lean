#!/usr/bin/env bash
# Check (i), BUILD §7.3: the GLY §F rules whose enforcement is a grep or a
# mechanical scan. The rules, their scopes and their baselines
# (scripts/baselines/check-gly-rules-<rule>.txt) are in
# scripts/check-gly-rules.py; this driver runs every rule.
# Public legacy API drift is checked by the current compiled snapshot.
# Usage: bash scripts/check-gly-rules.sh [--rule F-n]... [--list-legacy] [--write-baseline]
# Exit 0: no failing finding; 1: a failing finding; 2: an input error.
set -euo pipefail
cd "$(dirname "$0")/.."
# Keep the source/name rules and their compiled CheckGenFirst run first.
gly_source_rules() (
exec python3 scripts/check-gly-rules.py "$@"
)
source scripts/gate-common.sh

gly_faultx_route() {
  local targets
  targets=$(lake env lean --run scripts/CheckFaultXRoute.lean --libraries) || return $?
  [ -n "$targets" ] || { echo "CheckFaultXRoute returned no build targets" >&2; return 2; }
  gate_build $targets || return $?
  lake env lean --run scripts/CheckFaultXRoute.lean || return $?
  if [ "${NEG:-1}" = 1 ]; then python3 scripts/check-faultx-route-controls.py; fi
}

gly_checks() {
  # F-24 is the compiled proof-route check only (the name rule retired after the
  # route check passed its first gate, 993bfd0). `--rule F-24` selects it; the
  # source rules then run only if another --rule is also selected.
  local rc=0 route_rc=0 selected=0 route=0 other=0 skip=0 arg
  local -a py=()
  for arg in "$@"; do
    if [ "$skip" = 1 ]; then
      skip=0
      if [ "$arg" = F-24 ]; then route=1; py=("${py[@]:0:${#py[@]}-1}"); else other=1; py+=("$arg"); fi
      continue
    fi
    case "$arg" in
      --help|-h) gly_source_rules "$@"; return $? ;;
      --rule) selected=1; skip=1; py+=("$arg") ;;
      --rule=F-24) selected=1; route=1 ;;
      --rule=*) selected=1; other=1; py+=("$arg") ;;
      *) py+=("$arg") ;;
    esac
  done
  if [ "$selected" = 0 ] || [ "$other" = 1 ]; then
    gly_source_rules "${py[@]+"${py[@]}"}" || rc=$?
  fi
  if [ "$selected" = 0 ] || [ "$route" = 1 ]; then
    gly_faultx_route || route_rc=$?
  fi
  if [ "$rc" -ne 0 ]; then return "$rc"; fi
  return "$route_rc"
}

# check-build already holds a shared slot. gate_with_slot reuses that slot.
gate_with_slot gly_checks "$@"
