#!/usr/bin/env bash
# Check current snapshots, then run selected controls on temporary files.
# Current snapshot controls run in isolated files.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
# Validate the shared audit bound before Lean.
workers=${AUDIT_WORKERS:-2}
for value in "$workers" "${LEAN_SLOTS:-3}" "${GATE_SLOTS:-${LEAN_SLOTS:-3}}"; do
  case "$value" in
    ''|0*|*[!0-9]*) echo "audit slot counts must be positive integers" >&2; exit 2 ;;
  esac
  if [ "$value" -lt "$workers" ]; then workers=$value; fi
done
if [ "${AUDIT_SERIAL:-0}" = 1 ]; then workers=1; fi
JOBS=$workers
manifest_run() {
  local label=$1; shift
  gate_timed "$label" gate_with_slot manifest_command "$label" "$@"
}
manifest_command() {
  local label=$1; shift
  if [ "${AUDIT_TIMING:-0}" = 1 ]; then
    local flag=-v
    if [ "$(uname -s)" = Darwin ]; then flag=-l; fi
    local output=$timing_dir/$label.time rc=0
    if [ -n "${GATE_LOG_DIR:-}" ]; then
      output=$GATE_TIMING_RECORD.time
    fi
    if [ -n "${GATE_LOG_DIR:-}" ]; then
      /usr/bin/time "$flag" -o "$output" "$@" > "$GATE_TIMING_RECORD.stdout" \
        2> "$GATE_TIMING_RECORD.stderr" || rc=$?
      python3 -B "$GATE_TIMING_HELPER" finish "$GATE_TIMING_RECORD" "$rc" "$output"
      cat "$GATE_TIMING_RECORD.stdout"
      cat "$GATE_TIMING_RECORD.stderr" >&2
    else
      /usr/bin/time "$flag" -o "$output" "$@" || rc=$?
    fi
    return "$rc"
  else
    "$@"
  fi
}
mkdir -p .lake
gate_slots_init
tmp= timing_dir=
trap 'rm -rf "$tmp" "$timing_dir"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
timing_dir=$(mktemp -d "$PWD/.lake/fgsa-manifest-times.XXXXXX")
manifest_run main lake env lean --run scripts/V2Manifest.lean --scope fgsa --check
# The current deep snapshot is required at both tiers, after complete D15.
manifest_run deep lake env lean --run scripts/V2Manifest.lean \
  --scope fgsa --deep --check
manifest_run legacy python3 -B scripts/api-snapshot.py --scope legacy --check
# Every committed review product is compared with compiled state at both tiers.
# UNPORTED PC-SA is excluded by scripts/unported-libraries.txt in api-snapshot.py.
# Its last shallow/deep snapshots stay in the tree; active scopes remain mandatory.
manifest_run v2-deep python3 -B scripts/api-snapshot.py --scope v2 \
  --output docs/internal/api/v2-deep.json --check
manifest_run gen-deep python3 -B scripts/api-snapshot.py --scope gen \
  --output docs/internal/api/gen-deep.json --check
manifest_run compose-api python3 -B scripts/api-snapshot.py --scope compose --check
manifest_run claims-api python3 -B scripts/api-snapshot.py \
  --scope fgsa-claims --check
# NEG=0 skips controls when no checker path changed.
if [ "${NEG:-1}" != 1 ]; then echo "controls skipped (NEG=0)"; exit 0; fi
mkdir -p .lake
tmp=$(mktemp -d "$PWD/.lake/fgsa-manifest.XXXXXX")

manifest_run snapshot-controls python3 -B scripts/api-snapshot-controls.py
manifest_run deep-controls python3 -B scripts/fgsa-deep-controls.py
