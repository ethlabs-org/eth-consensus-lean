#!/usr/bin/env bash
# Shared gate functions. Bash 3.2 is sufficient. Source from the repo root.

gate_select_neg() {
  local base=$1 force=$2 args=()
  [ "$force" = 0 ] || args+=(--force)
  GATE_NEG_SCOPE=$(python3 -B scripts/checker_scope.py "$PWD" "$base" HEAD "${args[@]}")
  NEG=$(printf '%s' "$GATE_NEG_SCOPE" |
    python3 -c 'import json,sys; print(json.load(sys.stdin)["neg"])')
  export NEG
}

gate_neg_summary() {
  python3 -B scripts/checker_scope.py "$PWD" "$base" HEAD --summary "$logs/negative-controls.json"
}

# Source checks run in order, before any build or gate log directory.
# Use explicit returns: callers may test the function with if or ||.
gate_check_base() {
  local base=$1 head resolved
  head=$(git rev-parse --verify HEAD) || return $?
  if ! resolved=$(git rev-parse --verify "$base^{commit}" 2>/dev/null); then
    echo "BASE REFUSED: HEAD ${head:0:7} does not descend from base ${base:0:7}" >&2
    return 2
  fi
  if ! git merge-base --is-ancestor "$resolved" HEAD; then
    echo "BASE REFUSED: HEAD ${head:0:7} does not descend from base ${resolved:0:7}" >&2
    return 1
  fi
}

gate_precheck_step() {
  local name=$1 rc
  shift
  echo "== precheck $name"
  "$@" || {
    rc=$?
    echo "PRECHECK FAIL $name; build not started" >&2
    return "$rc"
  }
}

gate_precheck() (
  local base=${1:-} rule
  export SOURCE_ONLY=1 PYTHONDONTWRITEBYTECODE=1
  if [ -n "$base" ]; then
    gate_precheck_step base gate_check_base "$base" || exit $?
    gate_precheck_step diff-check git diff --check "$base..HEAD" || exit $?
    gate_precheck_step guard-lists python3 scripts/guard-lists.py diff \
      --main-rev "$base" --target scripts/check-fgsa-claims.sh || exit $?
  fi
  gate_precheck_step unported python3 -B scripts/unported-selftest.py --check || exit $?
  gate_precheck_step sleep-scopes python3 -B scripts/check-sleep-scopes.py || exit $?
  gate_precheck_step legacy-inventory python3 scripts/current-inventory.py legacy \
    docs/internal/api/legacy-api.json || exit $?
  gate_precheck_step import-policy python3 scripts/generate-import-policy.py --check || exit $?
  gate_precheck_step check-layers python3 scripts/check-layers.py || exit $?
  gate_precheck_step check-module-headers python3 scripts/check-module-headers.py || exit $?
  gate_precheck_step check-expose python3 scripts/check-expose.py || exit $?
  gate_precheck_step check-transparency python3 scripts/check-transparency.py || exit $?
  # The default Python rule set includes compiled F-31. Select only source rules.
  local -a gly_rules=()
  for rule in F-1 F-3 F-4 F-5 F-6 F-12 F-13 F-14 F-15 F-18 F-20 F-21 F-23 F-25 F-26 F-28 F-30; do
    gly_rules+=(--rule "$rule")
  done
  gate_precheck_step check-gly-rules python3 scripts/check-gly-rules.py "${gly_rules[@]}" || exit $?
  gate_precheck_step check-fgsa bash scripts/check-fgsa.sh || exit $?
  gate_precheck_step check-fgsa-run bash scripts/check-fgsa-run.sh || exit $?
  gate_precheck_step check-fgsa-claims bash scripts/check-fgsa-claims.sh || exit $?
  echo "PRECHECK PASS; build not started"
)

# Read inventory names as data. Preserve Lean's ? and ! identifiers as arguments.
gate_inventory_args() {
  local data name
  data=$(python3 -B scripts/check_inventory.py "$1") || return $?
  GATE_INVENTORY=()
  while IFS= read -r name; do GATE_INVENTORY+=("$name"); done <<< "$data"
}

gate_jobs() {
  # JOBS is a per-script pool bound: default 3 on Mac, 6 on Linux; env wins.
  # It is not machine concurrency. GATE_SLOTS caps all shared heavy steps.
  if [ "$(uname -s)" = Darwin ]; then JOBS=${JOBS:-3}; else JOBS=${JOBS:-6}; fi
  case "$JOBS" in
    ''|0*|*[!0-9]*) echo "JOBS must be a positive integer" >&2; return 2 ;;
  esac
}

gate_slots_init() {
  # One directory per gate, or per standalone check. All children share it.
  # GATE_SLOTS from the environment wins: default 3 on Mac, 3 on Linux (NUC: raise only from a measured peak RSS; peak x slots <= 15 GB).
  if [ "$(uname -s)" = Darwin ]; then GATE_SLOTS=${GATE_SLOTS:-3}
  else GATE_SLOTS=${GATE_SLOTS:-3}; fi
  case "$GATE_SLOTS" in
    ''|0*|*[!0-9]*) echo "GATE_SLOTS must be a positive integer" >&2; return 2 ;;
  esac
  if [ -z "${GATE_SLOT_DIR:-}" ]; then
    mkdir -p .lake || return $?
    GATE_SLOT_DIR=$(mktemp -d "$PWD/.lake/gate-slots.XXXXXX") || return $?
  fi
  mkdir -p "$GATE_SLOT_DIR" || return $?
  export GATE_SLOTS GATE_SLOT_DIR
}

gate_slot_release() {
  if [ -n "${gate_slot:-}" ]; then
    # Removing the PID directory claims the release. Only its remover may
    # remove the slot, so two stale-slot readers cannot remove a new owner.
    if rmdir "$gate_slot/owner.$gate_owner" 2>/dev/null; then
      rmdir "$gate_slot" 2>/dev/null || :
    fi
  fi
}

gate_slot_acquire() {
  local k slot owner pid
  # $$ is the parent PID in a Bash subshell. Bash 3.2 has no BASHPID.
  gate_owner=${BASHPID:-$(exec sh -c 'echo "$PPID"')}
  gate_slot=
  trap 'gate_slot_release' EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  while :; do
    for ((k=1; k<=GATE_SLOTS; k++)); do
      slot=$GATE_SLOT_DIR/slot.$k
      if mkdir "$slot" 2>/dev/null; then
        gate_slot=$slot
        mkdir "$slot/owner.$gate_owner" || return $?
        return 0
      fi
      for owner in "$slot"/owner.*; do
        [ -d "$owner" ] || continue
        pid=${owner##*.}
        case "$pid" in ''|0*|*[!0-9]*) continue ;; esac
        if ! kill -0 "$pid" 2>/dev/null; then
          if rmdir "$owner" 2>/dev/null; then rmdir "$slot" 2>/dev/null || :; fi
        fi
      done
      # An ownerless slot can be between mkdir and PID publication. Keep it
      # occupied: a timeout must not remove a delayed live holder's slot.
    done
    sleep 0.1
  done
}

# Fail-fast parallel steps (gate policy 2026-10-02). Start `runner <name>` for each
# name as a background job in its OWN process group (set -m). Optional --width N
# keeps at most N drivers active and launches pending names in submission order.
# Poll for exits (Bash 3.2: no wait -n). The runner writes "<rc> <wall>" to
# <resultdir>/<name>.result.
# At the first nonzero rc (or a missing result), send TERM to every other running
# step's process group, wait up to GATE_FF_GRACE seconds (default 30) for them to
# exit (EXIT traps clean up control files), then KILL the groups still alive.
# The caller's own group is never signalled. Then return 1 with GATE_FF_FAILED=<name> and
# GATE_FF_KILLED=" <name>..." set. Return 0 when every step passes.
gate_parallel_failfast() {
  local runner=$1 resultdir=$2; shift 2
  local width=$#
  if [ "${1:-}" = --width ]; then width=$2; shift 2; fi
  case "$width" in
    ''|0*|*[!0-9]*) echo "fail-fast width must be a positive integer" >&2; return 2 ;;
  esac
  local names=("$@") pids=() state=() i j rc wall alive grace=${GATE_FF_GRACE:-30}
  local running=0 next=0
  GATE_FF_FAILED= GATE_FF_KILLED=
  for i in "${!names[@]}"; do state[$i]=pending; done
  alive=${#names[@]}
  while [ "$alive" -gt 0 ]; do
    for i in "${!names[@]}"; do
      [ "${state[$i]}" = run ] || continue
      kill -0 "${pids[$i]}" 2>/dev/null && continue
      wait "${pids[$i]}" 2>/dev/null || :
      state[$i]=done; alive=$((alive-1)); running=$((running-1))
      rc=99
      if [ -f "$resultdir/${names[$i]}.result" ]; then read -r rc wall < "$resultdir/${names[$i]}.result"; fi
      [ "$rc" = 0 ] && continue
      GATE_FF_FAILED=${names[$i]}
      for j in "${!names[@]}"; do
        [ "${state[$j]}" = run ] || continue
        kill -TERM -- "-${pids[$j]}" 2>/dev/null || :
        GATE_FF_KILLED="$GATE_FF_KILLED ${names[$j]}"
      done
      # Wait up to the grace for the TERM traps (control cleanups) to finish;
      # KILL only a group that is still alive after it.
      local waited=0 live
      while [ "$waited" -lt "$grace" ]; do
        live=0
        for j in "${!names[@]}"; do
          [ "${state[$j]}" = run ] || continue
          # Test the whole process group: a leader can die while a child lives on.
          if kill -0 -- "-${pids[$j]}" 2>/dev/null; then live=1; else wait "${pids[$j]}" 2>/dev/null || :; state[$j]=stopped; fi
        done
        [ "$live" = 1 ] || break
        sleep 1; waited=$((waited+1))
      done
      for j in "${!names[@]}"; do
        [ "${state[$j]}" = run ] || continue
        kill -KILL -- "-${pids[$j]}" 2>/dev/null || :
        wait "${pids[$j]}" 2>/dev/null || :
        state[$j]=killed
      done
      return 1
    done
    # Refill only after checking all completed drivers for failure.
    set -m
    while [ "$running" -lt "$width" ] && [ "$next" -lt "${#names[@]}" ]; do
      "$runner" "${names[$next]}" & pids[$next]=$!; state[$next]=run
      next=$((next+1)); running=$((running+1))
    done
    set +m
    if [ "$alive" -gt 0 ]; then sleep 1; fi
  done
  return 0
}

# The subshell owns one slot until the entire command or function exits.
# Do not use this function in an if/|| test when the command needs set -e.
gate_with_slot() (
  # Nested check drivers share the caller's slot, including with GATE_SLOTS=1.
  if [ "${GATE_SLOT_HELD:-0}" = 1 ]; then
    gate_timing_slot
    "$@"; exit $?
  fi
  gate_slots_init || exit $?
  gate_slot_acquire || exit $?
  gate_timing_slot
  export GATE_SLOT_HELD=1
  "$@"
)

gate_timing_slot() {
  [ -z "${GATE_TIMING_RECORD:-}" ] ||
    python3 -B "$GATE_TIMING_HELPER" slot "$GATE_TIMING_RECORD"
  if [ -n "${GATE_STEP_TIMING_RECORD:-}" ] &&
      [ "$GATE_STEP_TIMING_RECORD" != "${GATE_TIMING_RECORD:-}" ]; then
    python3 -B "$GATE_TIMING_HELPER" slot "$GATE_STEP_TIMING_RECORD"
  fi
}

gate_measure_command() {
  [ -n "${GATE_TIMING_RECORD:-}" ] || { "$@"; return $?; }
  local flag=-v rc=0 output=$GATE_TIMING_RECORD.time
  [ "$(uname -s)" != Darwin ] || flag=-l
  /usr/bin/time "$flag" -o "$output" "$@" || rc=$?
  python3 -B "$GATE_TIMING_HELPER" finish "$GATE_TIMING_RECORD" "$rc" "$output"
  return "$rc"
}

# Record shell functions without putting timing output into command stdout.
gate_timed() (
  local label=$1; shift
  [ -n "${GATE_LOG_DIR:-}" ] || { "$@"; exit $?; }
  local record=$GATE_LOG_DIR/timings/${GATE_STEP:-standalone}/$label.json
  local resource=$record.cpu rc
  export GATE_TIMING_HELPER=${GATE_TIMING_HELPER:-$PWD/scripts/gate_timing.py}
  export GATE_TIMING_RECORD=$record
  if [ "$label" = "${GATE_STEP:-}" ]; then export GATE_STEP_TIMING_RECORD=$record; fi
  python3 -B "$GATE_TIMING_HELPER" start "$record" "$label" "$@"
  trap 'rc=$?; trap - EXIT; python3 -B "$GATE_TIMING_HELPER" finish "$record" "$rc" "$resource"; exit "$rc"' EXIT
  trap 'exit 130' INT
  trap 'exit 143' TERM
  TIMEFORMAT='GATE_CPU %U %S'
  { time ( "$@" 2>&3 ); } 3>&2 2> "$resource"
)

# A signal exit, or a failure with empty output, is not a valid rejection.
gate_control_check() {
  if [ "$2" -ge 128 ] || { [ "$2" -ne 0 ] && [ -z "$3" ]; }; then
    echo "CONTROL KILLED (rc $2): $1"
    return 1
  fi
  return 0
}

gate_options() {
  NEG=${NEG:-1}
  while [ $# -gt 0 ]; do
    case "$1" in
      --no-negative) NEG=0 ;;
      *) echo "unknown option: $1" >&2; return 2 ;;
    esac
    shift
  done
  case "$NEG" in 0|1) ;; *) echo "NEG must be 0 or 1" >&2; return 2 ;; esac
  gate_jobs
  gate_slots_init
}

# Every build in the gate uses this lock, including standalone check scripts.
# Linux uses flock; macOS uses an atomic directory because flock is not built in.
# GATE_NO_BUILD checks freshness without starting a build. The driver sets it
# only after one build of all default, support and CheckGenFirst targets.
gate_build() (
  local data target targets=()
  data=$(python3 -B scripts/unported.py "$@") || exit $?
  while IFS= read -r target; do
    [ -z "$target" ] || targets+=("$target")
  done <<< "$data"
  [ "${#targets[@]}" -gt 0 ] || exit 0
  set -- "${targets[@]}"
  mkdir -p .lake
  if command -v flock >/dev/null 2>&1; then
    if [ "${GATE_NO_BUILD:-0}" = 1 ]; then
      flock .lake/gate-build.lock lake build --no-build "$@"
    else
      flock .lake/gate-build.lock lake build "$@"
    fi
  else
    while ! mkdir .lake/gate-build.lock.d 2>/dev/null; do sleep 1; done
    trap 'rmdir .lake/gate-build.lock.d' EXIT
    trap 'exit 130' INT
    trap 'exit 143' TERM
    if [ "${GATE_NO_BUILD:-0}" = 1 ]; then
      lake build --no-build "$@"
    else
      lake build "$@"
    fi
  fi
)

# A build control can change any Lake output, including dependency outputs.
# Copy only stable Lake inputs; never copy concurrent gate/control directories.
# No hard links or writable package symlinks: a failed control cannot affect readers.
gate_copy_control_tree() {
  local source=$1 target=$2 part
  rsync -a --exclude=/.lake --exclude=/.git --exclude=/AGENTS.md \
    --exclude=/state.md --exclude=/log.md --exclude=/claude-files "$source/" "$target/"
  mkdir -p "$target/.lake"
  for part in build config packages; do
    [ -d "$source/.lake/$part" ] || continue
    if [ "$(uname -s)" = Darwin ]; then
      if cp -c -p -R "$source/.lake/$part" "$target/.lake/" 2>/dev/null; then continue; fi
    else
      if cp -a --reflink=auto "$source/.lake/$part" "$target/.lake/"; then continue; fi
    fi
    mkdir -p "$target/.lake/$part"
    rsync -a "$source/.lake/$part/" "$target/.lake/$part/"
  done
}

# Each control has one shared slot for its whole run, scratch directory and
# log. JOBS bounds this script's jobs, including those waiting for a slot.
# Poll without wait -n. Collect and print in submission order.
# Never call a control function in an if/|| test: that disables its set -e.
gate_pool_init() {
  pool_root=$1
  pool_pids=(); pool_logs=(); pool_names=()
  gate_slots_init
  mkdir -p "$pool_root"
}

gate_pool_add() {
  local running i dir
  while :; do
    running=$(jobs -pr | wc -l | tr -d ' ')
    [ "$running" -lt "$JOBS" ] && break
    sleep 1
  done
  i=${#pool_pids[@]}
  dir=$(mktemp -d "$pool_root/$1.XXXXXX")
  pool_logs[$i]=$dir/control.log
  pool_names[$i]=$1
  (
    set -e
    neg=$dir
    gate_with_slot "$@"
  ) > "$dir/control.log" 2>&1 &
  pool_pids[$i]=$!
}

gate_pool_wait() {
  local i rc first=0
  for ((i=0; i<${#pool_pids[@]}; i++)); do
    rc=0
    wait "${pool_pids[$i]}" || rc=$?
    cat "${pool_logs[$i]}"
    # rc 0 with no output is a valid pass (a merge-tier positive-only check).
    if [ "$rc" -ge 128 ] || { [ "$rc" -ne 0 ] && [ ! -s "${pool_logs[$i]}" ]; }; then
      echo "CONTROL KILLED (rc $rc): ${pool_names[$i]}"
      if [ "$rc" -eq 0 ]; then rc=1; fi
    fi
    if [ "$rc" -ne 0 ] && [ "$first" -eq 0 ]; then first=$rc; fi
  done
  pool_pids=(); pool_logs=(); pool_names=()
  return "$first"
}

# Serial controls form a barrier. They also get a private directory and log.
gate_control_serial() {
  gate_pool_wait || return $?
  gate_pool_add "$@"
  gate_pool_wait
}

# Source paths come from the specified tree; build targets remain module names.
gate_source_file() {
  python3 -B scripts/source_layout.py --root "$1" physical "$2"
}
gate_source_path() { python3 -B scripts/source_layout.py path "$@"; }
gate_source_dir() { python3 -B scripts/source_layout.py dir "$@"; }
gate_source_files() {
  python3 -B - "$1" "$2" <<'PYTHON'
import sys
from pathlib import Path
sys.path.insert(0, 'scripts')
from source_layout import Layout
layout = Layout(Path(sys.argv[1]))
for path in layout.source_files([sys.argv[2]]):
    logical = layout.logical_path(path)
    if logical != sys.argv[2] + '.lean':
        print(logical)
PYTHON
}
