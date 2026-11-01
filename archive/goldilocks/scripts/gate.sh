#!/usr/bin/env bash
# Run from the repository root.
# Order: source precheck -> build -> cheap checks/audits -> one fail-fast heavy group.
# Both tiers share GATE_SLOTS; checker changes or --neg select controls.
# C23 uses private source/build/config/packages copies (CoW when supported, else copy).
# Proof-equation controls use private source copies; other controls use private fixtures.
# Claims/manifest children take separate slots.
# NUC 2026-10-08..09: FULL 7025-8097 s (2 slots/12G), 10316 s (1 slot/7G);
# MERGE 1573-1993 s (2 slots). At 318074ba/1 slot: build 22, check-build 1938,
# FGSA 2154, run 1834, manifest 1497, claims 3321, compose 2830, coverage 116 s;
# Historical timing: axioms ~2 s each, coverage 0 s, blueprint 84 s.
# Old-read failures took ~300-500 s. Check them before heavy checks; keep controls later.
# Defaults: Mac 3, Linux 3 (scripts/gate-common.sh); env wins. JOBS is only a per-script pool bound.
# Linux requires a user scope with GATE_MEM (default 16G) and no swap; without it the gate refuses to run.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
gate_args=("$@")
tier=auto; base=; critical_path=0; attest_key=; attest_head=; force_neg=${NEG:-0}
integration=0; integration_args=(); integration_scope=
usage() {
  echo 'usage: bash scripts/gate.sh [--tier merge|full|auto] [--base REF] [--jobs N] [--neg]'
  echo '       bash scripts/gate.sh --critical-path'
  echo '       bash scripts/gate.sh --integration --base REF [--reviewed-allow FILE] [--reviewed-extraction SOURCE:TARGET]'
}
while [ $# -gt 0 ]; do
  case "$1" in
    --integration) integration=1; shift ;;
    --reviewed-allow|--reviewed-extraction)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      integration_args+=("$1" "$2"); shift 2 ;;
    --attest-key)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      attest_key=$2; shift 2 ;;
    --tier|--base|--jobs)
      [ $# -ge 2 ] || { usage >&2; exit 2; }
      case "$1" in --tier) tier=$2 ;; --base) base=$2 ;; --jobs) JOBS=$2 ;; esac
      shift 2 ;;
    --neg) force_neg=1; shift ;;
    --critical-path) critical_path=1; shift ;;
    --help|-h) usage; exit 0 ;;
    *) usage >&2; exit 2 ;;
  esac
done
case "$tier" in auto|merge|full) ;; *) usage >&2; exit 2 ;; esac
if [ "$integration" = 1 ]; then
  [ -n "$base" ] && [ -z "$attest_key" ] && [ "$critical_path" = 0 ] &&
    [ "$force_neg" = 0 ] && [ "$tier" != merge ] || {
    echo 'INTEGRATION REFUSED: requires explicit --base; incompatible with signing, --neg, merge, or critical-path' >&2
    exit 2
  }
  integration_scope=$(python3 -B scripts/integration_scope.py "$PWD" "$base" "${integration_args[@]}") || exit $?
  tier=full
elif [ "${#integration_args[@]}" -ne 0 ]; then
  echo 'INTEGRATION REFUSED: reviewed options require --integration' >&2; exit 2
fi
if [ "${SOURCE_ONLY:-0}" != 0 ]; then
  echo 'GATE REFUSED: SOURCE_ONLY must be unset or 0' >&2
  exit 2
fi
# Signing is opt-in. The operator must keep the private key outside target code.
# Main trusts only keys in its committed full-pass-signers policy file.
if [ -n "$attest_key" ]; then
  [ "$tier" = full ] && [ -n "$base" ] && [ "$critical_path" = 0 ] || {
    echo 'FULL RECEIPT requires --tier full --base <policy-head>' >&2; exit 2;
  }
  [ -z "$(git status --porcelain --untracked-files=all)" ] || {
    echo 'FULL RECEIPT DIRTY TARGET' >&2; exit 2;
  }
  attest_head=$(git rev-parse HEAD)
fi
# Both tiers need BASE..HEAD for control selection.
if [ -z "$base" ] && [ "$critical_path" = 0 ]; then
  base=$(git merge-base main HEAD) || {
    echo "PRECHECK FAIL base; build not started" >&2
    exit 2
  }
fi
# Refuse a bad base before the Linux memory-scope probe as well.
if [ -n "$base" ]; then
  gate_precheck_step base gate_check_base "$base" || exit $?
fi
case "$force_neg" in 0|1) ;; *) echo 'NEG must be 0 or 1' >&2; exit 2 ;; esac
gate_jobs
export JOBS

# Probe the user manager and memory properties before replacing this driver.
# Keep every argument and never retry a failed gate outside its memory scope.
memory_limit="Mac Lean wrapper"
if [ "$(uname -s)" = Linux ]; then
  memory_limit=${GATE_MEM:-16G}
  if [ "${GATE_MEM_SCOPED:-0}" != 1 ]; then
    if command -v systemd-run >/dev/null 2>&1 &&
        systemd-run --user --scope -q -p "MemoryMax=$memory_limit" -p MemorySwapMax=0 true; then
      export GATE_MEM_SCOPED=1
      exec systemd-run --user --scope -q -p "MemoryMax=$memory_limit" -p MemorySwapMax=0 \
        bash scripts/gate.sh "${gate_args[@]}"
    fi
    # Lead ruling (DC 2026-09-30, after the NUC OOM): no gate without the scope.
    echo "REFUSED: cannot create a systemd-run --user scope with MemoryMax=$memory_limit; the gate does not run unlimited" >&2
    exit 2
  else
    memory_limit="$memory_limit, swap=0"
  fi
fi
if [ "$critical_path" = 0 ]; then
  gate_select_neg "$base" "$force_neg"
  if [ "$integration" = 1 ]; then
    NEG=$(printf '%s' "$integration_scope" | python3 -c 'import json,sys; print(json.load(sys.stdin)["neg"])')
    export NEG
    GATE_NEG_SCOPE=$(printf '%s' "$GATE_NEG_SCOPE" | python3 -c \
      'import json,sys; d=json.load(sys.stdin); d.update(neg=int(sys.argv[1]),reason="provisional integration"); print(json.dumps(d))' "$NEG")
  fi
fi
# FIRST gate step: no build, slot directory, logs or full-pass stamp yet.
gate_precheck "$base" || exit $?
# BUILD §7.7: critical-path measurement is separate from the tiers.
# It runs in the same memory scope; the caller holds the NUC lock.
if [ "$critical_path" = 1 ]; then
  [ "$(uname -s)" = Linux ] || { echo "gate.sh --critical-path: NUC (Linux) only" >&2; exit 2; }
  echo "critical-path: memory=$memory_limit"
  exec bash scripts/critical-path.sh
fi
mkdir -p .lake
GATE_SLOT_DIR=$(mktemp -d "$PWD/.lake/gate-slots.XXXXXX")
gate_slots_init
export AUDIT_WORKERS=${AUDIT_WORKERS:-$((GATE_SLOTS < 2 ? GATE_SLOTS : 2))}
logs=$(mktemp -d "$PWD/.lake/gate-logs.XXXXXX")
export GATE_LOG_DIR=$logs GATE_TIMING_HELPER=$PWD/scripts/gate_timing.py AUDIT_TIMING=1
printf '%s\n' "$GATE_NEG_SCOPE" > "$logs/negative-controls.json"
if [ "$integration" = 1 ]; then
  printf '%s\n' "$integration_scope" > "$logs/integration.json"
  echo "PROVISIONAL INTEGRATION: $integration_scope"
fi
started=$(date +%s)
failed=0

# Include both sides of renames. Also inspect local edits, since a gate may
# run before a commit. Use NUL delimiters for names and disable external diffs.
tier_path() {
  case "$1" in
    scripts/*|*allow*.txt|lakefile.toml|lean-toolchain|lake-manifest.json|\
    Statements/*|*/Statements/*|docs/FGSA-API.md|docs/PCSA-API.md|docs/api/*|\
    docs/internal/FGSA-API.md|docs/internal/PCSA-API.md|docs/internal/api/*)
      reason="gate input changed: $1"; return 0 ;;
  esac
  return 1
}
choose_tier() {
  if [ "$tier" != auto ]; then reason="explicit --tier $tier"; return; fi
  base=$(git rev-parse --verify "$base^{commit}")
  git diff --no-ext-diff --no-renames --name-only -z "$base..HEAD" > "$logs/paths"
  git diff --no-ext-diff --no-renames --name-only -z HEAD >> "$logs/paths"
  git ls-files --others --exclude-standard -z >> "$logs/paths"
  tier=full
  local path
  while IFS= read -r -d '' path; do
    if tier_path "$path"; then return; fi
  done < "$logs/paths"
  git diff --no-ext-diff --no-textconv --no-renames --unified=0 "$base..HEAD" -- '*.lean' > "$logs/imports.diff"
  git diff --no-ext-diff --no-textconv --no-renames --unified=0 HEAD -- '*.lean' >> "$logs/imports.diff"
  if grep -vE '^(\+\+\+|---)' "$logs/imports.diff" |
      grep -E '^[+-](.*[^[:alnum:]_])?import([^[:alnum:]_]|$)' >/dev/null; then
    reason="an import line changed"; return
  fi
  git ls-files --others --exclude-standard -z -- '*.lean' > "$logs/untracked-lean"
  while IFS= read -r -d '' path; do
    if grep -E '(^|[^[:alnum:]_])import([^[:alnum:]_]|$)' "$path" >/dev/null; then
      reason="an import line was added: $path"; return
    fi
  done < "$logs/untracked-lean"
  if [ ! -f .lake/gate-last-full ]; then reason=".lake/gate-last-full is missing"; return; fi
  local modified now
  if [ "$(uname -s)" = Darwin ]; then modified=$(stat -f %m .lake/gate-last-full)
  else modified=$(stat -c %Y .lake/gate-last-full); fi
  now=$(date +%s)
  if [ "$((now-modified))" -ge 86400 ] || [ "$modified" -gt "$now" ]; then
    reason=".lake/gate-last-full is older than 24 h or has a future date"; return
  fi
  tier=merge; reason="no full-tier changes; full PASS is less than 24 h old"
}
choose_tier
if [ "$integration" = 1 ]; then
  echo "mode: PROVISIONAL INTEGRATION; slots=$GATE_SLOTS memory=$memory_limit"
else
  echo "tier: $(printf '%s' "$tier" | tr '[:lower:]' '[:upper:]') ($reason); slots=$GATE_SLOTS memory=$memory_limit"
fi
echo "logs: $logs"
gate_neg_summary
echo "reminder: run bash scripts/check-fg.sh on the Mac (research files required)"

# Do not put the step in an if/|| test: preserve errexit inside its functions.
step() (
  set +e
  name=$1; shift
  export GATE_STEP=$name
  start=$(date +%s)
  (set -e; gate_timed "$name" "$@") > "$logs/$name.log" 2>&1
  rc=$?
  end=$(date +%s)
  printf '%s %s\n' "$rc" "$((end-start))" > "$logs/$name.result"
)
# Fail-fast: stop after the first failing sequential step.
stop_if_failed() {
  if [ "$failed" -ne 0 ]; then echo "fail-fast: later steps skipped"; finish; exit 1; fi
}
summary() {
  local name=$1 rc wall
  read -r rc wall < "$logs/$name.result"
  echo "$name rc=$rc wall=${wall}s"
  if [ "$rc" -ne 0 ]; then
    failed=1
    cat "$logs/$name.log"
  fi
}
finish() {
  local cg peak
  gate_neg_summary
  # Peak memory of this gate's own cgroup (the MemoryMax scope on Linux).
  if [ -r /proc/self/cgroup ]; then
    cg=$(sed -n 's/^0:://p' /proc/self/cgroup)
    peak=$(cat "/sys/fs/cgroup$cg/memory.peak" 2>/dev/null) &&
      echo "memory.peak=$((peak / 1048576)) MiB (cgroup $cg)"
  fi
  if [ "$failed" -eq 0 ]; then
    if [ "$integration" = 1 ]; then
      if ! python3 -B scripts/integration_scope.py "$PWD" "$base" "${integration_args[@]}" --complete "$logs" > "$logs/integration-complete.log" 2>&1; then
        cat "$logs/integration-complete.log"; failed=1
        echo 'PROVISIONAL INTEGRATION FAIL'; return
      fi
      echo "PROVISIONAL INTEGRATION PASS (main acceptance requires FULL --neg and Mac check-fg); logs=$logs"
      return
    fi
    if [ -n "$attest_key" ]; then
      python3 scripts/full-pass.py sign "$PWD" "$attest_head" "$base" "$logs" \
        "$attest_key" "$logs/full-pass.json" || return $?
    fi
    if [ "$tier" = full ]; then touch .lake/gate-last-full; fi
    echo "GATE PASS tier=$tier slots=$GATE_SLOTS memory=$memory_limit wall=$(($(date +%s)-started))s"
  else
    if [ "$integration" = 1 ]; then echo 'PROVISIONAL INTEGRATION FAIL'
    else echo "GATE FAIL tier=$tier slots=$GATE_SLOTS memory=$memory_limit wall=$(($(date +%s)-started))s"; fi
  fi
}
build_all() {
  local targets
  targets=$(gate_with_slot lake env lean --run scripts/CheckGenFirst.lean --libraries)
  [ -n "$targets" ] || { echo "CheckGenFirst returned no build targets"; return 1; }
  # Build the full route-check scope before GATE_NO_BUILD is enabled.
  local route_targets
  route_targets=$(gate_with_slot lake env lean --run scripts/CheckFaultXRoute.lean --libraries) || return $?
  [ -n "$route_targets" ] || { echo "CheckFaultXRoute returned no build targets"; return 1; }
  targets="$targets $route_targets"
  # @ selects every default target of the root package, plus check support
  # and every module that CheckGenFirst scans (including facade orphans).
  GATE_NO_BUILD=0 gate_build --wfail @ AvailableChainCheckSupport $targets
}
step build build_all
summary build
if [ "$failed" -ne 0 ]; then finish; exit 1; fi
export GATE_NO_BUILD=1
if [ "$integration" = 1 ]; then
  step package-g0 python3 -B scripts/integration_g0.py
  summary package-g0
  stop_if_failed
fi
# Control selection applies to both tiers; build checks remain mandatory.
export SKIP_CONE=0
# Every check step by name. Heavy steps share the gate slots (GATE_SLOTS cap).
run_check() {
  case "$1" in
    check-build) step "$1" gate_measure_command bash scripts/check-build.sh --checks-only ;;
    check-fgsa|check-fgsa-run) step "$1" gate_measure_command bash "scripts/$1.sh" ;;
    check-fg-compose) step "$1" gate_with_slot gate_measure_command bash scripts/check-fg-compose.sh ;;
    catalog-lock) step "$1" gate_with_slot lake env lean --run scripts/CatalogLock.lean --check ;;
    v2-manifest) step "$1" gate_with_slot lake env lean --run scripts/V2Manifest.lean --check ;;
    gen-manifest) step "$1" gate_with_slot lake env lean --run scripts/V2Manifest.lean --scope gen --check ;;
    # Includes mandatory frame/deep checks at both tiers; NEG only selects controls.
    fgsa-manifest) step "$1" gate_measure_command bash scripts/check-fgsa-manifest.sh ;;
    fgsa-claims) step "$1" gate_measure_command bash scripts/check-fgsa-claims.sh ;;
    *) echo "unknown gate step: $1" >&2; return 2 ;;
  esac
}
# Fail-fast group: the first failing step stops the others (their own process groups).
run_group() {
  local queued
  for queued in "$@"; do
    python3 -B "$GATE_TIMING_HELPER" queue "$logs/timings/$queued/$queued.json" "$queued"
  done
  if ! gate_parallel_failfast run_check "$logs" --width "$GATE_SLOTS" "$@"; then
    for queued in "$@"; do
      python3 -B "$GATE_TIMING_HELPER" cancel "$logs/timings/$queued/$queued.json"
    done
    summary "$GATE_FF_FAILED"
    echo "fail-fast: $GATE_FF_FAILED failed; stopped:${GATE_FF_KILLED:- none}; later steps skipped"
    finish; exit 1
  fi
  local name
  for name in "$@"; do summary "$name"; done
}
audit() {
  local path=$1 out=$2 rc=0 count
  gate_with_slot lake env lean "$path" > "$out" 2>&1 || rc=$?
  cat "$out"
  count=$(grep -c sorryAx "$out" || :)
  echo "sorryAx = $count"
  [ "$rc" -eq 0 ] && [ "$count" = 0 ]
}
# A strict audit: every `#print axioms` command has a result, and each result
# uses only propext, Classical.choice and Quot.sound.
audit_strict() {
  local path=$1 out=$2 want got bad
  audit "$path" "$out" || return 1
  want=$(grep -c '^#print axioms' "$path" 2>/dev/null); want=${want:-0}
  got=$(grep -c "depends on axioms: \[\|does not depend on any axioms" "$out" || :)
  bad=$(tr '\n' ' ' < "$out" | grep -o 'depends on axioms: \[[^]]*\]' | sed 's/.*\[//; s/\]$//' |
    tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -vxE 'propext|Classical\.choice|Quot\.sound' || :)
  if [ -n "$bad" ]; then echo "BAD AXIOMS: $(echo $bad)"; return 1; fi
  if [ "$got" != "$want" ]; then echo "AXIOM RESULTS: $got of $want commands"; return 1; fi
  echo "axioms: $got results; only propext, Classical.choice, Quot.sound"
}
# Cheap checks need no controls. Source-only FGSA/run/claims checks already passed
# in gate_precheck, before build. Keep the receipt's exact top-level result set:
# the extra early old-read pass has its log/result below early/, and the original
# check-fgsa still runs the audit and all selected controls without a skip flag.
step fg-finality-coverage python3 -B scripts/check-fg-finality-coverage.py
summary fg-finality-coverage
stop_if_failed
for name in catalog-lock v2-manifest gen-manifest; do
  run_check "$name"
  summary "$name"
  stop_if_failed
done
early_old_reads() {
  local logs=$logs/early
  mkdir -p "$logs"
  step fgsa-old-reads gate_with_slot lake env lean --run scripts/CheckFGSAOldReads.lean
  summary fgsa-old-reads
  stop_if_failed
}
early_old_reads
# C14: keep required audit lines tied to their declaration's owning module.
step proof-audit-coverage gate_with_slot python3 scripts/check-proof-coverage.py
summary proof-audit-coverage
stop_if_failed
for lib in Generic FGSA FGSARun; do
  step "$lib-axioms" audit "$(gate_source_path "AvailableChain$lib.Tests.Axioms")" \
  "$logs/$lib.axioms"
  summary "$lib-axioms"
  stop_if_failed
done
step FGCompose-axioms audit "$(gate_source_path AvailableChainFGCompose.Tests.Axioms)" \
  "$logs/FGCompose.axioms"
summary FGCompose-axioms
stop_if_failed
step FGSACompose-axioms audit "$(gate_source_path AvailableChainFGSAProofs.Tests.FGCompose)" \
  "$logs/FGSACompose.axioms"
summary FGSACompose-axioms
stop_if_failed
step FGSafety-axioms audit "$(gate_source_path AvailableChainFGCompose.Tests.SafetyAxioms)" \
  "$logs/FGSafety.axioms"
summary FGSafety-axioms
stop_if_failed
step FGSASafety-axioms audit "$(gate_source_path AvailableChainFGSAProofs.Tests.FGSafety)" \
  "$logs/FGSASafety.axioms"
summary FGSASafety-axioms
stop_if_failed
# P13: the growth companion audit and blueprint → Lean map (D10, FULL only).
growth_audit=$(gate_source_path \
  AvailableChainFGSAProofs.Tests.WeakContinuationGrowthAssemblyAxioms)
step FGSAGrowth-axioms audit_strict "$growth_audit" \
  "$logs/FGSAGrowth.axioms"
summary FGSAGrowth-axioms
stop_if_failed
if [ "$tier" = full ]; then
  step fgsa-blueprint gate_with_slot python3 -B scripts/check-fgsa-blueprint.py --check
  summary fgsa-blueprint
  stop_if_failed
fi
if [ "$NEG" = 1 ]; then
  step checker-self-tests bash scripts/check-build.sh --selftests-only
  summary checker-self-tests
  stop_if_failed
fi
# Start the measured long tail earlier; this is submission order only.
# No control writes the real source/build tree. Shared slots bound every child;
# Linux's existing memory scope bounds the whole group, including private builds.
run_group fgsa-claims check-fg-compose fgsa-manifest check-fgsa-run check-fgsa \
  check-build
finish
exit "$failed"
