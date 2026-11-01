#!/usr/bin/env bash
# Source-only controls. All source changes and Git refs are temporary.
set -euo pipefail
cd "$(dirname "$0")/.."
repo=$PWD
head=$(git rev-parse --verify HEAD)
objects=$(cd "$(git rev-parse --git-path objects)" && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/precheck-selftest.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Any accidental Lake/Lean command must fail and leave evidence.
mkdir "$scratch/bin"
cat > "$scratch/bin/lake" <<'SH'
#!/usr/bin/env bash
echo "UNEXPECTED LEAN/LAKE CALL: $0" >&2
touch "$PRECHECK_TOOL_SENTINEL"
exit 97
SH
cp "$scratch/bin/lake" "$scratch/bin/lean"
chmod +x "$scratch/bin/lake" "$scratch/bin/lean"
export PATH="$scratch/bin:$PATH" PRECHECK_TOOL_SENTINEL="$scratch/tool-called"
export PYTHONDONTWRITEBYTECODE=1

init_snapshot() {
  local tree=$1 commit=$2
  git init -q "$tree"
  printf '%s\n' "$objects" > "$tree/.git/objects/info/alternates"
  git -C "$tree" read-tree "$commit"
  git -C "$tree" update-ref HEAD "$commit"
}
expect_rejection() {
  local label=$1 rc=$2 log=$3 pattern=$4
  if [ "$rc" -eq 0 ] || [ "$rc" -ge 128 ] || ! grep -qF "$pattern" "$log"; then
    cat "$log"
    echo "SELFTEST FAIL: $label rc=$rc; expected $pattern" >&2
    exit 1
  fi
  echo "rejected, as expected: $label rc=$rc"
}
expect_no_build() {
  local tree=$1
  if [ -e "$tree/build-started" ] || [ -e "$tree/.lake/gate-last-full" ]; then
    echo "SELFTEST FAIL: build or full-pass stamp after rejection" >&2
    exit 1
  fi
}
expect_guard_pass() {
  local label=$1 rc=$2 log=$3
  if [ "$rc" -ne 0 ] || ! grep -qF 'guard lists: current data parsed; diff reported' "$log" ||
      ! grep -qF 'guard list merge: target data and main code OK' "$log" ||
      ! grep -qF 'MAIN POLICY PASS' "$log"; then
    cat "$log"
    echo "SELFTEST FAIL: $label rc=$rc; expected guard lists and merge to pass" >&2
    exit 1
  fi
  echo "$label rc=$rc (diff and merged target lists pass)"
}

# Commit 1: copy the current source tree and add a forbidden Statements import.
bad=$scratch/forbidden
mkdir "$bad"
git ls-files -z |
  rsync -a --from0 --files-from=- --exclude=/.git --exclude=/.lake "$repo/" "$bad/"
rsync -a --exclude=__pycache__ --exclude='*.pyc' "$repo/scripts/" "$bad/scripts/"
init_snapshot "$bad" "$head"
python3 - "$bad" "$repo/scripts/precheck-fixtures/forbidden-import.txt" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, str(Path(sys.argv[1]) / 'scripts'))
from source_layout import Layout
root = Path(sys.argv[1])
path = root / Layout(root).source_path('AvailableChainFGSA.Statements.Store')
text = path.read_text()
assert 'module\n' in text
path.write_text(text.replace('module\n', 'module\n' + Path(sys.argv[2]).read_text(), 1))
PY
rc=0
(
  set -e
  cd "$bad"
  source scripts/gate-common.sh
  build_all() { touch build-started; }
  gate_precheck "$head" || exit $?
  build_all
  mkdir -p .lake
  touch .lake/gate-last-full
) > "$scratch/forbidden.log" 2>&1 || rc=$?
expect_rejection forbidden-import "$rc" "$scratch/forbidden.log" 'PRECHECK FAIL check-layers; build not started'
expect_rejection forbidden-import-rule "$rc" "$scratch/forbidden.log" 'AvailableChainGeneric.Proofs.Pure.Walk'
expect_no_build "$bad"

# Commit 1: unrelated commits cannot pass the base check. No source scan is needed.
dag=$scratch/dag
git init -q "$dag"
empty=$(git -C "$dag" mktree </dev/null)
left=$(printf 'left\n' | git -C "$dag" -c user.name=Precheck -c user.email=precheck@example.invalid commit-tree "$empty")
right=$(printf 'right\n' | git -C "$dag" -c user.name=Precheck -c user.email=precheck@example.invalid commit-tree "$empty")
git -C "$dag" update-ref HEAD "$left"
rc=0
(
  set -e
  cd "$dag"
  source "$repo/scripts/gate-common.sh"
  build_all() { touch build-started; }
  gate_precheck "$right" || exit $?
  build_all
  mkdir -p .lake
  touch .lake/gate-last-full
) > "$scratch/base.log" 2>&1 || rc=$?
expect_rejection non-descendant-base "$rc" "$scratch/base.log" "BASE REFUSED: HEAD ${left:0:7} does not descend from base ${right:0:7}"
expect_rejection base-precheck "$rc" "$scratch/base.log" 'PRECHECK FAIL base; build not started'
expect_no_build "$dag"
(
  cd "$dag"
  source "$repo/scripts/gate-common.sh"
  gate_check_base "$left"
)
echo 'ancestor-base rc=0'

# Commit 2: use HEAD sources. Do not use the local main ref: it is stale on the
# NUC. The gate runs the precheck on HEAD first, so its findings cannot mask F-28.
# The policy checkout has this script set; its target has a permissive guard.
source_base=$head
policy=$scratch/policy
target=$scratch/target
mkdir "$policy" "$target"
git archive "$source_base" | tar -xf - -C "$policy"
rsync -a --exclude=__pycache__ --exclude='*.pyc' "$repo/scripts/" "$policy/scripts/"
init_snapshot "$policy" "$source_base"
git archive "$source_base" | tar -xf - -C "$target"
# Same script set as the policy copy: on an uncommitted tree, HEAD's scripts lack
# the working allow lines that the working EXPECTED lists need (06, 2026-10-01).
rsync -a --exclude=__pycache__ --exclude='*.pyc' "$repo/scripts/" "$target/scripts/"
init_snapshot "$target" "$source_base"
# This fixture checks main-policy Claims code against a permissive target guard.
# Keep unrelated production GLY findings in the real gate, outside this fixture.
cat >> "$policy/scripts/gate-common.sh" <<'SH'
gate_precheck() {
  export SOURCE_ONLY=1
  gate_precheck_step guard-lists python3 scripts/guard-lists.py diff \
    --main-rev "$1" --target scripts/check-fgsa-claims.sh || return $?
  gate_precheck_step check-fgsa-claims bash scripts/check-fgsa-claims.sh || return $?
  echo 'PRECHECK PASS; build not started'
}
SH
claims_audit=$(python3 -B scripts/source_layout.py --root "$target" \
  path AvailableChainFGSAClaims.Tests.Axioms)
cat "$repo/scripts/precheck-fixtures/claims-theorem.txt" >> "$target/$claims_audit"
control=$repo/scripts/precheck-fixtures/guard-lists-control.py
python3 "$control" permissive "$target/scripts/check-fgsa-claims.sh" "$policy/scripts/check-fgsa-claims.sh"
rc=0
bash "$policy/scripts/precheck.sh" "$target" > "$scratch/policy.log" 2>&1 || rc=$?
expect_rejection main-policy-f28 "$rc" "$scratch/policy.log" 'F-28: AvailableChainFGSAClaims.Tests.Axioms precheckForbiddenClaim'
expect_rejection main-policy-guard "$rc" "$scratch/policy.log" "MAIN POLICY FAIL check-fgsa-claims main=${source_base:0:7} target=${source_base:0:7}"
expect_no_build "$target"

# Keep the list controls fast. Inspect the merged checker instead of scanning
# the source tree, and repeat the gate's history check with the copied allow data.
cat >> "$policy/scripts/gate-common.sh" <<'SH'
gate_precheck() {
  gate_precheck_step guard-lists python3 scripts/guard-lists.py diff \
    --main-rev "$1" --target scripts/check-fgsa-claims.sh || return $?
  python3 scripts/precheck-fixtures/guard-lists-control.py verify \
    scripts/check-fgsa-claims.sh "$GUARD_LISTS_TARGET" "$GUARD_LISTS_MAIN" || return $?
  echo 'PRECHECK PASS; build not started'
}
SH
export GUARD_LISTS_TARGET="$target/scripts/check-fgsa-claims.sh"
export GUARD_LISTS_MAIN="$policy/scripts/check-fgsa-claims.sh"
python3 "$control" extra "$GUARD_LISTS_TARGET" "$GUARD_LISTS_MAIN"
rc=0
bash "$policy/scripts/precheck.sh" "$target" > "$scratch/lists-extra.log" 2>&1 || rc=$?
expect_guard_pass guard-lists-extra "$rc" "$scratch/lists-extra.log"
expect_no_build "$target"

removed=$(python3 "$control" drop "$GUARD_LISTS_TARGET" "$GUARD_LISTS_MAIN")
rc=0
bash "$policy/scripts/precheck.sh" "$target" > "$scratch/lists-drop.log" 2>&1 || rc=$?
expect_guard_pass guard-lists-drop "$rc" "$scratch/lists-drop.log"
grep -qF "GUARD LIST REMOVED: EXPECTED $removed" "$scratch/lists-drop.log"
expect_no_build "$target"

# Use the real expose checker for policy data, without another full scan.
cp "$policy/scripts/check-fgsa-claims.sh" "$target/scripts/check-fgsa-claims.sh"
export POLICY_DATA_TARGET="$target"
cat >> "$policy/scripts/gate-common.sh" <<'SH'
gate_precheck() {
  cmp scripts/baselines/check-expose.txt "$POLICY_DATA_TARGET/scripts/baselines/check-expose.txt" || return $?
  gate_precheck_step check-expose python3 scripts/check-expose.py || return $?
  echo 'PRECHECK PASS; build not started'
}
SH
# Target checker code must not replace main's checker.
printf 'raise SystemExit(99)\n' > "$target/scripts/check-expose.py"
source_path=$(python3 -B scripts/source_layout.py --root "$target" \
  path AvailableChainGeneric.Proofs.Pure.Walk)
logical_path=AvailableChainGeneric/Proofs/Pure/Walk.lean
printf '\n@[expose] def precheckPolicyAllow : Nat := 0\n' >> "$target/$source_path"
rc=0
bash "$policy/scripts/precheck.sh" "$target" > "$scratch/data-no-allow.log" 2>&1 || rc=$?
expect_rejection policy-data-no-allow "$rc" "$scratch/data-no-allow.log" 'precheckPolicyAllow (not in scripts/expose-allow.txt)'
expect_no_build "$target"

expect_policy_pass() {
  local label=$1 rc=$2 log=$3 pattern=$4 summary=$5
  if [ "$rc" -ne 0 ] || ! grep -qxF "$pattern" "$log" || [ "$(tail -n 1 "$log")" != "$summary" ]; then
    cat "$log"
    echo "SELFTEST FAIL: $label rc=$rc; expected $pattern and $summary" >&2
    exit 1
  fi
  echo "$label rc=$rc"
  echo "$pattern"
  expect_no_build "$target"
}
allow_line="$logical_path precheckPolicyAllow"
printf '%s\n' "$allow_line" >> "$target/scripts/expose-allow.txt"
rc=0
bash "$policy/scripts/precheck.sh" "$target" > "$scratch/data-allow.log" 2>&1 || rc=$?
expect_policy_pass policy-data-allow "$rc" "$scratch/data-allow.log" \
  "POLICY DATA REVIEW: +scripts/expose-allow.txt: $allow_line" \
  'MAIN POLICY PASS (with 1 policy-data additions for review)'

# Remove a resolved finding and exactly one baseline entry.
git show "$head:$source_path" > "$target/$source_path"
cp "$policy/scripts/expose-allow.txt" "$target/scripts/expose-allow.txt"
python3 - "$target" <<'PY'
from pathlib import Path
import sys
sys.path.insert(0, str(Path(sys.argv[1]) / 'scripts'))
from source_layout import Layout
root = Path(sys.argv[1])
source = root / Layout(root).source_path('AvailableChainSAPC.Proofs.Archive')
text = source.read_text()
assert text.count('@[expose] public section') == 1
source.write_text(text.replace('@[expose] public section', 'public section'))
baseline = root / 'scripts/baselines/check-expose.txt'
text = baseline.read_text()
entry = 'expose-section AvailableChainSAPC/Proofs/Archive.lean\n'
assert text.count(entry) == 1
baseline.write_text(text.replace(entry, ''))
PY
rc=0
bash "$policy/scripts/precheck.sh" "$target" > "$scratch/data-baseline.log" 2>&1 || rc=$?
expect_policy_pass policy-data-baseline "$rc" "$scratch/data-baseline.log" \
  'POLICY DATA: -1 scripts/baselines/check-expose.txt' \
  "MAIN POLICY PASS main=${head:0:7} target=${head:0:7}"
if grep -qF 'POLICY DATA REVIEW:' "$scratch/data-baseline.log"; then
  cat "$scratch/data-baseline.log"
  echo 'SELFTEST FAIL: baseline removal reported additions' >&2
  exit 1
fi
if [ -e "$PRECHECK_TOOL_SENTINEL" ]; then
  echo 'SELFTEST FAIL: Lean or Lake was called' >&2
  exit 1
fi
echo 'precheck-selftest: PASS (no build, Lean, Lake or full-pass stamp)'
