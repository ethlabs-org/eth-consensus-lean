#!/usr/bin/env bash
# Run this checkout's source policy against a tracked copy of a worktree.
# Sources, lakefile and policy data come from the target; checker code is ours.
# The temporary Git index uses the target HEAD. No worktree or build is created.
set -euo pipefail
brief=; base=; receipt=
usage() {
  echo 'usage: precheck.sh [--brief FILE] [--base REF] [--full-pass RECEIPT] <worktree>'
}
while [ $# -gt 1 ]; do
  [ $# -ge 3 ] || { usage >&2; exit 2; }
  case "$1" in
    --brief) brief=$2 ;;
    --base) base=$2 ;;
    --full-pass) receipt=$2 ;;
    *) usage >&2; exit 2 ;;
  esac
  shift 2
done
[ $# -eq 1 ] || { usage >&2; exit 2; }
[ -z "$base" ] || [ -n "$brief" ] || { usage >&2; exit 2; }
main_root=$(cd "$(dirname "$0")/.." && pwd -P)
target_root=$(cd "$1" && pwd -P)
main_head=$(git -C "$main_root" rev-parse --verify HEAD)
target_head=$(git -C "$target_root" rev-parse --verify HEAD)
if [ "$(git -C "$target_root" rev-parse --show-toplevel)" != "$target_root" ]; then
  echo "precheck.sh: target must be a worktree root" >&2
  exit 2
fi

if [ -n "$brief" ]; then
  python3 "$main_root/scripts/precheck-scope.py" "$target_root" \
    "${base:-$main_head}" "$brief"
fi
if [ -n "$receipt" ]; then
  python3 "$main_root/scripts/full-pass.py" verify "$main_root" "$target_root" "$receipt"
  echo 'MAIN POLICY COPY SKIPPED: verified exact-head FULL PASS'
  exit 0
fi

scratch=$(mktemp -d "${TMPDIR:-/tmp}/main-precheck.XXXXXX")
tree=$scratch/tree
check=copy
cleanup() {
  local rc=$?
  trap - EXIT
  if [ "$rc" -ne 0 ]; then
    echo "MAIN POLICY FAIL $check main=${main_head:0:7} target=${target_head:0:7}" >&2
  fi
  rm -rf "$scratch"
  exit "$rc"
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
mkdir "$tree"
echo "main policy: main=${main_head:0:7} target=${target_head:0:7}"
# Copy tracked working files, so an uncommitted source edit is checked too.
# Do not copy target scripts, Git state, or build output.
git -C "$target_root" ls-files -z |
  rsync -a --from0 --files-from=- --exclude=/scripts --exclude=/.git --exclude=/.lake \
    "$target_root/" "$tree/"
rsync -a --exclude=__pycache__ --exclude='*.pyc' "$main_root/scripts/" "$tree/scripts/"

if [ -f "$target_root/scripts/check-fgsa-claims.sh" ]; then
  check=guard-lists
  echo '== precheck guard-lists'
  python3 "$main_root/scripts/guard-lists.py" diff \
    --main "$main_root/scripts/check-fgsa-claims.sh" \
    --target "$target_root/scripts/check-fgsa-claims.sh"
  python3 "$main_root/scripts/guard-lists.py" merge \
    --code "$main_root/scripts/check-fgsa-claims.sh" \
    --data "$target_root/scripts/check-fgsa-claims.sh" \
    --out "$tree/scripts/check-fgsa-claims.sh"

fi

# Keep the target's allow lists and baselines; report changes for review.
# Missing target files retain the policy copy from main.
check=policy-data
python3 - "$main_root" "$target_root" "$tree" "$scratch/policy-additions" <<'PY'
from difflib import SequenceMatcher
from pathlib import Path
import shutil
import sys

main, target, tree, count_file = map(Path, sys.argv[1:])
additions = 0
files = sorted([*target.glob('scripts/*-allow.txt'),
                *target.glob('scripts/*-expected.txt'),
                *target.glob('scripts/baselines/*.txt')])
for source in files:
    if not source.is_file():
        continue
    relative = source.relative_to(target)
    reference = main / relative
    before = reference.read_text().splitlines() if reference.is_file() else []
    after = source.read_text().splitlines()
    removed = 0
    for tag, i, j, k, l in SequenceMatcher(None, before, after, autojunk=False).get_opcodes():
        if tag in ('replace', 'delete'):
            removed += j - i
        if tag in ('replace', 'insert'):
            for line in after[k:l]:
                print(f'POLICY DATA REVIEW: +{relative}: {line}')
                additions += 1
    if removed:
        print(f'POLICY DATA: -{removed} {relative}')
    destination = tree / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)
count_file.write_text(str(additions))
PY
policy_additions=$(cat "$scratch/policy-additions")

# The guard diff reads Git history. Use read-only object stores with a private
# index and refs, instead of adding a worktree to either checkout.
check=git-snapshot
target_objects=$(cd "$target_root" && cd "$(git rev-parse --git-path objects)" && pwd -P)
main_objects=$(cd "$main_root" && cd "$(git rev-parse --git-path objects)" && pwd -P)
git init -q "$tree"
printf '%s\n%s\n' "$target_objects" "$main_objects" > "$tree/.git/objects/info/alternates"
git -C "$tree" read-tree "$target_head"
git -C "$tree" update-ref HEAD "$target_head"

check=precheck
rc=0
(
  cd "$tree"
  source scripts/gate-common.sh
  gate_precheck "$main_head"
) > "$scratch/precheck.log" 2>&1 || rc=$?
cat "$scratch/precheck.log"
if [ "$rc" -ne 0 ]; then
  check=$(sed -n 's/^PRECHECK FAIL \(.*\); build not started$/\1/p' "$scratch/precheck.log")
  check=${check:-precheck}
  exit "$rc"
fi
if [ "$policy_additions" -gt 0 ]; then
  echo "MAIN POLICY PASS (with $policy_additions policy-data additions for review)"
else
  echo "MAIN POLICY PASS main=${main_head:0:7} target=${target_head:0:7}"
fi
