#!/usr/bin/env bash
# Land the current commit on main (AGENTS.md "Land on main"): the only way to push to main. It refuses unless
#   - the tree is clean (check-changed would also check uncommitted and untracked files, which are not pushed),
#   - HEAD contains origin/main (rebase first),
#   - `scripts/check.sh --changed origin/main` passes (the downstream cone of the change; a change to scripts/ or the
#     build configuration runs the whole fast mode, with self-tests for scripts/),
#   - `scripts/review-boundary.sh origin/main` passes (a trusted-surface change needs the tag: go through a PR),
#   - origin/main did not move while the check ran (if it did: rebase, if clean, and check again; up to
#     PUSH_MAIN_TRIES = 3 rounds);
# then it records HEAD as verified (for the pre-push hook scripts/hooks/pre-push), pushes HEAD to main and prints
# the check's result line. Usage: scripts/push-main.sh   (in a job on the shared box; RUN_DIR is set if missing).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
die() { echo "push-main: REFUSED: $*" >&2; exit 1; }
remote=origin
git fetch -q --tags --force "$remote" main || die "cannot fetch $remote main"
[[ -z "$(git status --porcelain)" ]] ||
  { git status --short >&2; die "uncommitted or untracked files (commit them, or remove them): the check would include them"; }
tries="${PUSH_MAIN_TRIES:-3}"
while :; do
  base="$(git rev-parse "$remote/main")" head="$(git rev-parse HEAD)"
  [[ "$base" != "$head" ]] || die "HEAD is $remote/main: nothing to push"
  git merge-base --is-ancestor "$base" HEAD ||
    die "HEAD does not contain $remote/main (${base:0:8}): git rebase $remote/main, then run this again"
  log="$(mktemp)"
  export RUN_DIR="${RUN_DIR:-$(mktemp -d)}"
  echo "push-main: checking ${head:0:8} against $remote/main ${base:0:8} (scripts/check.sh --changed)"
  rc=0
  scripts/check.sh --changed "$base" 2>&1 | tee "$log" || rc=$?
  result="$(grep '^check.sh: ' "$log" | tail -1)"
  ((rc == 0)) && [[ "$result" == "check.sh: PASSED"* ]] || die "${result:-check.sh did not finish} (log: $log)"
  scripts/review-boundary.sh "$base" || die "review boundary: a trusted-surface change needs spec-approved (a PR; docs/spec-review.md)"
  git fetch -q --tags --force "$remote" main
  [[ "$(git rev-parse "$remote/main")" == "$base" ]] && break
  # main moved while the check ran: rebase (only if clean) and check again, against the new main.
  tries=$((tries - 1))
  ((tries > 0)) || die "$remote/main kept moving while the check ran (PUSH_MAIN_TRIES); run this again"
  git rebase -q "$remote/main" || { git rebase --abort; die "$remote/main moved and the rebase conflicts: resolve, then run this again"; }
  echo "push-main: $remote/main moved; rebased onto $(git rev-parse --short "$remote/main"), checking again"
done
echo "$head" >>"$(git rev-parse --git-common-dir)/push-main-verified"
git push "$remote" HEAD:main
echo "push-main: pushed ${head:0:8} to main after: $result"
