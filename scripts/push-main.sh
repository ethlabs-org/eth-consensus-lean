#!/usr/bin/env bash
# Land the current commit on main (AGENTS.md "Land on main"): the only way to push to main. It refuses unless
#   - the tree is clean (check-changed would also check uncommitted and untracked files, which are not pushed),
#   - HEAD contains origin/main (rebase first),
#   - `scripts/check.sh --changed origin/main` passes (the downstream cone of the change; a change to scripts/ or the
#     build configuration runs the whole fast mode, with self-tests for scripts/),
#   - `scripts/review-boundary.sh origin/main` passes (every commit that touches the trusted surface carries a
#     `Trusted-surface: <what and why>` line),
#   - `scripts/check-commit-emails.py origin/main HEAD` passes (every author, committer and co-author address of the
#     commits to push is on the public allowlist scripts/commit-emails.toml);
# then it records HEAD as verified (for the pre-push hook scripts/hooks/pre-push), pushes HEAD to main as a
# fast-forward of the commit it checked against, and prints the check's result line. The record of a trusted-surface
# change is its commits' Trusted-surface lines and the `check` run of main's push (scripts/review-boundary.sh).
# It refuses a GitHub `origin` other than the code repository (`code` in scripts/repos.toml), before and again right
# after fetching main. The slug comes from scripts/repos.toml on the target, origin/main, not from HEAD: a change that
# renames the code repository is checked against the name it lands under, and once it has landed, a clone still
# pointing at the old name is refused. A target without the file (before it existed) has no guard.
#
# Contention. The first round runs without a lock. If main moved meanwhile, the next rounds hold the landing
# lock, the branch `push-main-lock` on the remote: one lander at a time rebases, checks and pushes, so its round cannot
# be overtaken by another push-main. Others wait for the lock (polling every 30 s) instead of checking in vain, and do
# not push while someone else holds it. A lock older than PUSH_MAIN_LOCK_TTL seconds (default 1800) is taken over.
# Correctness never depends on the lock: the push is a fast-forward of the checked base, so a push that would land an
# unchecked combination is rejected by git. Rounds: PUSH_MAIN_TRIES (default 6).
# Usage: scripts/push-main.sh   (RUN_DIR is set if missing).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
started=$SECONDS
timing() { echo "push-main: timing $1=$((SECONDS - $2))s"; }
die() { echo "push-main: REFUSED: $*" >&2; release; exit 1; }
remote=origin lock_ref=refs/heads/push-main-lock ttl="${PUSH_MAIN_LOCK_TTL:-1800}" held=""
repos() { git show "$remote/main:scripts/repos.toml" |
  python3 -I -c 'import sys, tomllib; print(tomllib.loads(sys.stdin.read())[sys.argv[1]])' "$1"; }
guard() {  # sets code from the target's scripts/repos.toml; refuses an origin that is another repository
  local url slug=""
  url="$(git config "remote.$remote.url")"  # as configured: insteadOf rewrites do not change which repository it is
  [[ ! "$url" =~ ^(https://github\.com/|git@github\.com:|ssh://git@github\.com/)(.*)$ ]] ||
    slug="$(sed -E 's#\.git$##; s#/$##' <<<"${BASH_REMATCH[2]}")"
  if git cat-file -e "$remote/main:scripts/repos.toml" 2>/dev/null; then
    code="$(repos code)" || die "cannot read scripts/repos.toml on $remote/main"
  else
    code=""
  fi
  [[ -z "$slug" || -z "$code" || "$slug" == "$code" ]] ||
    die "$remote is $url, but the code repository is $code (scripts/repos.toml on $remote/main): use a clone of https://github.com/$code.git"
}
lock_info() {  # prints "<sha> <unix time> <owner...>" of the remote lock, or nothing
  local sha
  sha="$(git ls-remote "$remote" "$lock_ref" | cut -f1)"
  [[ -n "$sha" ]] || return 0
  git fetch -q "$remote" "+$lock_ref:refs/push-main/lock" 2>/dev/null || return 0
  echo "$sha $(git log -1 --format='%ct %s' refs/push-main/lock)"
}
acquire() {  # take the lock (create, or take over an expired one); waits while someone else holds it
  local info sha t owner now
  owner="$(hostname) $$ $(git rev-parse --short HEAD)"
  while :; do
    info="$(lock_info)" now="$(date +%s)"
    if [[ -z "$info" ]]; then
      held="$(git commit-tree -m "push-main lock: $owner" "$(git hash-object -t tree /dev/null)" </dev/null)"
      git push -q --force-with-lease="$lock_ref:" "$remote" "$held:$lock_ref" 2>/dev/null && return 0
    else
      read -r sha t _ <<<"$info"
      if ((now - t > ttl)); then
        echo "push-main: taking over an expired lock ($(cut -d' ' -f3- <<<"$info"), $((now - t)) s old)"
        held="$(git commit-tree -m "push-main lock: $owner" "$(git hash-object -t tree /dev/null)" </dev/null)"
        git push -q --force-with-lease="$lock_ref:$sha" "$remote" "+$held:$lock_ref" 2>/dev/null && return 0
      else
        echo "push-main: waiting for the landing lock ($(cut -d' ' -f3- <<<"$info"), $((now - t)) s old)"
      fi
    fi
    held=""; sleep 30
  done
}
release() {
  [[ -n "$held" ]] || return 0
  git push -q --force-with-lease="$lock_ref:$held" "$remote" ":$lock_ref" 2>/dev/null || true
  held=""
}
# Cancellation must stop the landing, not merely release its lock and resume.
# EXIT performs cleanup for both normal completion and signal-triggered exits.
trap 'rc=$?; release; timing total "$started"; echo "push-main: exit=$rc"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

guard
git fetch -q --tags --force "$remote" main || die "cannot fetch $remote main"
guard
[[ -z "$(git status --porcelain)" ]] ||
  { git status --short >&2; die "uncommitted or untracked files (commit them, or remove them): the check would include them"; }
tries="${PUSH_MAIN_TRIES:-6}"
while :; do
  [[ -z "$(git status --porcelain)" ]] || die "tree changed before checking"
  base="$(git rev-parse "$remote/main")" head="$(git rev-parse HEAD)"
  [[ "$base" != "$head" ]] || die "HEAD is $remote/main: nothing to push"
  git merge-base --is-ancestor "$base" HEAD ||
    die "HEAD does not contain $remote/main (${base:0:8}): git rebase $remote/main, then run this again"
  log="$(mktemp)"
  export RUN_DIR="${RUN_DIR:-$(mktemp -d)}"
  echo "push-main: checking ${head:0:8} against $remote/main ${base:0:8} (scripts/check.sh --changed)${held:+, holding the lock}"
  phase=$SECONDS
  rc=0
  scripts/check.sh --changed "$base" 2>&1 | tee "$log" || rc=$?
  timing check "$phase"
  result="$(grep '^check.sh: ' "$log" | tail -1)"
  ((rc == 0)) && [[ "$result" == "check.sh: PASSED"* ]] || die "${result:-check.sh did not finish} (log: $log)"
  phase=$SECONDS
  scripts/review-boundary.sh "$base" || die "review boundary: label each commit that touches the trusted surface with a Trusted-surface: line"
  timing review-boundary "$phase"
  # Before the upload: the email allowlist of every commit to push (scripts/commit-emails.toml; CI runs it again).
  python3 -I scripts/check-commit-emails.py "$base" "$head" ||
    die "commit emails: rewrite the commits above with an allowed address (scripts/commit-emails.toml)"
  git fetch -q --tags --force "$remote" main
  if [[ "$(git rev-parse "$remote/main")" == "$base" ]]; then
    # Without the lock, don't overtake a lander that holds it (it checked against this same main).
    info="$([[ -n "$held" ]] || lock_info)"
    if [[ -z "$info" ]]; then
      [[ "$(git rev-parse HEAD)" == "$head" && -z "$(git status --porcelain)" ]] ||
        die "HEAD or tree changed during checks"
      echo "$head" >>"$(git rev-parse --git-common-dir)/push-main-verified"
      phase=$SECONDS
      if out="$(git push --force-with-lease="refs/heads/main:$base" "$remote" "$head:refs/heads/main" 2>&1)"; then
        printf '%s\n' "$out"
        release
        timing delivery "$phase"
        echo "push-main: pushed ${head:0:8} to main after: $result"
        exit 0
      fi
      printf '%s\n' "$out" >&2
      # Only a lease rejection (` ! [rejected] ... (stale info)`, main moved) is contention. Anything else, such as
      # the remote declining (a ruleset such as GH013 "must be made through a pull request", a protected branch, a
      # hook: `[remote rejected]`) or an authentication or network failure, no rebase or retry can fix, so stop at
      # once (die releases the lock).
      grep -q '\[remote rejected\]' <<<"$out" &&
        die "the remote declined the push to main, not because main moved ($(grep -m1 -oE 'GH[0-9]+[^.]*|\[remote rejected\].*' <<<"$out")): nothing was pushed; fix the access or the rule, then run this again"
      grep -q '^ ! \[rejected\]' <<<"$out" ||
        die "the push to main failed, not because main moved ($(grep -m1 -E 'fatal|error' <<<"$out" || echo 'see above')): nothing was pushed; fix it, then run this again"
      echo "push-main: the push was rejected (main moved at the last moment)"
    fi
  fi
  # main moved (or someone holds the lock): take the lock, rebase (only if clean) and check again.
  tries=$((tries - 1))
  ((tries > 0)) || die "$remote/main kept moving (PUSH_MAIN_TRIES rounds); run this again"
  if [[ -z "$held" ]]; then
    phase=$SECONDS
    acquire
    timing lock-acquire "$phase"
  fi
  [[ "$(git rev-parse HEAD)" == "$head" && -z "$(git status --porcelain)" ]] ||
    die "HEAD or tree changed before rebase"
  phase=$SECONDS
  git fetch -q --tags --force "$remote" main
  git rebase -q "$remote/main" || { git rebase --abort; die "$remote/main moved and the rebase conflicts: resolve, then run this again"; }
  timing fetch-rebase "$phase"
  echo "push-main: rebased onto $(git rev-parse --short "$remote/main"); checking again under the lock"
done
