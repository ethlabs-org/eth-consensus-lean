#!/usr/bin/env bash
# Fallback CI without GitHub Actions (#50): checks new heads of `main` and of open, non-draft PRs into `main` in an
# orb, as ci.yml would, and records each result in the table of issue $ORB_CI_ISSUE (default 63); a failure is also a
# comment (#17 for main, the PR for a PR), and a PR's result is commented on the PR. (The agent token cannot post
# commit statuses or check runs: HTTP 403.) Run it as a supervised service so it survives restarts and pauses:
#   amp orb service start orb-ci --command 'bash <checkout>/scripts/orb-ci.sh'
# Re-check commits of main on request: append their SHAs to $ORB_CI_HOME/queue (one per line).
# It copies itself to $ORB_CI_HOME and runs the copy, checks out each head (a PR merged into main first, like
# GitHub's merge commit) in its own worktree $ORB_CI_HOME/wt with hard-linked Lake packages, and keeps logs in
# $ORB_CI_HOME/logs. Options: --once (one pass, then exit). Environment: ORB_CI_HOME (default ~/orb-ci),
# ORB_CI_INTERVAL (seconds between passes, default 600), ORB_CI_REPO (the checkout it was started from),
# ORB_CI_SIGN (the comments' sign-off), ORB_CI_JOB (the shared box: `job` options and scope, e.g.
# '--mem 16G --cpus 8 consensus-lean'; each check.sh run is then a box `job`, waited for; unset in an orb).
# Mode as in ci.yml: docs-only change -> `check.sh --changed <base>`; otherwise `--fast`, with `--selftests` when
# scripts/ or the build configuration changed and `--canary` when the build configuration changed; then
# scripts/review-boundary.sh <base> and a clean-tree check. <base>: the previously checked main head (if an
# ancestor), or a PR's main.
set -uo pipefail
HOME_DIR="${ORB_CI_HOME:-$HOME/orb-ci}"
if [[ "${ORB_CI_COPY:-}" != 1 ]]; then  # run from a copy: the checkout may change under a running script
  mkdir -p "$HOME_DIR"
  cp "${BASH_SOURCE[0]}" "$HOME_DIR/orb-ci.sh"
  ORB_CI_REPO="${ORB_CI_REPO:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}" ORB_CI_COPY=1 exec bash "$HOME_DIR/orb-ci.sh" "$@"
fi
REPO="$ORB_CI_REPO" WT="$HOME_DIR/wt" LOGS="$HOME_DIR/logs" DONE="$HOME_DIR/done" ISSUE="${ORB_CI_ISSUE:-63}"
INTERVAL="${ORB_CI_INTERVAL:-600}"
SLUG="$(gh repo view "$(git -C "$REPO" remote get-url origin)" --json nameWithOwner -q .nameWithOwner)"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p "$LOGS"; touch "$DONE"
log() { echo "$(date -u +%FT%TZ) $*"; }
SIGN="${ORB_CI_SIGN:-— amp-orbs (process, orb-ci)}"

in_ci() {  # in_ci <cmd...>: run the command with CI set; with ORB_CI_JOB, in a box `job` (which sets RUN_DIR)
  [[ -n "${ORB_CI_JOB:-}" ]] || { CI=1 RUN_DIR="$(mktemp -d)" "$@"; return; }
  local opts unit st run rc
  read -ra opts <<<"$ORB_CI_JOB"
  # The job's output goes to its run folder (not the journal, which may drop lines), printed when it ends.
  unit="$(job "${opts[@]}" orb-ci -- bash -c 'CI=1 LAKE_RESTORE_ARTIFACTS=true "$@" >"$RUN_DIR/out.log" 2>&1' _ "$@" |
    awk '$1 == "started" { print $2 }')"
  [[ -n "$unit" ]] || { echo "orb-ci: job did not start"; return 1; }
  while systemctl --user -q is-active "$unit"; do sleep 10; done
  st="/srv/status/$(id -un).$unit.json"
  read -r run rc < <(python3 -I -c 'import json, sys; s = json.load(open(sys.argv[1]))
print(s.get("run_dir") or "-", s.get("exit", 1))' "$st" 2>/dev/null) || { echo "orb-ci: no status $st"; return 1; }
  echo "orb-ci: job $unit, run folder $run, exit $rc"
  cat "$run/out.log"
  return "$rc"
}

setup_worktree() {
  [[ -d "$WT" ]] && return 0
  git -C "$REPO" worktree add -q --detach "$WT" origin/main || return 1
  mkdir -p "$WT/.lake" && cp -al "$REPO/.lake/packages" "$WT/.lake/packages" &&
    { [[ ! -d "$REPO/.lake/build" ]] || cp -a "$REPO/.lake/build" "$WT/.lake/build"; }
}

record() {  # record <ref> <sha> <mode> <result>: a row at the top of the issue's table (the last 40 kept)
  local body row
  row="| $(date -u '+%m-%d %H:%M') | $1 | \`${2:0:8}\` | $3 | $4 |"
  body="$(gh issue view "$ISSUE" -R "$SLUG" --json body -q .body)" || { log "cannot read issue $ISSUE"; return; }
  body="$(ROW="$row" python3 -c 'import os, sys
b = sys.stdin.read(); head, rest = b.split("|---|---|---|---|---|\n", 1); rows, tail = rest.split("<!-- /orb-ci results -->", 1)
rows = [r for r in rows.splitlines() if r.startswith("|")][:39]
print(head + "|---|---|---|---|---|\n" + "\n".join([os.environ["ROW"]] + rows) + "\n<!-- /orb-ci results -->" + tail, end="")' <<<"$body")" &&
    gh issue edit "$ISSUE" -R "$SLUG" --body "$body" >/dev/null || log "cannot update issue $ISSUE"
}

# check <kind> <id> <head>: kind main|pr; records the result in the issue and comments.
check() {
  local kind="$1" id="$2" head="$3" base flags=() mode=fast paths rc=0 t0=$SECONDS lg="$LOGS/$3.log" fails
  cd "$WT" || return 1
  : >"$lg"
  git checkout -q --detach -f origin/main && git clean -qfdx -e .lake || return 1
  if [[ "$kind" == main-recheck ]]; then
    git checkout -q --detach "$head" || return 1
    base="$(git rev-parse -q --verify HEAD^1 || true)"
  elif [[ "$kind" == pr ]]; then
    base="$(git rev-parse origin/main)"
    if ! git -c user.email=orb-ci@local -c user.name=orb-ci -c commit.gpgsign=false merge -q --no-ff --no-edit "$head" >>"$lg" 2>&1; then
      git merge --abort 2>/dev/null
      record "PR #$id" "$head" merge "does not merge into main"; echo "$head merge-conflict" >>"$DONE"; return 0
    fi
  else
    git checkout -q --detach "$head" || return 1
    # The commit this push replaced: the last checked head of main if it is an ancestor, else the first parent.
    base="$(tail -n 200 "$DONE" | awk '$2 == "main" { s = $1 } END { print s }')"
    { [[ -n "$base" && "$base" != "$head" ]] && git merge-base --is-ancestor "$base" HEAD 2>/dev/null; } ||
      base="$(git rev-parse -q --verify HEAD^1 || true)"
  fi
  if [[ -n "$base" ]]; then
    paths="$(git diff --no-renames --name-only "$base" HEAD --)"
    if [[ -n "$paths" ]] && ! grep -qvE '(\.md$|^docs/)' <<<"$paths"; then mode=changed
    else
      grep -qE '^(scripts/|lakefile\.(toml|lean)$|lake-manifest\.json$|lean-toolchain$)' <<<"$paths" && flags+=(--selftests)
      grep -qE '^(lakefile\.(toml|lean)$|lake-manifest\.json$|lean-toolchain$)' <<<"$paths" && flags+=(--canary)
      # step 4's reach report when the trusted surface or scripts/ changed (as ci.yml)
      local trusted=()
      mapfile -t trusted < <(python3 -I -c 'import tomllib
print("\n".join(tomllib.load(open("scripts/boundaries.toml", "rb"))["checks"]["trusted_paths"]))' 2>/dev/null)
      GIT_LITERAL_PATHSPECS=1 git diff --quiet "$base" HEAD -- "${trusted[@]}" scripts || flags+=(--reach)
    fi
  else
    flags+=(--selftests --reach --canary)
  fi
  {
    echo "orb-ci: $kind $id at $head (base ${base:-none}), mode $mode ${flags[*]}"
    if [[ "$mode" == changed ]]; then
      in_ci scripts/check.sh --changed "$base" || rc=1
    else
      in_ci scripts/check.sh --fast "${flags[@]}" || rc=1
    fi
    echo "--- review boundary ---"; scripts/review-boundary.sh "$base" || rc=1
    [[ -z "$(git status --porcelain)" ]] || { echo "tree not clean:"; git status --porcelain; rc=1; }
  } >>"$lg" 2>&1
  local secs=$((SECONDS - t0))
  local ref="main" what="--$mode ${flags[*]}" body
  [[ "$kind" == pr ]] && ref="PR #$id"
  [[ "$kind" == main-recheck ]] && ref="main (re-check)"
  if ((rc == 0)); then
    record "$ref" "$head" "$what" "PASSED in ${secs}s"
    body="**orb-ci: PASSED** on \`${head:0:8}\` (merged into main \`${base:0:8}\`): \`check.sh $what\`, review boundary, clean tree; ${secs}s. Fallback CI while Actions is down (#50, results: #$ISSUE).

$SIGN"
  else
    fails="$(grep -E '^(FAIL|::error)' "$lg" | head -20)"
    record "$ref" "$head" "$what" "**FAILED** in ${secs}s"
    body="**orb-ci: FAILED** on \`${head:0:8}\` ($ref): \`check.sh $what\`, ${secs}s. Fallback CI while Actions is down (#50, results: #$ISSUE).

\`\`\`
${fails:-(no FAIL line; see the log $lg)}
\`\`\`
$SIGN"
  fi
  if [[ "$kind" == pr ]]; then gh pr comment "$id" -R "$SLUG" --body "$body" >/dev/null || log "cannot comment on PR #$id"
  elif ((rc != 0)) && [[ "$kind" == main ]]; then gh issue comment 17 -R "$SLUG" --body "$body" >/dev/null || log "cannot comment on #17"; fi
  echo "$head $kind $rc $secs" >>"$DONE"
  log "$kind ${id:-main} ${head:0:8}: rc=$rc ${secs}s"
}

pass() {
  # --tags --force: spec-approved moves (review-boundary compares against it)
  git -C "$REPO" fetch -q --tags --force origin main || { log "fetch failed"; return; }
  setup_worktree || { log "worktree setup failed"; return; }
  local head q
  # Re-checks on request: one commit of main per line in $HOME_DIR/queue (checked against its first parent).
  if [[ -s "$HOME_DIR/queue" ]]; then
    while read -r q; do
      [[ -n "$q" ]] && q="$(git -C "$REPO" rev-parse -q --verify "$q^{commit}")" && check main-recheck "" "$q"
    done <"$HOME_DIR/queue"
    : >"$HOME_DIR/queue"
  fi
  head="$(git -C "$REPO" rev-parse origin/main)"
  grep -q "^$head main " "$DONE" || check main "" "$head"
  local prs
  prs="$(gh pr list -R "$SLUG" --state open --base main --json number,headRefOid,isDraft \
    -q '.[] | select(.isDraft | not) | "\(.number) \(.headRefOid)"')" || { log "PR list failed"; return; }
  while read -r n sha; do
    [[ -n "$n" ]] || continue
    grep -q "^$sha " "$DONE" && continue
    git -C "$REPO" fetch -q origin "pull/$n/head" || continue
    check pr "$n" "$sha"
  done <<<"$prs"
}

log "orb-ci started: $SLUG, worktree $WT, every ${INTERVAL}s"
while true; do
  pass
  [[ "${1:-}" == --once ]] && break
  sleep "$INTERVAL"
done
