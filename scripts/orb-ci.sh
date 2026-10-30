#!/usr/bin/env bash
# Fallback CI without GitHub Actions (#50): checks new heads of `main` and of open, non-draft PRs into `main` in an
# orb, as ci.yml would, and records each result in the table of issue $ORB_CI_ISSUE (default 63); a failure is also a
# comment (#17 for main, the PR for a PR), and a PR's result is commented on the PR. (The agent token cannot post
# commit statuses or check runs: HTTP 403.) Run it as a supervised service so it survives restarts and pauses:
#   amp orb service start orb-ci --command 'bash <checkout>/scripts/orb-ci.sh'
# Re-check commits of main on request: append their SHAs to $ORB_CI_HOME/queue (one per line).
# It copies itself to $ORB_CI_HOME and runs the copy, checks out each head (a PR merged into main first, like
# GitHub's merge commit) in its own worktree ($ORB_CI_HOME/wt for main, wt-pr for PRs) with hard-linked Lake
# packages, removes the build outputs of modules whose source is not in the tree (prune_build), and keeps logs in
# $ORB_CI_HOME/logs. Options: --once (one pass, then exit); --full nightly|tag|now (the full tier, below).
# Environment: ORB_CI_HOME (default ~/orb-ci),
# ORB_CI_INTERVAL (seconds between passes, default 600), ORB_CI_REPO (the checkout it was started from),
# ORB_CI_SIGN (the comments' sign-off), ORB_CI_JOB (the shared box: `job` options and scope, e.g.
# '--mem 16G --cpus 8 consensus-lean'; each check.sh run is then a box `job`, waited for; unset in an orb).
# Mode as in ci.yml: docs-only change -> `check.sh --changed <base>`; otherwise `--fast`, with `--selftests` when
# scripts/ or the build configuration changed and `--canary` when the build configuration changed; then
# scripts/review-boundary.sh <base> and a clean-tree check. <base>: the previously checked main head (if an
# ancestor), or a PR's main.
# Full tier (as full.yml, unsplit), one run and exit, in its own worktree $ORB_CI_HOME/wt-full, one at a time
# (a lock): `check.sh --full` on main's head, which fails if a step is skipped or the tree is left dirty; a row
# in the issue, and a #17 comment on failure. `--full nightly`: unless that head already passed a full run;
# `--full poll` (cheap, every minute, no lock): appends the tag spec-approved's commit to $ORB_CI_HOME/tags-seen
# when it changed, so a tag that moves twice between full runs is still seen. `--full tag`: one run per commit in
# tags-seen not yet in full-tags (handled): on that commit itself once it is on main, else (a PR head merged as
# another commit) on the newest commit of main whose trusted files equal the tag's; pending until then
# (full-tags-pending), dropped after a day; a row on the issue either way ("PASSED earlier" when that commit
# already passed). `--full now`: main's head, always; `--full sha <commit> [<ref>]`: that commit.
# ORB_CI_FULL_ENV: extra environment for check.sh --full (e.g. 'REPLAY_JOBS=5').
set -uo pipefail
HOME_DIR="${ORB_CI_HOME:-$HOME/orb-ci}"
if [[ "${1:-} ${2:-}" == "--full poll" ]]; then  # before the copy and gh: runs every minute
  c="$(git -C "${ORB_CI_REPO:?}" ls-remote origin 'refs/tags/spec-approved^{}' | cut -f1)"
  [[ -n "$c" ]] || c="$(git -C "$ORB_CI_REPO" ls-remote origin refs/tags/spec-approved | cut -f1)"  # not annotated
  [[ -z "$c" ]] || [[ "$(tail -n 1 "$HOME_DIR/tags-seen" 2>/dev/null | cut -d' ' -f1)" == "$c" ]] ||
    echo "$c $(date +%s)" >>"$HOME_DIR/tags-seen"
  exit 0
fi
if [[ "${ORB_CI_COPY:-}" != 1 ]]; then  # run from a copy: the checkout may change under a running script
  mkdir -p "$HOME_DIR"
  cp "${BASH_SOURCE[0]}" "$HOME_DIR/orb-ci.sh"
  ORB_CI_REPO="${ORB_CI_REPO:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}" ORB_CI_COPY=1 exec bash "$HOME_DIR/orb-ci.sh" "$@"
fi
REPO="$ORB_CI_REPO" WT="$HOME_DIR/wt" WT_PR="$HOME_DIR/wt-pr" LOGS="$HOME_DIR/logs" DONE="$HOME_DIR/done" ISSUE="${ORB_CI_ISSUE:-63}"
INTERVAL="${ORB_CI_INTERVAL:-600}" FULL_DONE="$HOME_DIR/done-full"
[[ "${1:-}" != --full ]] || WT="$HOME_DIR/wt-full"
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
  trap 'systemctl --user stop "$unit"; exit 143' TERM INT  # stopping this process stops its job
  while systemctl --user -q is-active "$unit"; do sleep 10; done
  trap - TERM INT
  st="/srv/status/$(id -un).$unit.json"
  read -r run rc < <(python3 -I -c 'import json, sys; s = json.load(open(sys.argv[1]))
print(s.get("run_dir") or "-", s.get("exit", 1))' "$st" 2>/dev/null) || { echo "orb-ci: no status $st"; return 1; }
  echo "orb-ci: job $unit, run folder $run, exit $rc"
  cat "$run/out.log"
  return "$rc"
}

setup_worktree() {  # setup_worktree <dir>
  [[ -d "$1" ]] && return 0
  git -C "$REPO" worktree add -q --detach "$1" origin/main || return 1
  mkdir -p "$1/.lake" && cp -al "$REPO/.lake/packages" "$1/.lake/packages" &&
    { [[ ! -d "$REPO/.lake/build" ]] || cp -a "$REPO/.lake/build" "$1/.lake/build"; }
}

# In the checked-out tree: remove the build outputs (.lake/build/lib/lean/X.*, .lake/build/ir/X.*) of every module X
# whose source X.lean is in none of the lakefile's source dirs, i.e. a module of a ref checked here before. A kept
# .lake/build would otherwise let steps read its stale .oleans, and step 5 refuse a leaf with orphan descendants.
prune_build() {
  python3 -I -c 'import glob, os, tomllib
try:
    lake = tomllib.load(open("lakefile.toml", "rb"))
except OSError:
    raise SystemExit("orb-ci: no lakefile.toml, build outputs not pruned")
dirs = {"."} | {t.get("srcDir", ".") for k in ("lean_lib", "lean_exe") for t in lake.get(k, [])}
lib, ir, gone = ".lake/build/lib/lean", ".lake/build/ir", []
for o in glob.glob(f"{lib}/**/*.olean", recursive=True):
    m = os.path.relpath(o, lib)[:-len(".olean")]
    if not any(os.path.isfile(os.path.join(d, m + ".lean")) for d in dirs):
        gone.append(m.replace("/", "."))
        for f in glob.glob(glob.escape(f"{lib}/{m}") + ".*") + glob.glob(glob.escape(f"{ir}/{m}") + ".*"):
            os.remove(f)
for root in (lib, ir):  # directories left empty
    for d, _, _ in sorted(os.walk(root), key=lambda w: -len(w[0])):
        if d != root and not os.listdir(d):
            os.rmdir(d)
if gone:
    print(f"orb-ci: removed the build outputs of {len(gone)} modules without a source here:", *sorted(gone)[:20])'
}

record() {  # record <ref> <sha> <mode> <result>: a row at the top of the issue's table (the last 40 kept)
  local body row
  row="| $(date -u '+%m-%d %H:%M') | $1 | \`${2:0:8}\` | $3 | $4 |"
  exec 8>"$HOME_DIR/issue.lock"; flock 8  # the full tier and the watcher both edit the table
  body="$(gh issue view "$ISSUE" -R "$SLUG" --json body -q .body)" || { log "cannot read issue $ISSUE"; exec 8>&-; return; }
  body="$(ROW="$row" python3 -c 'import os, sys
b = sys.stdin.read(); head, rest = b.split("|---|---|---|---|---|\n", 1); rows, tail = rest.split("<!-- /orb-ci results -->", 1)
rows = [r for r in rows.splitlines() if r.startswith("|")][:39]
print(head + "|---|---|---|---|---|\n" + "\n".join([os.environ["ROW"]] + rows) + "\n<!-- /orb-ci results -->" + tail, end="")' <<<"$body")" &&
    gh issue edit "$ISSUE" -R "$SLUG" --body "$body" >/dev/null || log "cannot update issue $ISSUE"
  exec 8>&-
}

# check <kind> <id> <head>: kind main|pr; records the result in the issue and comments.
check() {
  local kind="$1" id="$2" head="$3" base flags=() mode=fast paths rc=0 t0=$SECONDS lg="$LOGS/$3.log" fails summary
  if [[ "$kind" == pr ]]; then cd "$WT_PR" || return 1; else cd "$WT" || return 1; fi
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
    prune_build
    if [[ "$mode" == changed ]]; then
      in_ci scripts/check.sh --changed "$base" || rc=1
    else
      in_ci scripts/check.sh --fast "${flags[@]}" || rc=1
    fi
    echo "--- review boundary ---"; scripts/review-boundary.sh "$base" || { echo "orb-ci FAIL: review boundary"; rc=1; }
    [[ -z "$(git status --porcelain)" ]] || { echo "orb-ci FAIL: tree not clean"; git status --porcelain; rc=1; }
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
    fails="$(grep -E '^(FAIL|orb-ci FAIL|::error)' "$lg" | head -20)" summary="$(fail_summary "$lg")"
    record "$ref" "$head" "$what" "**FAILED** in ${secs}s: $summary"
    body="**orb-ci: FAILED** on \`${head:0:8}\` ($ref): $summary. \`check.sh $what\`, ${secs}s. Fallback CI while Actions is down (#50, results: #$ISSUE).

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
  { setup_worktree "$WT" && setup_worktree "$WT_PR"; } || { log "worktree setup failed"; return; }
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

# fail_summary <log>: the failed checks, for a FAILED row and comment ("step 1 build, review boundary"): each
# `FAIL  <n> <label> (...)` line of check.sh as "step <n> <label>", then each `orb-ci FAIL: <what>` line of this
# script; at most about 120 characters.
fail_summary() {
  local s
  s="$(grep -E '^(FAIL  [0-9]|orb-ci FAIL: )' "$1" | sed -E 's/^FAIL  /step /; s/^orb-ci FAIL: //; s/ \(.*//' |
    awk 'NF && !seen[$0]++' | paste -sd ';' | sed 's/;/, /g')"
  ((${#s} <= 120)) || s="${s:0:117}..."
  echo "${s:-no FAIL line}"
}

# full_check <kind> <ref> <head>: the full tier on <head> (a commit of main), recorded as <ref>.
full_check() {
  local kind="$1" ref="$2" head="$3" rc=0 t0=$SECONDS lg="$LOGS/$3.full-$(date -u +%m%d-%H%M).log" fenv skipped body summary
  cd "$WT" && git checkout -q --detach -f "$head" && git clean -qfdx -e .lake || return 1
  read -ra fenv <<<"${ORB_CI_FULL_ENV:-}"
  {
    echo "orb-ci: $ref at $head, mode full ${fenv[*]}"
    prune_build
    in_ci env "${fenv[@]}" scripts/check.sh --full || rc=1
  } >>"$lg" 2>&1
  # as full.yml: nothing skipped (no sandbox step left out), tree clean
  skipped="$(grep -E 'skipped: no bwrap|^SKIP ' "$lg")"
  { [[ -z "$skipped" ]] || { echo "orb-ci FAIL: steps skipped"; echo "$skipped"; rc=1; }
    [[ -z "$(git status --porcelain)" ]] || { echo "orb-ci FAIL: tree not clean"; git status --porcelain; rc=1; }
  } >>"$lg" 2>&1
  local secs=$((SECONDS - t0))
  if ((rc == 0)); then record "$ref" "$head" "--full" "PASSED in ${secs}s"
  else
    summary="$(fail_summary "$lg")"
    record "$ref" "$head" "--full" "**FAILED** in ${secs}s: $summary"
    body="**orb-ci: FAILED** on \`${head:0:8}\` ($ref): $summary. \`check.sh --full\`, ${secs}s. Fallback CI while Actions is down (#50, results: #$ISSUE).

\`\`\`
$(grep -E '^(FAIL|orb-ci FAIL|::error)' "$lg" | head -20 || true)
\`\`\`
(log: $lg)
$SIGN"
    gh issue comment 17 -R "$SLUG" --body "$body" >/dev/null || log "cannot comment on #17"
  fi
  echo "$head $kind $rc $secs" >>"$FULL_DONE"
  log "full $kind ${head:0:8}: rc=$rc ${secs}s"
}

trusted_same() {  # trusted_same <a> <b>: the trusted files (the lists at both commits, united) are equal at a and b
  local p=()
  mapfile -t p < <(for r in "$1" "$2"; do git -C "$REPO" show "$r:scripts/boundaries.toml" 2>/dev/null |
    python3 -I -c 'import sys, tomllib
print("\n".join(tomllib.loads(sys.stdin.read()).get("checks", {}).get("trusted_paths", [])))' 2>/dev/null; done | sort -u)
  ((${#p[@]})) && GIT_LITERAL_PATHSPECS=1 git -C "$REPO" diff --quiet "$1" "$2" -- "${p[@]}"
}

tag_target() {  # tag_target <tag commit>: the commit of main to check for it; nothing while main does not hold it
  local c
  if git -C "$REPO" merge-base --is-ancestor "$1" origin/main 2>/dev/null; then echo "$1"; return; fi
  for c in $(git -C "$REPO" rev-list --first-parent -n 100 origin/main); do  # newest first
    trusted_same "$1" "$c" && { echo "$c"; return; }
  done
}

full_pass() {  # full_pass nightly|tag|now|sha <commit> [<ref>]
  exec 9>"$HOME_DIR/full.lock"
  if [[ "$1" == tag ]]; then flock -n 9 || return 0; else flock 9; fi  # one full run at a time
  touch "$FULL_DONE" "$HOME_DIR/full-tags" "$HOME_DIR/tags-seen"
  git -C "$REPO" fetch -q --tags --force origin main || { log "fetch failed"; return 1; }
  setup_worktree "$WT" || { log "worktree setup failed"; return 1; }
  local head tag
  head="$(git -C "$REPO" rev-parse origin/main)"
  case "$1" in
    nightly)
      if grep -q "^$head [a-z]* 0 " "$FULL_DONE"; then log "full: ${head:0:8} already passed"
      else full_check nightly "main (full)" "$head"; fi ;;
    now) full_check now "main (full, manual)" "$head" ;;
    sha)
      head="$(git -C "$REPO" rev-parse -q --verify "${2:-}^{commit}")" || { log "full: no commit '${2:-}'"; return 2; }
      full_check now "${3:-main (full, ${head:0:8})}" "$head" ;;
    tag)  # until a pass handles nothing: tags-seen grows while a run goes on
      local t at tgt again=1
      while ((again)); do
        again=0; : >"$HOME_DIR/full-tags-pending"
        git -C "$REPO" fetch -q --tags --force origin main || { log "fetch failed"; return 1; }
        while read -r t at; do
          [[ -n "$t" ]] && ! grep -qx "$t" "$HOME_DIR/full-tags" || continue
          git -C "$REPO" cat-file -e "$t^{commit}" 2>/dev/null || git -C "$REPO" fetch -q origin "$t" 2>/dev/null
          tgt="$(tag_target "$t")"
          if [[ -z "$tgt" ]]; then
            if (($(date +%s) - ${at:-0} > 86400)); then log "full: spec-approved ${t:0:8} never reached main; dropped"
              echo "$t" >>"$HOME_DIR/full-tags"
            else echo "$t $at" >>"$HOME_DIR/full-tags-pending"; fi
            continue
          fi
          if grep -q "^$tgt [a-z]* 0 " "$FULL_DONE"; then
            record "main (full, tag ${t:0:8})" "$tgt" "--full" "PASSED earlier on this commit"
          else full_check tag "main (full, tag ${t:0:8})" "$tgt" || continue; fi
          echo "$t" >>"$HOME_DIR/full-tags"; again=1
        done <"$HOME_DIR/tags-seen"
      done ;;
    *) log "usage: orb-ci.sh --full nightly|tag|now|poll|sha <commit> [<ref>]"; return 2 ;;
  esac
}

if [[ "${1:-}" == --full ]]; then full_pass "${@:2}"; exit; fi
log "orb-ci started: $SLUG, worktree $WT, every ${INTERVAL}s"
while true; do
  pass
  [[ "${1:-}" == --once ]] && break
  sleep "$INTERVAL"
done
