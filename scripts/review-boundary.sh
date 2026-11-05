#!/usr/bin/env bash
# Review boundary (a step of ci.yml's `check` job and of push-main.sh): a record of trusted-surface changes, not an
# approval gate. Run in the repository, on the commit to check (HEAD):
#   scripts/review-boundary.sh [<base>]   check HEAD; <base> is the commit the change starts from (a PR's base,
#                                         the commit a push to main replaced), if any
#   scripts/review-boundary.sh --self-test   the verdicts on throwaway repositories (fixtures below)
# The trusted paths are `[checks] trusted_paths` of scripts/boundaries.toml at HEAD and at <base> (united, so a change
# cannot drop a path from the record by editing the list); literal paths only.
#   - <base> not usable (absent, all-zero, or not an ancestor of HEAD): pass; nothing to compare.
#   - The change <base>..HEAD touches no trusted path: pass.
#   - Otherwise it prints the trusted files changed, and every non-merge commit of <base>..HEAD that touches a trusted
#     path must carry a trailer line `Trusted-surface: <what changes and why>` (fail if one does not), so that
#     `git log --grep='^Trusted-surface:'` lists every such change.
# With GITHUB_STEP_SUMMARY set (GitHub Actions), it also appends the per-commit record to the run's summary: for each
# commit of <base>..HEAD that touches a trusted path, the paths it touches and its Trusted-surface line, then the
# verdict. So the `check` run of every push and pull request shows which trusted paths each commit changed.
# Exit 0 = pass, 1 = fail.
set -euo pipefail
export GIT_LITERAL_PATHSPECS=1

paths_at() {  # paths_at <rev>: the list in <rev>'s boundaries.toml, one per line (nothing if absent)
  git show "$1:scripts/boundaries.toml" 2>/dev/null | python3 -I -c 'import sys, tomllib
print("\n".join(tomllib.loads(sys.stdin.read()).get("checks", {}).get("trusted_paths", [])))' 2>/dev/null || true
}
err() { echo "::error::$*"; }
summary() { [[ -z "${GITHUB_STEP_SUMMARY:-}" ]] || printf '%s\n' "$@" >>"$GITHUB_STEP_SUMMARY"; }
cell() { sed 's/|/\\|/g' <<<"$1"; }  # a Markdown table cell
label_of() {  # label_of <commit>: the text of its Trusted-surface line (the line the check requires), or nothing
  git log -1 --format=%B "$1" | grep -m1 -E '^Trusted-surface: *[^ ]' | sed -E 's/^Trusted-surface: *//' || true
}
record() {  # record <commit...>: the summary table, one row per commit touching a trusted path
  local c paths label
  summary "| Commit | Subject | Trusted paths touched | Trusted-surface line |" "| --- | --- | --- | --- |"
  for c in "$@"; do
    paths="$(git show --format= --name-only "$c" -- "${protected[@]}" | sed 's/.*/`&`/' | paste -sd ' ' -)"
    label="$(label_of "$c")"
    summary "| \`$(git rev-parse --short "$c")\` | $(cell "$(git log -1 --format=%s "$c")") | $paths | $(cell "${label:-(none)}") |"
  done
}

check() {
  local base="${1:-}" use_base=0 p c protected=() unlabeled=() touching=()
  if [[ -n "$base" && ! "$base" =~ ^0+$ ]] && git cat-file -e "$base^{commit}" 2>/dev/null &&
     git merge-base --is-ancestor "$base" HEAD 2>/dev/null; then
    use_base=1
  fi
  if [[ -z "$(paths_at HEAD)" ]]; then
    err "scripts/boundaries.toml at HEAD has no [checks] trusted_paths"; return 1
  fi
  mapfile -t protected < <({ paths_at HEAD; ((!use_base)) || paths_at "$base"; } | awk NF | LC_ALL=C sort -u)
  for p in "${protected[@]}"; do
    [[ "$p" =~ ^[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*)*$ && "/$p/" != */../* ]] ||
      { err "trusted_paths entry '$p' is not a plain relative path"; return 1; }
  done
  echo "trusted paths: ${protected[*]}"
  summary "### Trusted surface (review boundary)" ""
  if ((!use_base)); then
    echo "no usable base: nothing to compare (pass)"
    summary "No usable base: nothing compared (pass)."; return 0
  fi
  local range
  range="$(git rev-parse --short "$base")..$(git rev-parse --short HEAD)"
  if git diff --quiet "$base" HEAD -- "${protected[@]}"; then
    echo "the change $range touches no trusted path: pass"
    summary "The change \`$range\` touches no trusted path (pass)."; return 0
  fi
  echo "the change $range touches trusted paths (recorded, not gated):"
  git diff --stat "$base" HEAD -- "${protected[@]}"
  mapfile -t touching < <(git rev-list --reverse --no-merges --full-history "$base..HEAD" -- "${protected[@]}")
  for c in "${touching[@]}"; do
    [[ -n "$(label_of "$c")" ]] || unlabeled+=("$c")
  done
  summary "The change \`$range\` touches trusted paths in ${#touching[@]} commit(s):" ""
  record "${touching[@]}"
  summary ""
  if ((${#unlabeled[@]})); then
    for c in "${unlabeled[@]}"; do
      err "commit $(git log -1 --format='%h %s' "$c") touches the trusted surface without a 'Trusted-surface: <what and why>' line in its message"
    done
    summary "**FAIL:** ${#unlabeled[@]} commit(s) without a Trusted-surface line."
    return 1
  fi
  echo "every commit touching it carries a Trusted-surface line: pass"
  summary "Every commit touching it carries a Trusted-surface line (pass)."
}

# --- self-test: verdicts on throwaway repositories ------------------------------------------------
self_test() {
  local script tmp fails=0
  script="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)/$(basename "${BASH_SOURCE[0]}")"
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' RETURN
  cd "$tmp"
  git init -q -b main . && git config user.email t@t && git config user.name t && git config commit.gpgsign false
  toml() { mkdir -p scripts; printf '[checks]\ntrusted_paths = [%s]\n' "$1" >scripts/boundaries.toml; }
  commit() { git add -A && git commit -q -m "$1" && git rev-parse HEAD; }
  expect() {  # expect <pass|fail> <label> <head> [<base>]
    local want="$1" label="$2" head="$3" base="${4:-}" rc=0 out
    git checkout -q --detach "$head"
    out="$(GITHUB_STEP_SUMMARY='' bash "$script" $base 2>&1)" || rc=$?
    if { [[ "$want" == pass ]] && ((rc == 0)); } || { [[ "$want" == fail ]] && ((rc == 1)); }; then
      echo "  ok ($want): $label"
    else
      echo "  WRONG (expected $want, exit $rc): $label"; sed 's/^/    /' <<<"$out"; fails=1
    fi
  }
  local L=$'\n\nTrusted-surface: test change'
  toml '"Spec", "Challenge.lean"'; mkdir -p Spec Proofs; echo a >Spec/A.lean; echo p >Proofs/P.lean; echo c >Challenge.lean
  local m0 other spec spec_l file_l two mixed drop drop_l glob nolist merged
  m0="$(commit main0)"
  echo p2 >Proofs/P.lean; other="$(commit 'proofs only')"
  expect pass "a change outside the trusted paths" "$other" "$m0"
  git checkout -q --detach "$m0"; echo a2 >Spec/A.lean; spec="$(commit 'Spec, unlabeled')"
  expect fail "an unlabeled Spec change" "$spec" "$m0"
  expect pass "an unlabeled Spec change, no base" "$spec"
  expect pass "an unlabeled Spec change, all-zero base (new branch push)" "$spec" "0000000000000000000000000000000000000000"
  git checkout -q --detach "$m0"; echo a3 >Spec/A.lean; spec_l="$(commit "Spec, labeled$L")"
  expect pass "a labeled Spec change" "$spec_l" "$m0"
  git checkout -q --detach "$m0"; echo c2 >Challenge.lean; file_l="$(commit "Challenge.lean, labeled$L")"
  expect pass "a labeled change of a trusted file (not a directory)" "$file_l" "$m0"
  git checkout -q --detach "$m0"; echo c3 >Challenge.lean; commit 'Challenge.lean, unlabeled' >/dev/null
  expect fail "an unlabeled change of a trusted file" HEAD "$m0"
  git checkout -q --detach "$spec_l"; echo p3 >Proofs/P.lean; mixed="$(commit 'proofs on top, unlabeled')"
  expect pass "a labeled trusted commit followed by an unlabeled untrusted one" "$mixed" "$m0"
  git checkout -q --detach "$spec_l"; echo a4 >Spec/A.lean; two="$(commit 'Spec again, unlabeled')"
  expect fail "two trusted commits, the second unlabeled" "$two" "$m0"
  git checkout -q --detach "$m0"; echo trailer >Spec/A.lean; commit $'Spec\n\nnot a trailer: Trusted-surface: x' >/dev/null
  expect fail "a Trusted-surface mention that is not its own line" HEAD "$m0"
  git checkout -q --detach "$m0"; toml '"Challenge.lean"'; echo a5 >Spec/A.lean; drop="$(commit 'drops Spec from the list, edits it')"
  expect fail "an unlabeled change that drops a path from trusted_paths and edits it" "$drop" "$m0"
  git checkout -q --detach "$m0"; toml '"Challenge.lean"'; echo a6 >Spec/A.lean; drop_l="$(commit "drops Spec, labeled$L")"
  expect pass "the same change, labeled" "$drop_l" "$m0"
  git checkout -q --detach "$drop_l"; echo a7 >Spec/A.lean; commit 'Spec after it left the list, unlabeled' >/dev/null
  expect pass "an unlabeled change of a path that an earlier commit dropped from trusted_paths" HEAD "$drop_l"
  git checkout -q --detach "$drop_l"; echo c4 >Challenge.lean; commit 'Challenge.lean, still listed, unlabeled' >/dev/null
  expect fail "the control: an unlabeled change of a path still in trusted_paths" HEAD "$drop_l"
  git checkout -q --detach "$m0"; toml '"Spec/*"'; glob="$(commit 'glob entry')"
  expect fail "a glob in trusted_paths" "$glob" "$m0"
  git checkout -q --detach "$m0"; rm scripts/boundaries.toml; nolist="$(commit 'no list')"
  expect fail "no trusted_paths at HEAD" "$nolist" "$m0"
  git checkout -q --detach "$other"; git merge -q --no-ff --no-edit "$spec_l"; merged="$(git rev-parse HEAD)"
  expect pass "a merge (unlabeled merge commit) of a labeled trusted commit" "$merged" "$other"
  git checkout -q --detach "$other"; git merge -q --no-ff --no-edit "$spec"
  expect fail "a merge of an unlabeled trusted commit" HEAD "$other"
  expect pass "a base that is not an ancestor of HEAD: nothing to compare" "$spec" "$other"
  # The run summary (GITHUB_STEP_SUMMARY): one row per commit that touches a trusted path, with the paths it touches
  # and its Trusted-surface text; "!text" must be absent.
  expect_summary() {  # expect_summary <label> <head> <base> <text...>
    local label="$1" head="$2" base="$3" t ok=1 out
    shift 3
    out="$(mktemp)"  # outside the throwaway repository, so no commit picks it up
    git checkout -q --detach "$head"
    GITHUB_STEP_SUMMARY="$out" bash "$script" "$base" >/dev/null 2>&1 || true
    for t in "$@"; do
      if [[ "$t" == '!'* ]]; then ! grep -qF -- "${t#!}" "$out" || ok=0
      else grep -qF -- "$t" "$out" || ok=0; fi
    done
    if ((ok)); then echo "  ok (summary): $label"
    else echo "  WRONG (summary): $label"; sed 's/^/    /' "$out"; fails=1; fi
    rm -f "$out"
  }
  local both
  short() { git rev-parse --short "$1"; }
  expect_summary "a labeled Spec change: its row, its paths, its label, pass" "$spec_l" "$m0" \
    "| \`$(short "$spec_l")\` | Spec, labeled | \`Spec/A.lean\` | test change |" "1 commit(s)" "(pass)"
  expect_summary "an unlabeled Spec change: its row says (none), and the verdict fails" "$spec" "$m0" \
    "| \`$(short "$spec")\` | Spec, unlabeled | \`Spec/A.lean\` | (none) |" "**FAIL:** 1 commit(s)" "!(pass)"
  expect_summary "an untrusted commit on top of a labeled one gets no row" "$mixed" "$m0" \
    "| \`$(short "$spec_l")\` |" "!$(short "$mixed")\` |" "1 commit(s)"
  expect_summary "a change outside the trusted paths: no table" "$other" "$m0" "touches no trusted path (pass)" "!| Commit |"
  git checkout -q --detach "$m0"; echo a8 >Spec/A.lean; echo c5 >Challenge.lean
  both="$(commit "Spec | Challenge$L")"
  expect_summary "a commit touching two trusted paths lists both; a | in the subject is escaped" "$both" "$m0" \
    "| Spec \\| Challenge | \`Challenge.lean\` \`Spec/A.lean\` | test change |"
  # The repository's own list (docs/decisions.md §"Trusted surface and Challenge scope"): a Shape example and a Goldilocks milestone statement
  # (the Milestones layers) are not on the trusted surface; the Goldilocks instance Spec and the endpoint statement are.
  local real ex gold ms acc
  local G=ConsensusLean/Instances/Goldilocks
  git checkout -q --detach "$m0"; cp "$(dirname "$script")/boundaries.toml" scripts/boundaries.toml
  mkdir -p ConsensusLean/Examples/Shape $G/Spec $G/Milestones/Statements $G/Statements
  echo e >ConsensusLean/Examples/Shape/Streamlet.lean; echo g >$G/Spec/Frame.lean
  echo m >$G/Milestones/Statements/FGSafety.lean; echo a >$G/Statements/Obligations.lean
  real="$(commit "the repository's trusted_paths$L")"
  echo e2 >ConsensusLean/Examples/Shape/Streamlet.lean; ex="$(commit 'Shape example, unlabeled')"
  expect pass "repository list: an unlabeled change of a Shape example (Examples/Shape/Streamlet.lean)" "$ex" "$real"
  git checkout -q --detach "$real"; echo m2 >$G/Milestones/Statements/FGSafety.lean
  ms="$(commit 'Goldilocks milestone statement, unlabeled')"
  expect pass "repository list: an unlabeled change of a milestone statement (Milestones/Statements/FGSafety.lean)" \
    "$ms" "$real"
  git checkout -q --detach "$real"; echo g2 >$G/Spec/Frame.lean
  gold="$(commit 'Goldilocks Spec, unlabeled')"
  expect fail "repository list: an unlabeled change of the Goldilocks instance Spec" "$gold" "$real"
  git checkout -q --detach "$real"; echo a2 >$G/Statements/Obligations.lean
  acc="$(commit 'Goldilocks endpoint statement, unlabeled')"
  expect fail "repository list: an unlabeled change of the endpoint statement (Statements/Obligations)" \
    "$acc" "$real"
  return "$fails"
}

if [[ "${1:-}" == --self-test ]]; then
  self_test && echo "review-boundary self-test: all verdicts as expected" || { echo "review-boundary self-test: FAILED"; exit 1; }
else
  check "${1:-}"
fi
