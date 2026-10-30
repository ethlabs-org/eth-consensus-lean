#!/usr/bin/env bash
# Review boundary (steps of ci.yml's `check` job; docs/spec-review.md): the trusted surface against the tag
# `spec-approved`. Run in the repository, on the commit to check (HEAD):
#   scripts/review-boundary.sh [<base>]   check HEAD; <base> is the commit the change starts from (a PR's base,
#                                         the commit a push to main replaced), if any
#   scripts/review-boundary.sh --self-test   the verdicts on throwaway repositories (fixtures below)
# The trusted paths are `[checks] trusted_paths` of scripts/boundaries.toml at HEAD, at the tag and at <base>
# (united, so a change cannot drop a path from the check by editing the list); literal paths only.
#   - No tag: pass with a warning (nothing approved yet).
#   - <base> usable (a commit that is an ancestor of HEAD) and the change <base>..HEAD touches no trusted path:
#     pass. Such a change cannot alter the trusted files it lands on, so a tag that is briefly ahead of main (moved
#     to a PR's head just before its merge) does not turn unrelated changes red. If main's trusted files differ
#     from the tag meanwhile, that is reported as a warning.
#   - Otherwise: the trusted files at HEAD must equal those at the tag (fail if not).
# Exit 0 = pass, 1 = fail.
set -euo pipefail
export GIT_LITERAL_PATHSPECS=1
TAG='refs/tags/spec-approved^{commit}'

paths_at() {  # paths_at <rev>: the list in <rev>'s boundaries.toml, one per line (nothing if absent)
  git show "$1:scripts/boundaries.toml" 2>/dev/null | python3 -I -c 'import sys, tomllib
print("\n".join(tomllib.loads(sys.stdin.read()).get("checks", {}).get("trusted_paths", [])))' 2>/dev/null || true
}
err() { echo "::error::$*"; }

check() {
  local base="${1:-}" have_tag=0 use_base=0 p protected=()
  git rev-parse -q --verify "$TAG" >/dev/null && have_tag=1
  if [[ -n "$base" && ! "$base" =~ ^0+$ ]] && git cat-file -e "$base^{commit}" 2>/dev/null &&
     git merge-base --is-ancestor "$base" HEAD 2>/dev/null; then
    use_base=1
  fi
  if [[ -z "$(paths_at HEAD)" ]]; then
    err "scripts/boundaries.toml at HEAD has no [checks] trusted_paths"; return 1
  fi
  mapfile -t protected < <({ paths_at HEAD; ((!have_tag)) || paths_at "$TAG"; ((!use_base)) || paths_at "$base"; } |
    awk NF | LC_ALL=C sort -u)
  for p in "${protected[@]}"; do
    [[ "$p" =~ ^[A-Za-z0-9_][A-Za-z0-9_.-]*(/[A-Za-z0-9_][A-Za-z0-9_.-]*)*$ && "/$p/" != */../* ]] ||
      { err "trusted_paths entry '$p' is not a plain relative path"; return 1; }
  done
  echo "trusted paths: ${protected[*]}"
  if ((!have_tag)); then
    echo "::warning title=Review boundary: not yet approved::no tag spec-approved: the trusted surface is not yet approved (non-blocking until the tag exists; see docs/spec-review.md)"
    return 0
  fi
  local tag_short
  tag_short="$(git rev-parse --short "$TAG")"
  if ((use_base)); then
    if git diff --quiet "$base" HEAD -- "${protected[@]}"; then
      echo "the change $(git rev-parse --short "$base")..$(git rev-parse --short HEAD) touches no trusted path: pass"
      if ! git diff --quiet "$TAG" HEAD -- "${protected[@]}"; then
        echo "::warning title=Review boundary: tag and main differ::the trusted files here differ from spec-approved ($tag_short), which this change does not touch: the tag is ahead of main (a PR about to merge) or main took a trusted change the tag does not cover (docs/spec-review.md)"
      fi
      return 0
    fi
    echo "the change touches trusted paths:"
    git diff --stat "$base" HEAD -- "${protected[@]}"
  else
    echo "no usable base: the whole trusted surface is compared with the tag"
  fi
  if ! git diff --quiet "$TAG" HEAD -- "${protected[@]}"; then
    err "trusted surface differs from spec-approved ($tag_short): awaiting approval (an agent other than the author moves the tag to this PR head; docs/spec-review.md)"
    git diff --stat "$TAG" HEAD -- "${protected[@]}"
    return 1
  fi
  echo "trusted surface equals spec-approved ($tag_short)"
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
    out="$(bash "$script" $base 2>&1)" || rc=$?
    if { [[ "$want" == pass ]] && ((rc == 0)); } || { [[ "$want" == fail ]] && ((rc == 1)); }; then
      echo "  ok ($want): $label"
    else
      echo "  WRONG (expected $want, exit $rc): $label"; sed 's/^/    /' <<<"$out"; fails=1
    fi
  }
  toml '"Spec", "Challenge.lean"'; mkdir -p Spec Proofs; echo a >Spec/A.lean; echo p >Proofs/P.lean; echo c >Challenge.lean
  local m0 pr_other ahead pr_spec pr_drop pr_glob pr_nolist side
  m0="$(commit main0)"
  expect pass "no tag yet (warning)" "$m0" "$m0"
  git tag -a -m t spec-approved "$m0"
  echo p2 >Proofs/P.lean; pr_other="$(commit 'PR: proofs only')"
  expect pass "tag = main, a change outside the trusted paths" "$pr_other" "$m0"
  git checkout -q --detach "$m0"; echo a2 >Spec/A.lean; ahead="$(commit 'unmerged PR: Spec')"
  git tag -f -a -m t spec-approved "$ahead" >/dev/null
  expect pass "tag ahead of main (unmerged PR head), a change outside the trusted paths" "$pr_other" "$m0"
  expect fail "tag ahead of main, no base: whole surface compared" "$pr_other"
  expect pass "the tagged PR itself" "$ahead" "$m0"
  git checkout -q --detach "$m0"; echo a3 >Spec/A.lean; pr_spec="$(commit 'PR: Spec, not approved')"
  expect fail "a Spec change the tag does not cover" "$pr_spec" "$m0"
  git checkout -q --detach "$m0"; echo c2 >Challenge.lean; side="$(commit 'PR: a single trusted file')"
  expect fail "a change of a trusted file (not a directory)" "$side" "$m0"
  git tag -f -a -m t spec-approved "$m0" >/dev/null
  git checkout -q --detach "$m0"; toml '"Challenge.lean"'; echo a4 >Spec/A.lean; pr_drop="$(commit 'PR: drops Spec from the list, edits it')"
  expect fail "a change that drops a path from trusted_paths and edits it" "$pr_drop" "$m0"
  git checkout -q --detach "$m0"; toml '"Spec/*"'; pr_glob="$(commit 'PR: glob entry')"
  expect fail "a glob in trusted_paths" "$pr_glob" "$m0"
  git checkout -q --detach "$m0"; rm scripts/boundaries.toml; pr_nolist="$(commit 'PR: no list')"
  expect fail "no trusted_paths at HEAD" "$pr_nolist" "$m0"
  git checkout -q --detach "$m0"; git tag -f -a -m t spec-approved "$ahead" >/dev/null
  expect fail "a base that is not an ancestor of HEAD: whole surface compared" "$pr_other" "$ahead"
  expect fail "an all-zero base (new branch push): whole surface compared" "$pr_other" "0000000000000000000000000000000000000000"
  return "$fails"
}

if [[ "${1:-}" == --self-test ]]; then
  self_test && echo "review-boundary self-test: all verdicts as expected" || { echo "review-boundary self-test: FAILED"; exit 1; }
else
  check "${1:-}"
fi
