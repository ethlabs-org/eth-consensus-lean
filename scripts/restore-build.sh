#!/usr/bin/env bash
# Restore the project build (.lake/build) from CI: the `lake-build` artifact of the newest green `check` run on
# main whose commit is an ancestor of HEAD (or HEAD itself). Lake then rebuilds only what changed since that
# commit, instead of nearly everything after a Spec change. Called by .agents/setup before its prebuild; also
# usable by hand in any clone. A speedup only: Lake still checks every restored module against its trace, so an
# output whose inputs changed is rebuilt; one whose trace matches is used as is, which is why only green main push
# runs are restored. The archive is unpacked next to .lake/build and swapped in by a rename only when complete, so
# an interrupted download or unpack leaves the previous build (or none), never a half-restored one.
#
# Needs `gh` authenticated for the code repository (scripts/repos.toml; the Actions API needs a token even for a
# public repository) and zstd. Without them, or without a matching artifact (artifacts expire after a few days;
# docs-only pushes upload none), it says why and exits 0: the build then runs from scratch as before.
#
# Usage: scripts/restore-build.sh [--force]   (--force: restore even when .lake/build is already up to date)
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

skip() { echo "restore-build: $*; nothing restored"; exit 0; }
force=0
[[ "${1:-}" == --force ]] && force=1

command -v gh >/dev/null || skip "gh not installed"
command -v zstd >/dev/null || skip "zstd not installed"
gh auth status >/dev/null 2>&1 || skip "gh is not authenticated"
repo="$(python3 -I -c 'import tomllib; print(tomllib.load(open("scripts/repos.toml", "rb"))["code"])')"
head="$(git rev-parse HEAD)"

if ((!force)) && [[ -d .lake/build ]] &&
   lake build --no-build ConsensusLean >/dev/null 2>&1; then
  skip ".lake/build is up to date for ConsensusLean"
fi

# Is commit $1 HEAD or an ancestor of it? Ask GitHub (works in a shallow clone), else local history.
is_ancestor() {
  local status
  status="$(gh api "repos/$repo/compare/$1...$head" -q .status 2>/dev/null)" || status=""
  case "$status" in
    identical|ahead) return 0 ;;
    behind|diverged) return 1 ;;
  esac
  git merge-base --is-ancestor "$1" "$head" 2>/dev/null
}

found=""
while read -r id sha; do
  [[ -n "$id" ]] || continue
  is_ancestor "$sha" || continue
  if gh api "repos/$repo/actions/runs/$id/artifacts" \
       -q '.artifacts[] | select(.name == "lake-build" and (.expired | not)) | .name' | grep -qx lake-build; then
    found="$id $sha"; break
  fi
done < <(gh api "repos/$repo/actions/workflows/ci.yml/runs?branch=main&event=push&status=success&per_page=30" \
           -q '.workflow_runs[] | "\(.id) \(.head_sha)"' 2>/dev/null || true)
[[ -n "$found" ]] || skip "no lake-build artifact of a green main run at or below HEAD ${head:0:8}"

read -r id sha <<<"$found"
mkdir -p .lake
# Inside .lake, so the final mv is a rename on the same file system.
tmp="$(mktemp -d .lake/restore-build.XXXXXX)"
trap 'rm -rf "$tmp"' EXIT
echo "restore-build: run $id, commit ${sha:0:8} (HEAD ${head:0:8})"
gh run download "$id" -R "$repo" -n lake-build -D "$tmp"
zstd -dc "$tmp/lake-build.tar.zst" | tar -C "$tmp" -xf -
[[ -d "$tmp/build" ]] || skip "the artifact has no build/ directory"
rm -rf .lake/build && mv "$tmp/build" .lake/
echo "restore-build: restored .lake/build from ${sha:0:8}; lake build now rebuilds only what changed since"
