#!/usr/bin/env bash
# User-unit ExecStartPre: refresh a compatible cached watcher/publisher pair.
# A failed fetch/extraction leaves the previous pair untouched. No service control.
set -euo pipefail
home="${ORB_CI_HOME:?}" repo="${ORB_CI_REPO:?}"
mkdir -p "$home"
exec 9>"$home/refresh.lock"; flock 9
git -C "$repo" fetch -q origin main
sha="$(git -C "$repo" rev-parse origin/main)"
stage="$(mktemp -d "$home/refresh.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
git -C "$repo" show "$sha:scripts/orb-ci.sh" >"$stage/orb-ci.sh"
git -C "$repo" show "$sha:scripts/publish-inventory.py" >"$stage/publish-inventory.py"
bash -n "$stage/orb-ci.sh"
python3 -I -c 'import pathlib,sys; compile(pathlib.Path(sys.argv[1]).read_bytes(), sys.argv[1], "exec")' "$stage/publish-inventory.py"
# Full/poll never call the publisher. The previous watcher ignores it; the new
# watcher uses this same CLI contract. Helper-first promotion is compatible.
mv "$stage/publish-inventory.py" "$home/publish-inventory.py"
mv "$stage/orb-ci.sh" "$home/orb-ci.sh"
echo "orb-ci cached pair: $sha"
