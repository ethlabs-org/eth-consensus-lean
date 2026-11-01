#!/usr/bin/env bash
# Check docs/internal/PCSA-API.md against the code (V2Manifest --scope pcsa --check, D15),
# then (full tier) the write control and the negative controls on temp files.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
active=$(python3 -B scripts/unported.py AvailableChainPCSA)
if [ "$active" = '' ]; then
  echo 'SKIP UNPORTED: PC-SA manifest and controls'
  exit 0
fi
mkdir -p .lake
tmp=
trap 'rm -rf "$tmp"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
lake env lean --run scripts/V2Manifest.lean --scope pcsa --check
# NEG=0 skips controls when no checker path changed.
if [ "${NEG:-1}" != 1 ]; then echo "controls skipped (NEG=0)"; exit 0; fi
tmp=$(mktemp -d "$PWD/.lake/pcsa-manifest.XXXXXX")

# W: --write from code gives the entry sections of the committed doc byte for byte
# (from the first library heading; notes in the header may be written by hand).
lake env lean --run scripts/V2Manifest.lean --scope pcsa --write --manifest "$tmp/base.md"
entries() { sed -n '/^## `/,$p' "$1"; }
entries "$tmp/base.md" > "$tmp/base.entries"
entries docs/internal/PCSA-API.md > "$tmp/doc.entries"
[ -s "$tmp/base.entries" ] || { echo "CONTROL SETUP FAIL: no entry sections" >&2; exit 1; }
cmp "$tmp/base.entries" "$tmp/doc.entries" ||
  { echo "CONTROL W FAIL: --write differs from docs/internal/PCSA-API.md; write the doc again" >&2
    exit 1; }
echo "CONTROL W OK"

# Three different entries: drop the first, change the hash of the second, and add
# an unknown entry after the third.
# Bash 3.2 (Mac) has no mapfile.
read -r dropped changed after < <(awk '/^[a-z]+ [^ ]+ [0-9a-f]+$/ { printf "%s ", $2 }
  END { print "" }' "$tmp/base.md")
[ -n "${after:-}" ] || { echo "CONTROL SETUP FAIL: fewer than three entries" >&2; exit 1; }
after=${after%% *}
extra=${after}Control

expect() {  # expect <id> <rc> <manifest> <reason>...
  local id=$1 want=$2 manifest=$3 rc=0 reason
  shift 3
  lake env lean --run scripts/V2Manifest.lean --scope pcsa --check \
    --manifest "$manifest" > "$tmp/$id.log" 2>&1 || rc=$?
  if [ "$rc" -ne "$want" ]; then
    echo "CONTROL $id FAIL: expected exit $want, got $rc" >&2; cat "$tmp/$id.log" >&2; exit 1
  fi
  for reason in "$@"; do
    grep -F -- "$reason" "$tmp/$id.log" > /dev/null ||
      { echo "CONTROL $id FAIL: expected reason: $reason" >&2; cat "$tmp/$id.log" >&2; exit 1; }
  done
  echo "CONTROL $id OK"
}

# N1: edited doc copy. One Lean load checks the three D15 failure kinds.
python3 - "$tmp/base.md" "$tmp/edited.md" "$dropped" "$changed" "$after" <<'PY'
import pathlib
import sys

src, dst, dropped, changed, after = sys.argv[1:]
out, seen = [], set()
for line in pathlib.Path(src).read_text().splitlines(keepends=True):
    words = line.split()
    name = words[1] if len(words) == 3 else None
    if name == dropped:
        seen.add(name)
        continue
    if name == changed:
        seen.add(name)
        words[2] = ("0" if words[2][0] != "0" else "1") + words[2][1:]
        line = " ".join(words) + "\n"
    out.append(line)
    if name == after:
        seen.add(name)
        out.append(f"{words[0]} {after}Control {words[2]}\n")
if seen != {dropped, changed, after}:
    raise SystemExit("CONTROL SETUP FAIL: entry absent")
pathlib.Path(dst).write_text("".join(out))
PY
expect N1 1 "$tmp/edited.md" "NOT LISTED $dropped" "CHANGED $changed " \
  "EXTRA ENTRY $extra (heading" "UNKNOWN $extra (heading"

# N2: a missing doc is an error, not a SKIP (PC-SA has no pre-freeze bootstrap).
expect N2 2 "$tmp/no-current.md" "cannot read $tmp/no-current.md"
