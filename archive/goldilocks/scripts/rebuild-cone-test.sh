#!/usr/bin/env bash
# Check (c), BUILD §7.1 and §7.2 B0: rebuild-cone-test.sh <Module.Name> [<toolchain>]
#
# The primary build check: under the module system (`module`, `public import`,
# `@[expose] public section`, proofs not exported), a proof-only edit must
# rebuild exactly one module. The script works on a throwaway copy of the
# repository (default: the parent of scripts/; CONE_REPO overrides it):
#   1. the copy must be up to date (`lake build --no-build`), else exit 2;
#   2. it makes two proof-only edits in <Module.Name>: one line
#      `have coneProbe : True := trivial` at the start of the first tactic
#      proof (`:= by` at the end of a line) of a theorem, and a new
#      `private theorem` at the end of the file;
#   3. it waits for a free compile slot (fewer than 3 `lean.orig`; BUILD
#      §7.6), runs `lake build`, lists the rebuilt project modules, and
#      deletes the copy.
# Exit 0: exactly one module rebuilt (the edited one). Exit 1: more than one.
# Exit 2: usage error, baseline not built, or the edited build failed.
# <toolchain> (optional) runs `elan run <toolchain> lake`; the tree must be
# built with that toolchain. CONE_TARGETS (optional, space-separated lake
# targets) limits the baseline check and the build to those targets, for a
# tree that is green only in part; the default is the default targets. The
# edits add no axiom and use no `simp [f]` or `rw [f]`, so the equation-lemma
# and axiom triggers (BUILD §7.1) are out of scope here; check (d) covers
# them. Sketch: claude-files/a0/check-sketches/rebuild-cone-test.sh (S4).
set -euo pipefail
# Copy source separately from Lake data. Only stable build inputs enter the
# copy; no gate/control/timing directory can enter through rsync or APFS clone.
copy_repo() {
  local source=$1 target=$2 mode=${3:-auto} part
  rsync -a --exclude=/.lake --exclude=/.git --exclude=/AGENTS.md \
    --exclude=/state.md --exclude=/log.md --exclude=/claude-files "$source/" "$target/"
  mkdir -p "$target/.lake"
  for part in build config; do
    [ -d "$source/.lake/$part" ] || continue
    if [ "$mode" = auto ] && cp -c -R "$source/.lake/$part" "$target/.lake/" 2>/dev/null; then
      continue
    fi
    mkdir -p "$target/.lake/$part"
    rsync -a "$source/.lake/$part/" "$target/.lake/$part/"
  done
  ln -s "$source/.lake/packages" "$target/.lake/packages"
}

if [ "${1:-}" = --controls ] || [ "${1:-}" = --copy-selftest ]; then
  TMP=$(mktemp -d "${TMPDIR:-/tmp}/cone-copy-control.XXXXXX")
  trap 'rm -rf "$TMP"' EXIT
  for mode in auto rsync; do
    src=$TMP/$mode-source
    dst=$TMP/$mode-copy
    mkdir -p "$src/.lake/build" "$src/.lake/config" "$src/.lake/packages" "$dst"
    printf 'source\n' > "$src/Probe.lean"
    printf 'built\n' > "$src/.lake/build/probe.olean"
    printf 'config\n' > "$src/.lake/config/probe"
    for name in fgsa-run-neg.keep fgsa-manifest-times.keep gate-slots.keep future-temp.keep; do
      mkdir "$src/.lake/$name"
      printf 'excluded\n' > "$src/.lake/$name/probe"
    done
    vanish=$(mktemp -d "$src/.lake/fgsa-run-neg.XXXXXX")
    printf 'vanishing\n' > "$vanish/probe"
    # Enough output to fill the pipe: rsync cannot finish before the reader
    # sees a copied-file marker and removes the temporary gate directory.
    python3 - "$src" <<'PYFILES'
from pathlib import Path
import sys
root = Path(sys.argv[1])
for i in range(2000):
    (root / (f'copy-{i:04d}-' + 'x' * 180)).write_text('copy control\n')
PYFILES
    fifo=$TMP/$mode-copy-events
    mkfifo "$fifo"
    (
      seen=0
      while IFS= read -r -t 10 event; do
        case "$event" in copy:*) seen=1; break ;; esac
      done
      [ "$seen" = 1 ] && [ -d "$vanish" ] || exit 1
      rm -rf "$vanish"
      printf 'deleted during source copy\n' > "$TMP/$mode-deleted"
      cat >/dev/null
    ) < "$fifo" & vanisher=$!
    rsync() {
      local last
      for last in "$@"; do :; done
      if [ "$last" = "$dst/" ]; then
        command rsync -v --out-format='copy:%n' "$@" > "$fifo"
      else
        command rsync "$@"
      fi
    }
    copy_repo "$src" "$dst" "$mode"
    unset -f rsync
    wait "$vanisher"
    [ -s "$TMP/$mode-deleted" ]
    [ ! -e "$vanish" ]
    cmp "$src/Probe.lean" "$dst/Probe.lean"
    cmp "$src/.lake/build/probe.olean" "$dst/.lake/build/probe.olean"
    cmp "$src/.lake/config/probe" "$dst/.lake/config/probe"
    [ -L "$dst/.lake/packages" ]
    [ "$(ls -A "$dst/.lake" | sort | tr '\n' ' ')" = 'build config packages ' ]
    echo "CONTROL vanishing gate directory ($mode): PASS"
  done
  exit 0
fi
[ $# -ge 1 ] && [ $# -le 2 ] || { echo "usage: $0 <Module.Name> [<toolchain>]" >&2; exit 2; }
REPO=$(cd "${CONE_REPO:-$(dirname "$0")/..}" && pwd); MOD=$1; TC=${2:-}
LAKE=(lake); [ -n "$TC" ] && LAKE=(elan run "$TC" lake)
REL=$(python3 -B "$REPO/scripts/source_layout.py" --root "$REPO" path "$MOD")
[ -f "$REPO/$REL" ] || { echo "no file $REPO/$REL" >&2; exit 2; }
TMP=$(mktemp -d "${TMPDIR:-/tmp}/cone-test.XXXXXX")
trap 'rm -rf "$TMP"' EXIT
copy_repo "$REPO" "$TMP"
cd "$TMP"
"${LAKE[@]}" build --no-build ${CONE_TARGETS:-} >/dev/null 2>&1 ||
  { echo "baseline: tree not built; run lake build first" >&2; exit 2; }
cp "$REL" "$TMP/.orig.lean"
python3 - "$REL" <<'PY'
import re, sys
p = sys.argv[1]; lines = open(p).read().split('\n')
decl = re.compile(r'^\s*(@\[[^\]]*\]\s*)?((private|protected)\s+)?(theorem|lemma)\b')
other = re.compile(r'^\s*(@\[[^\]]*\]\s*)?((private|protected|noncomputable)\s+)*'
                   r'(def|abbrev|instance|structure|inductive|example|theorem|lemma)\b')
done = False; i = 0
while i < len(lines) and not done:
    if decl.match(lines[i]):
        j = i
        while j < len(lines):
            if j > i and other.match(lines[j]): break
            if lines[j].rstrip().endswith(':= by'):
                k = j + 1
                while k < len(lines) and not lines[k].strip(): k += 1
                if k < len(lines):
                    ind = re.match(r'\s*', lines[k]).group(0)
                    if len(ind) > len(re.match(r'\s*', lines[j]).group(0)) or ind:
                        lines.insert(j + 1, ind + 'have coneProbe : True := trivial')
                        done = True
                break
            j += 1
        i = j if j > i else i + 1
    else:
        i += 1
lines.append('')
lines.append('private theorem coneProbePrivate : True := trivial')
open(p, 'w').write('\n'.join(lines) + '\n')
print('edit: in-proof line ' + ('added' if done else 'NOT added (no tactic proof found)')
      + '; private theorem appended')
PY
# Wait for a free compile slot (3 machine-wide; the wrapper also throttles).
while [ "$(pgrep -x lean.orig | wc -l | tr -d ' ')" -ge 3 ]; do sleep 5; done
set +e
OUT=$("${LAKE[@]}" build ${CONE_TARGETS:-} 2>&1); RC=$?
set -e
cp "$TMP/.orig.lean" "$REL"
if [ $RC -ne 0 ]; then
  echo "$OUT" | grep -E '^error' | head -5
  echo "edited build failed" >&2; exit 2
fi
BUILT=$(echo "$OUT" | sed -nE 's/.*Built ([A-Za-z0-9_.«»]+).*/\1/p' |
  while read -r m; do
    path=$(python3 -B scripts/source_layout.py path "$m") && [ -f "$path" ] && echo "$m"
  done)
N=$(echo "$BUILT" | grep -c . || true)
echo "rebuilt $N module(s):"; echo "$BUILT" | sed 's/^/  /'
[ "$N" -eq 1 ] && { echo "PASS: a proof-only edit in $MOD rebuilt one module"; exit 0; }
echo "FAIL: a proof-only edit in $MOD rebuilt $N modules"; exit 1
