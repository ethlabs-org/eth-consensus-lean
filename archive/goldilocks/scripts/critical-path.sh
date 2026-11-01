#!/usr/bin/env bash
# BUILD §7.6/§7.7: the FG-SA critical-path measurement (`bash scripts/gate.sh --critical-path`).
# NUC only. Run it through gate.sh, which holds the MemoryMax scope; the caller holds
# flock /tmp/ac-nuc.lock. A scratch clone of HEAD with a copy of .lake/packages (Mathlib
# warm) and an empty .lake/build is built with CP_SLOTS (default 3) compile slots. Every
# `lean` call of the build goes through a timing wrapper (bin/lean of a copied sysroot; Lake
# ignores the LEAN variable), so a module span excludes its slot wait. The critical path is
# the longest import chain by sum of spans. It fails above CP_LIMIT seconds (default 120;
# target CP_TARGET, default 100; BUILD r3.8).
set -euo pipefail
cd "$(dirname "$0")/.."
[ "$(uname -s)" = Linux ] || { echo "critical-path: NUC (Linux) only" >&2; exit 2; }
targets=${CP_TARGETS:-"AvailableChainFGSA AvailableChainFGSARun"}
slots=${CP_SLOTS:-3}; target=${CP_TARGET:-100}; limit=${CP_LIMIT:-120}
case "$slots" in ''|0*|*[!0-9]*) echo "CP_SLOTS must be a positive integer" >&2; exit 2 ;; esac
head=$(git rev-parse HEAD)
mkdir -p .lake
d=$(mktemp -d "$PWD/.lake/critical-path.XXXXXX")
trap 'rm -rf "$d"' EXIT
sysroot=$(lean --print-prefix)

# A copied sysroot whose bin/lean is the timing wrapper; bin/lake is a copy, so that Lake
# finds this sysroot from its own path.
mkdir -p "$d/sys/bin" "$d/slots"
for e in "$sysroot"/*; do [ "$(basename "$e")" = bin ] || ln -s "$e" "$d/sys/"; done
for e in "$sysroot"/bin/*; do ln -s "$e" "$d/sys/bin/"; done
rm "$d/sys/bin/lean" "$d/sys/bin/lake"
cp "$sysroot/bin/lake" "$d/sys/bin/lake"
cat > "$d/sys/bin/lean" <<'WRAP'
#!/bin/bash
# Timing wrapper: take one of CP_SLOTS flock slots, run the real lean, log "start end rc file".
f=; for a in "$@"; do case "$a" in *.lean) f=$a ;; esac; done
[ -n "$f" ] || exec "$CP_REAL_LEAN" "$@"
while :; do
  for k in $(seq 1 "$CP_SLOTS"); do
    exec {fd}>"$CP_SLOT_DIR/s$k"
    if flock -n "$fd"; then break 2; fi
    exec {fd}>&-
  done
  sleep 0.1
done
t0=$(date +%s.%N); rc=0; "$CP_REAL_LEAN" "$@" || rc=$?; t1=$(date +%s.%N)
echo "$t0 $t1 $rc $f" >> "$CP_LOG"
exit $rc
WRAP
chmod +x "$d/sys/bin/lean"

git clone -q --no-checkout "$PWD" "$d/ac"
git -C "$d/ac" checkout -q --detach "$head"
mkdir -p "$d/ac/.lake"
cp -a .lake/packages "$d/ac/.lake/packages"
echo "critical-path: head $(git rev-parse --short HEAD); targets $targets; $slots slots"

export CP_REAL_LEAN=$sysroot/bin/lean CP_SLOTS=$slots CP_SLOT_DIR=$d/slots CP_LOG=$d/times.log
t0=$(date +%s)
# shellcheck disable=SC2086
if ! (cd "$d/ac" && "$d/sys/bin/lake" build $targets > "$d/build.log" 2>&1); then
  tail -20 "$d/build.log"
  echo "critical-path: BUILD FAILED" >&2
  exit 1
fi
echo "critical-path: cold build wall $(( $(date +%s) - t0 )) s; $(wc -l < "$d/times.log") modules"

python3 - "$d/ac" "$d/times.log" "$target" "$limit" <<'PY'
import os, re, sys
repo, log, target, limit = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4])
sys.path.insert(0, os.path.join(repo, 'scripts'))
from source_layout import Layout
layout = Layout(repo)
span = {}
for line in open(log):
    t0, t1, rc, f = line.split(maxsplit=3)
    span[layout.module_of_source(os.path.relpath(f.strip(), repo))] = float(t1) - float(t0)
imp = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)')
deps = {m: [i.group(1) for i in map(imp.match, open(os.path.join(repo, layout.source_path(m))))
            if i and i.group(1) in span] for m in span}
memo = {}
def cp(m):
    if m not in memo:
        best = max((cp(d) for d in deps[m]), key=lambda x: x[0], default=(0.0, []))
        memo[m] = (best[0] + span[m], [m] + best[1])
    return memo[m]
sys.setrecursionlimit(10000)
total, chain = max((cp(m) for m in span), key=lambda x: x[0])
print(f"critical-path: sum of spans {sum(span.values()):.0f} s over {len(span)} modules")
print("critical-path: longest chain (span s, module):")
for m in chain:
    print(f"  {span[m]:6.1f}  {m}")
verdict = "PASS" if total <= limit else "FAIL"
print(f"CRITICAL PATH {verdict}: {total:.0f} s over {len(chain)} modules "
      f"(target {target:.0f} s, limit {limit:.0f} s)")
sys.exit(0 if total <= limit else 1)
PY
