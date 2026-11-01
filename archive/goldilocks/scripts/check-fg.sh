#!/usr/bin/env bash
# All FG checks in one run. It builds the two FG libraries once (under --wfail),
# then runs the root-import check, the syntax check, the axiom check, the
# pinned-name check, the pin check and the negative controls of the pin check
# and of the FG import-closure check, and stops at the first failure. The
# test-only overrides FGPINIDS, FGREG and FGHISTALLOW are unset for the
# positive runs. The Lean
# checks read the built .olean files, which Lean does not compare with the
# sources, so they must run after the build. Run: bash scripts/check-fg.sh.
# --research-only checks the pin names, registry, research sources and pin
# controls. It requires fresh FG build output and still runs Lean emitters.
# Use the default mode for the full FG gate.
# Exit codes: 0 all checks pass; otherwise the exit code of the failed step.
set -euo pipefail
unset FGPINIDS FGREG FGHISTALLOW
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
research_only=0
case "${1:-}" in
  '') [ $# -eq 0 ] || exit 2 ;;
  --research-only) [ $# -eq 1 ] || exit 2; research_only=1 ;;
  *) echo "usage: bash scripts/check-fg.sh [--research-only]" >&2; exit 2 ;;
esac
step() { echo "== $1"; }
# Use the same complete source module set as the public inventory writer.
targets=$(python3 -B - <<'PY'
import runpy
import sys
sys.path.insert(0, 'scripts')
snapshot = runpy.run_path('scripts/write-check-inventories.py')['snapshot']
print(' '.join(snapshot.source_modules(snapshot.SCOPES['fg'])))
PY
)
mkdir -p .lake
log=$(mktemp)
neg=$(mktemp -d "$PWD/.lake/fg-neg.XXXXXX")
trap 'rm -f "$log"; rm -rf "$neg"' EXIT
if [ "$research_only" = 1 ]; then
  step "research-only: require fresh FG build output"
  lake build --no-build $targets >"$log" 2>&1 ||
    { rc=$?; echo "RESEARCH CHECK NEEDS FRESH FG BUILD"; tail -30 "$log"; exit "$rc"; }
  export GATE_NO_BUILD=1
else
step "lake build --wfail: complete FG source scope"
lake build --wfail $targets >"$log" 2>&1 ||
  { rc=$?; echo "BUILD FAILED"; tail -30 "$log"; exit $rc; }
step "root imports"
missing=$(comm -23 \
  <(ls "$(gate_source_dir AvailableChainKitFG)"/*.lean \
    "$(gate_source_dir AvailableChainSimplexFG)"/*.lean |
    while IFS= read -r p; do python3 -B scripts/source_layout.py module "$p"; done | sort) \
  <(grep -ho 'import [A-Za-z.]*' "$(gate_source_path AvailableChainKitFG)" \
    "$(gate_source_path AvailableChainSimplexFG)" |
    sed 's/import //' | sort))
[ -z "$missing" ] || { echo "NOT IMPORTED BY A LIBRARY ROOT: $missing"; exit 2; }
step "scripts/check-fg-syntax.sh"
bash scripts/check-fg-syntax.sh
step "scripts/CheckFGAxioms.lean"
python3 -B scripts/current-inventory.py fg scripts/fg-expected.txt
python3 -B scripts/write-check-inventories.py --scope fg --check
gate_inventory_args scripts/fg-expected.txt
# The data reader validates names; quoted array arguments preserve ? and !.
lake env lean --run scripts/CheckFGAxioms.lean --expect finalityOf_def "${GATE_INVENTORY[@]}"
fi
step "scripts/FGPinIds.lean --check-names"
lake env lean --run scripts/FGPinIds.lean --check-names
step "scripts/check-fg-pins.sh"
bash scripts/check-fg-pins.sh
step "negative controls of scripts/check-fg-pins.sh"
# Each control runs the pin check on temporary copies: an emitter script that
# changes the elaborated table (FGPINIDS), a registry copy (FGREG) or an
# allowlist copy (FGHISTALLOW); some controls use the real registry. Each
# control must fail and print its message (expect_pass: must pass).
# FGNEGSHOW=1 also prints the output of each control.
run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }
show() { [ -z "${FGNEGSHOW:-}" ] || printf "%s\n" "$out" | sed "s/^/    /"; }
expect_fail() {  # NAME PATTERN...: the check failed and printed each PATTERN (fixed strings)
  local name=$1 p; shift
  if [ "$code" -eq 0 ]; then echo "$out"; echo "NEGATIVE CONTROL NOT DETECTED: $name"; exit 1; fi
  for p in "$@"; do
    if [[ $out != *"$p"* ]]; then
      echo "$out"; echo "NEGATIVE CONTROL $name: missing \"$p\""; exit 1
    fi
  done
  echo "rejected, as expected: $name"; show
}
expect_pass() {  # NAME: the check passed
  if [ "$code" -ne 0 ]; then echo "$out"; echo "POSITIVE CONTROL FAILED: $1"; exit 1; fi
  echo "passed, as expected: $1"; show
}
emitter() {  # NAME PINS HIST: an emitter of the manifest of these Lean values
  cat > "$neg/$1.lean" <<LEAN
import AvailableChainKitFG.Pins
open AvailableChain.KitFG
def main : IO Unit := do
  for l in manifest ($2) defPins notFormalized ($3) do IO.println l
LEAN
}
# splice NAME COV KINDS: the manifest of the real table, except that the records
# and trailers of KINDS come from the table with one more pin neg.extra.v1 (one
# clause COV): a record of a pin that has no pin record (step 0 controls).
splice() {
  cat > "$neg/$1.lean" <<LEAN
import AvailableChainKitFG.Pins
open AvailableChain.KitFG
def kinds : List String := $3
def pick (l : String) : Bool :=
  kinds.any fun k => l.startsWith (k ++ " ") || l.startsWith ("END " ++ k ++ " ")
def main : IO Unit := do
  let base := manifest pins defPins notFormalized historicalPins
  let extra : Pin := { id := "neg.extra.v1", sources := [], clauses := [⟨"control", $2⟩] }
  let full := manifest (pins ++ [extra]) defPins notFormalized historicalPins
  let body (ls : List String) := ls.filter (!·.startsWith "END ")
  let trail (ls : List String) := ls.filter (·.startsWith "END ")
  let key (l : String) := (l.splitOn " ").take 2
  for l in (body base).filter (!pick ·) ++ (body full).filter pick do IO.println l
  for t in trail base do
    IO.println (if pick t then ((trail full).find? (key · == key t)).getD t else t)
LEAN
}
withdraw() {  # ID: a registry copy with the Index status of ID set to WITHDRAWN (control)
  I="$1" LC_ALL=C awk -F'│' -v OFS='│' '/^## Index/ { s = 1 } /^## / && !/^## Index/ { s = 0 }
    s && index($0, "│ " ENVIRON["I"] " ") == 1 { $4 = " WITHDRAWN (control) "; n++ }
    { print } END { if (n != 1) exit 1 }' docs/internal/FG-COMPOSITION.md > "$neg/reg-$1.md" ||
    { echo "NO INDEX ROW FOR THE CONTROL: $1"; exit 1; }
}
pins_check() { run env "$@" bash scripts/check-fg-pins.sh; }
# A current pin (not a hist pin) that the controls change.
cur=fg.accountable.v1
addCov() { echo "pins.map fun p => if p.id == \"$cur\" then { p with clauses := p.clauses ++ \
  [⟨\"control\", $1⟩] } else p"; }
# The allowlist of the script.
sed -n "/^HIST='\$/,/^'\$/p" scripts/check-fg-pins.sh | sed '1d;$d' > "$neg/allow0"

# Step 4, status test.
emitter NegA "$(addCov '.ap "ap.headReachesLo.v5" ""')" historicalPins
withdraw ap.headReachesLo.v5
pins_check FGPINIDS="$neg/NegA.lean" FGREG="$neg/reg-ap.headReachesLo.v5.md"
expect_fail "(a) a current .ap to a withdrawn AP id (registry copy)" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN (control)), named by the current pin $cur (dep)"
pins_check FGPINIDS="$neg/NegA.lean"
expect_fail "(a) the same on the real registry" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN" "named by the current pin $cur (dep)"
emitter NegB "$(addCov '.external "fj.frame.v3" ""')" historicalPins
withdraw fj.frame.v3
pins_check FGPINIDS="$neg/NegB.lean" FGREG="$neg/reg-fj.frame.v3.md"
expect_fail "(b) a current dep on a withdrawn pin (registry copy)" \
  "NOT CURRENT: fj.frame.v3 (WITHDRAWN (control)), named by the current pin $cur (dep)"
pins_check FGPINIDS="$neg/NegB.lean"
expect_fail "(b) the same on the real registry" \
  "NOT CURRENT: fj.frame.v3 (WITHDRAWN" "named by the current pin $cur (dep)"
emitter NegF "$(addCov '.ap "ap.X.v1" ""')" historicalPins
pins_check FGPINIDS="$neg/NegF.lean"
expect_fail "(f) a current .ap to an id with status REFUTED; WITHDRAWN (real registry)" \
  "NOT CURRENT: ap.X.v1 (REFUTED; WITHDRAWN), named by the current pin $cur (dep)"
emitter NegG "$(addCov '.ap "ap.headReachesLo.v4" ""')" historicalPins
pins_check FGPINIDS="$neg/NegG.lean"
expect_fail "(g) a current .ap to a SUPERSEDED id (real registry)" \
  "NOT CURRENT: ap.headReachesLo.v4 (SUPERSEDED" "named by the current pin $cur (dep)"
withdraw "$cur"
pins_check FGREG="$neg/reg-$cur.md"
expect_fail "(h) a current pin whose own id is WITHDRAWN" \
  "NOT CURRENT: $cur (WITHDRAWN (control)), named by the current pin $cur (own id)"
emitter NegI "$(addCov '.paper "from ap.headReachesLo.v5 and fg.finalLock.v1"')" historicalPins
pins_check FGPINIDS="$neg/NegI.lean"
expect_fail "(i) a current pin that names a withdrawn id in its free text" \
  "NOT CURRENT: ap.headReachesLo.v5 (WITHDRAWN" "named by the current pin $cur (text)" \
  "NOT CURRENT: fg.finalLock.v1 (WITHDRAWN"
emitter PosI "$(addCov '.paper "a note (history: ap.headReachesLo.v5 (R ≥ 3), fg.finalLock.v1)"')" \
  historicalPins
pins_check FGPINIDS="$neg/PosI.lean"
expect_pass "(i) the same ids inside a (history: …) marker"
emitter NegI2 "$(addCov '.paper "a note (history: ap.headReachesLo.v5"')" historicalPins
pins_check FGPINIDS="$neg/NegI2.lean"
expect_fail "(i) an unclosed (history: marker" "MALFORMED TRAILER: END mention" "$cur/!UNCLOSED"

# Step 5, the hist pins and the allowlist.
emitter NegC pins "historicalPins ++ [\"$cur\"]"
pins_check FGPINIDS="$neg/NegC.lean"
expect_fail "(c) a hist pin not on the allowlist" "HIST PIN NOT ON THE ALLOWLIST: $cur"
{ cat "$neg/allow0"; echo "$cur 2026-09-29 control (d)"; } > "$neg/allow"
pins_check FGHISTALLOW="$neg/allow"
expect_fail "(d) an allowlist entry with no hist record" \
  "ALLOWLIST ENTRY WITHOUT A HIST RECORD: $cur"
pins_check FGPINIDS="$neg/NegC.lean" FGHISTALLOW="$neg/allow"
expect_fail "(e) a hist pin with a current status (PROVED)" "HIST PIN IS CURRENT: $cur (PROVED"
{ cat "$neg/allow0"; echo "$cur 2026-09-29"; } > "$neg/allowM"
pins_check FGHISTALLOW="$neg/allowM"
expect_fail "(j) an allowlist entry with no reason" "MALFORMED ALLOWLIST ENTRY: $cur 2026-09-29"
{ cat "$neg/allow0"; head -1 "$neg/allow0"; } > "$neg/allowD"
pins_check FGHISTALLOW="$neg/allowD"
expect_fail "(j) a duplicate allowlist entry" "DUPLICATE ALLOWLIST ENTRY: fj.frame.v3"

# Step 0, the manifest.
emitter NegK1 pins 'historicalPins ++ ["no.such.v1"]'
pins_check FGPINIDS="$neg/NegK1.lean"
expect_fail "(k) a hist id that is not a pin id" "HIST ID NOT A PIN ID: no.such.v1"
emitter NegK2 pins 'historicalPins ++ ["fj.frame.v3"]'
pins_check FGPINIDS="$neg/NegK2.lean"
expect_fail "(k) a repeated hist record" "DUPLICATE: hist fj.frame.v3"
splice NegK3 '.external "comp.settle.v1" ""' '["dep"]'
pins_check FGPINIDS="$neg/NegK3.lean"
expect_fail "(k) a dep record of no pin" "DEP OF NO PIN: neg.extra.v1"
splice NegK4 '.external "fg.uniqueJust.v1" ""' '["external"]'
pins_check FGPINIDS="$neg/NegK4.lean"
expect_fail "(k) an external id with no dep record" "DEP TARGETS ARE NOT THE AP AND EXTERNAL IDS"
splice NegK5 '.paper "see fg.uniqueJust.v1"' '["mention"]'
pins_check FGPINIDS="$neg/NegK5.lean"
expect_fail "(k) a mention record of no pin" "MENTION OF NO PIN: neg.extra.v1"

# The FG import closure (CheckFGAxioms.lean): a root module that imports a
# library outside the closure allowlist (a stand-in for AvailableChainFGSA;
# scripts/check-fgsa.sh runs the control with AvailableChainFGSA itself).
if [ "$research_only" = 0 ]; then
printf 'def negLibX : Nat := 1\n' > "$neg/AvailableChainNegLib.lean"
printf 'import AvailableChainNegLib\n' > "$neg/FGClosureNeg.lean"
for m in AvailableChainNegLib FGClosureNeg; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c \
  'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGAxioms.lean --root FGClosureNeg' "$neg"
expect_fail "(l) a library above the FG libraries in the FG import closure" \
  "FORBIDDEN LIBRARY IN THE FG IMPORT CLOSURE: AvailableChainNegLib"
# An orphan module must be audited even when no facade imports it.
orphan=$neg/orphan
mkdir -p "$orphan"
# Lean resolves a library prefix from one search directory. Keep its compiled
# modules together when adding the isolated orphan under that prefix.
for lib in AvailableChainSimplexFG AvailableChainKitFG; do
  cp -R "$(gate_source_dir "$lib")" "$(gate_source_path "$lib")" "$orphan/"
  cp -R ".lake/build/lib/lean/$lib" "$orphan/"
  cp .lake/build/lib/lean/"$lib".olean* "$orphan/"
done
mkdir -p "$orphan/scripts"
cp scripts/source_layout.py "$orphan/scripts/"
printf '[[lean_lib]]\nname="AvailableChainSimplexFG"\n[[lean_lib]]\nname="AvailableChainKitFG"\n' \
  > "$orphan/lakefile.toml"
mkdir -p "$orphan/AvailableChainKitFG/Tests"
printf '%s\n' 'namespace AvailableChain.KitFG.Control' 'axiom orphanBad : Nat' \
  'end AvailableChain.KitFG.Control' > "$orphan/AvailableChainKitFG/Tests/Orphan.lean"
lake env bash -c \
  'lean --root="$0" -o "$0/AvailableChainKitFG/Tests/Orphan.olean" \
    "$0/AvailableChainKitFG/Tests/Orphan.lean"' "$orphan"
run lake env bash -c \
  'export LEAN_PATH="$0:$LEAN_PATH"; cd "$0"; lean --run "$1/scripts/CheckFGAxioms.lean"' \
  "$orphan" "$PWD"
expect_fail "(m) a project axiom in an FG module outside the facades" \
  "BAD AXIOMS AvailableChain.KitFG.Control.orphanBad"
fi
if [ "$research_only" = 1 ]; then echo "FG research checks pass (research-only)"
else echo "all FG checks pass"; fi
