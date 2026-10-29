#!/usr/bin/env bash
# The trust checks of consensus-lean, end to end. Structure copied from verified-consensus
# scripts/verify.sh (CC0-1.0): one function per step, each reporting PASS/FAIL/SKIP, then a summary.
# Every path and module list comes from scripts/boundaries.toml (layout) and the inventory that
# scripts/check-imports.py derives from it; nothing here is find-derived.
#
#   0  pins             toolchain + every dependency = scripts/pins.toml, and   (check-pins.py)
#                       Lake resolves exactly those checkouts (LEAN_PATH)
#   1  build            default targets + fixtures + check-decls                (lake)
#   2  imports          import discipline, root coverage, inventory             (check-imports.py)
#   3  declarations     axioms/sorry/opaque/unsafe/extern/csimp per library     (EthLib check-decls)
#   4  Spec surface     persisted extensions, snapshot, theorems, noconst       (SpecSurface.lean)
#   5  kernel replay    every leaf module of every default library              (leanchecker)
#   6  review pins      ReviewAxioms compiled into the tests root               (#guard_msgs)
#   7  backstop         grep for sorry/admit/native_decide, Spec meta commands, lakefile options
#   8  vendored         sha256 of every verbatim copy                           (scripts/vendor.sha256)
#   9  comparator config  exact comparator.json (from B4; fixtures run now)    (jq)
#   10 lake check       sandboxed build + export + replay                       (needs bwrap)
#   11 lake comparator  Spec statements vs proofs (from B4)                     (needs bwrap)
#   12 docs             README spec-file list (from B5)
# Every step with a negative fixture also runs it through the same function ("self-test" steps).
#
# Usage: scripts/check.sh [--no-build] [--quick] [--update-snapshot] [--update-extensions]
#   --no-build           do not compile; `lake build --no-build` still fails on anything stale
#   --quick              skip the self-tests and kernel replay (summary: partial)
#   --update-snapshot    rewrite scripts/spec-snapshot.txt (the run then FAILS: review + commit it)
#   --update-extensions  rewrite scripts/spec-extensions.txt likewise
# With CI set, --quick, --update-* and --no-build are refused.
# On the shared box run it only inside `job --mem 16G ...` (it refuses to start without RUN_DIR or CI).

set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

usage="usage: scripts/check.sh [--no-build] [--quick] [--update-snapshot] [--update-extensions]"
no_build=0 quick=0 update_snapshot=0 update_extensions=0
while (($#)); do
  case "$1" in
    --no-build) no_build=1 ;;
    --quick) quick=1 ;;
    --update-snapshot) update_snapshot=1 ;;
    --update-extensions) update_extensions=1 ;;
    -h|--help) echo "$usage"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; echo "$usage" >&2; exit 2 ;;
  esac
  shift
done
if [[ -z "${RUN_DIR:-}" && -z "${CI:-}" ]]; then
  echo "check.sh: refusing to run without RUN_DIR (set by \`job\`) or CI: on the shared box run it in a job" >&2
  exit 2
fi
if [[ -n "${CI:-}" ]] && ((quick || no_build || update_snapshot || update_extensions)); then
  echo "check.sh: --quick, --no-build and --update-* are refused in CI" >&2
  exit 2
fi

CFG=scripts/boundaries.toml
WORK="$(mktemp -d "${RUN_DIR:-${TMPDIR:-/tmp}}/check.XXXXXX")"
INV="$WORK/inventory.tsv"
FX=scripts/fixtures
SURFACE=(lake env lean --run scripts/SpecSurface.lean)

# cfg <key>: a list or string of [checks] (or a top-level key) of boundaries.toml, one item per line.
cfg() {
  python3 -I -c 'import sys, tomllib
c = tomllib.load(open(sys.argv[1], "rb")); k = sys.argv[2]
v = c["lib"] if k == "libs" else c["checks"][k] if k in c.get("checks", {}) else c[k]
v = [l["name"] for l in v] if k == "libs" else v
print("\n".join(v) if isinstance(v, list) else v)' "$CFG" "$1"
}
mapfile -t LIBS < <(cfg libs)
mapfile -t SPEC_MODULES < <(cfg spec_modules)
mapfile -t EXT_LIBS < <(cfg extension_libs)
mapfile -t EXTRA_TARGETS < <(cfg extra_build_targets)
mapfile -t NOCONST_EXEMPT < <(cfg noconst_exempt)
THEOREMS_MODE="$(cfg theorems_mode)"
REVIEW_AXIOMS="$(cfg review_axioms_module)"
REVIEW_ROOT="$(cfg review_root)"
CHALLENGE="$(cfg challenge_module)"
SOLUTION="$(cfg solution_module)"
STATEMENTS="$(cfg statements_module)"
case "$THEOREMS_MODE" in report|enforce) ;; *) echo "check.sh: theorems_mode must be report or enforce" >&2; exit 2 ;; esac
((${#LIBS[@]} > 0 && ${#SPEC_MODULES[@]} > 0 && ${#EXT_LIBS[@]} > 0 && ${#EXTRA_TARGETS[@]} > 0)) || { echo "check.sh: empty configuration" >&2; exit 2; }

# Inventory queries (written by step 2): modules of a library; leaf or parent modules of all libraries.
inv_modules() { awk -F'\t' -v l="$1" '$1 == l { print $2 }' "$INV"; }
inv_kind() { awk -F'\t' -v k="$1" '$3 == k { print $2 }' "$INV"; }
mod_file() { echo "${1//.//}.lean"; }

# expect_fail <tag|-> <cmd...>: the command must exit nonzero, and print <tag> unless <tag> is `-`.
expect_fail() {
  local tag="$1" out rc
  shift
  out="$("$@" 2>&1)" && rc=0 || rc=$?
  if ((rc == 0)); then
    echo "  expected failure, got exit 0: $*"; echo "$out" | tail -20; return 1
  fi
  if [[ "$tag" != - ]] && ! grep -qF -- "$tag" <<<"$out"; then
    echo "  exit $rc but no '$tag' in the output of: $*"; echo "$out" | tail -20; return 1
  fi
  [[ "$tag" == - ]] && tag=
  echo "  ok (exit $rc${tag:+, $tag}): $*"
}
expect_pass() {
  local out
  if out="$("$@" 2>&1)"; then echo "  ok (exit 0): $*"; return 0; fi
  echo "  expected exit 0: $*"; echo "$out" | tail -20; return 1
}

# --- step 0: pins ---------------------------------------------------------------------------------
# pins_check <lean-toolchain> <lake-manifest.json> <package-overrides.json> <lakefile.toml> [options]:
# the checkouts are always the real .lake/packages (Lake's default packagesDir, the only one accepted).
pins_check() {
  python3 -I scripts/check-pins.py --toolchain "$1" --manifest "$2" --overrides "$3" --lakefile "$4" \
    --pins scripts/pins.toml --packages-dir .lake/packages "${@:5}"
}
pins_fixture() {  # pins_fixture <case> [options]: fixtures/pins-<case>/ (its own lakefile.toml if it has one)
  local d="$FX/pins-$1" lf=lakefile.toml
  [[ -f "$d/lakefile.toml" ]] && lf="$d/lakefile.toml"
  pins_check "$d/lean-toolchain" "$d/lake-manifest.json" "$d/package-overrides.json" "$lf" "${@:2}"
}
step_pins() {
  set +e
  local rc=0 want lp lib
  # What Lake actually resolves (overrides, path dependencies, packagesDir) is in LEAN_PATH.
  lp="$(lake env printenv LEAN_PATH)" && lib="$(lake env lean --print-libdir)" || { echo "  no LEAN_PATH"; rc=1; }
  pins_check lean-toolchain lake-manifest.json .lake/package-overrides.json lakefile.toml \
    --lean-path "$lp" --libdir "$lib" || rc=1
  want="$(python3 -I -c 'import tomllib; print(tomllib.load(open("scripts/pins.toml", "rb"))["lean_version"])')"
  if ! lake env lean --version | grep -qF "version $want,"; then
    echo "  lean --version is not $want: $(lake env lean --version)"; rc=1
  fi
  set -e
  return "$rc"
}
selftest_pins() {
  set +e
  local rc=0 c lp lib
  for c in toolchain rev url extra; do
    expect_fail 'FAIL[pins]' pins_fixture "$c" || rc=1
  done
  # Resolution mechanisms other than git checkouts in .lake/packages are refused.
  for c in path override packagesdir subdir lakefile; do
    expect_fail 'FAIL[pins] resolution' pins_fixture "$c" || rc=1
  done
  # A dependency configFile/manifestFile outside its checkout (Lake loads <checkout>/<file>): the
  # redirected lakefile keeps Cli's build directory, so LEAN_PATH and the checkout's status look unchanged.
  for c in configFile manifestFile; do
    expect_fail "FAIL[pins] resolution: Cli.$c is '../../../" pins_fixture "${c,,}" || rc=1
    expect_fail "not a tracked file of the checkout $repo_root/.lake/packages/Cli" pins_fixture "${c,,}" || rc=1
  done
  # A LEAN_PATH in which Lake resolved Cli elsewhere (what an override or path dependency produces).
  lp="$(lake env printenv LEAN_PATH)" && lib="$(lake env lean --print-libdir)" || { echo "  no LEAN_PATH"; return 1; }
  expect_fail 'FAIL[pins] resolution: LEAN_PATH has' pins_check lean-toolchain lake-manifest.json \
    .lake/package-overrides.json lakefile.toml --libdir "$lib" \
    --lean-path "$(sed 's#/\.lake/packages/Cli/#/.lake/Cli-altered/#' <<<"$lp")" || rc=1
  set -e
  return "$rc"
}

# --- step 1: build --------------------------------------------------------------------------------
step_build() {
  set +e
  local rc=0
  if ((no_build)); then
    lake build --no-build || rc=1
    lake build --no-build "${EXTRA_TARGETS[@]}" || rc=1
  else
    lake build || rc=1
    lake build "${EXTRA_TARGETS[@]}" || rc=1
  fi
  set -e
  return "$rc"
}

# --- step 2: imports ------------------------------------------------------------------------------
step_imports() {
  set +e
  python3 -I scripts/check-imports.py --config "$CFG" --lakefile lakefile.toml --inventory-out "$INV"
  local rc=$?
  set -e
  [[ $rc -eq 0 && -s "$INV" ]] || { echo "  no inventory: every later step needs it"; return 1; }
  # Every module named in [checks] must be in the inventory (a typo would silently check less).
  local m l bad=0
  for m in "${SPEC_MODULES[@]}" "$REVIEW_AXIOMS" "$REVIEW_ROOT"; do
    cut -f2 "$INV" | grep -qxF "$m" || { echo "  FAIL[config] $m (boundaries.toml [checks]) is not in the inventory"; bad=1; }
  done
  for m in "${NOCONST_EXEMPT[@]}"; do
    inv_kind parent | grep -qxF "$m" || { echo "  FAIL[config] noconst_exempt $m is not a module with descendants"; bad=1; }
  done
  for l in "${EXT_LIBS[@]}"; do
    printf '%s\n' "${LIBS[@]}" | grep -qxF "$l" || { echo "  FAIL[config] extension_libs: unknown library $l"; bad=1; }
  done
  return "$bad"
}
selftest_imports() { python3 -I scripts/check-imports.py --self-test "$FX/imports"; }

# --- step 3: declarations (EthLib check-decls) ----------------------------------------------------
# decls_scope <scope> <baseline> <modules...>: one check-decls process importing every given module;
# fails on any finding, on a stale baseline entry, and on an empty scope (`0 declarations`).
decls_scope() {
  local scope="$1" baseline="$2" out rc n
  shift 2
  (($# > 0)) || { echo "  no modules for scope $scope"; return 1; }
  out="$(lake exe check-decls --scope "$scope" --baseline "$baseline" "$@" 2>&1)" && rc=0 || rc=$?
  echo "$out"
  n="$(sed -nE "s/^check-decls: ([0-9]+) declarations under $scope,.*/\1/p" <<<"$out")"
  if [[ -z "$n" || "$n" -eq 0 ]]; then echo "  scope $scope: no declarations checked"; return 1; fi
  return "$rc"
}
# The baseline holds `<Library> <kind> <declaration>  # reason` lines. It is parsed once, strictly
# (check-decls itself silently drops a malformed line), and split into one `kind decl` file per library.
split_baseline() {  # split_baseline <baseline> <outdir> <libs...>
  local baseline="$1" dir="$2"
  shift 2
  [[ -r "$baseline" ]] || { echo "  cannot read baseline $baseline"; return 1; }
  mkdir -p "$dir" && rm -f "$dir"/baseline.*
  local l
  for l in "$@"; do : >"$dir/baseline.$l"; done
  awk -v dir="$dir" -v libs="$*" '
    BEGIN { n = split(libs, a, " "); for (i = 1; i <= n; i++) ok[a[i]] = 1 }
    { sub(/#.*/, "") }
    NF == 0 { next }
    NF != 3 || !($1 in ok) { print "  bad baseline line " FNR ": " $0; bad = 1; next }
    { print $2 " " $3 >> (dir "/baseline." $1) }
    END { exit bad }' "$baseline"
}
# decls_libs <inventory> <baseline> <libs...>: check-decls once per library, over every inventory module.
decls_libs() {
  local inv="$1" baseline="$2" rc=0 l
  shift 2
  split_baseline "$baseline" "$WORK/bl" "$@" || return 1
  for l in "$@"; do
    mapfile -t mods < <(awk -F'\t' -v l="$l" '$1 == l { print $2 }' "$inv")
    echo "  check-decls --scope $l (${#mods[@]} modules)"
    decls_scope "$l" "$WORK/bl/baseline.$l" "${mods[@]}" || rc=1
  done
  return "$rc"
}
step_decls() { decls_libs "$INV" scripts/check_decls_baseline.txt "${LIBS[@]}"; }
selftest_decls() {
  set +e
  local rc=0 out
  bash scripts/test_check_decls.sh || rc=1
  # OrphanLib through the real glue: a fixture inventory (root + orphan) and a fixture baseline.
  printf 'CheckFixtures.OrphanLib\tCheckFixtures.OrphanLib\tparent\nCheckFixtures.OrphanLib\tCheckFixtures.OrphanLib.Bad\tleaf\n' >"$WORK/fx-inv.tsv"
  echo "# fixture baseline: nothing listed" >"$WORK/fx-baseline.txt"
  out="$(decls_libs "$WORK/fx-inv.tsv" "$WORK/fx-baseline.txt" CheckFixtures.OrphanLib)" &&
    { echo "  OrphanLib passed"; rc=1; }
  for f in 'opaque CheckFixtures.OrphanLib.Bad.hidden' 'axiom CheckFixtures.OrphanLib.Bad.assumed'; do
    grep -qF "$f" <<<"$out" && echo "  ok: OrphanLib reports $f" || { echo "  OrphanLib misses $f"; rc=1; }
  done
  expect_fail 'no declarations checked' decls_scope CheckFixtures.EmptyScope /dev/null CheckFixtures.EmptyScope || rc=1
  printf 'CheckFixtures.OrphanLib opaque\n' >"$WORK/fx-malformed.txt"
  expect_fail 'bad baseline line' decls_libs "$WORK/fx-inv.tsv" "$WORK/fx-malformed.txt" CheckFixtures.OrphanLib || rc=1
  expect_fail 'cannot read baseline' decls_libs "$WORK/fx-inv.tsv" "$WORK/does-not-exist" CheckFixtures.OrphanLib || rc=1
  # BadSkipKernel passes check-decls (no axiom): only kernel replay (step 5) rejects it.
  expect_pass decls_scope CheckFixtures.BadSkipKernel /dev/null CheckFixtures.BadSkipKernel.A || rc=1
  set -e
  return "$rc"
}

# --- step 4: Spec surface (SpecSurface.lean) ------------------------------------------------------
# The snapshot header: what the Spec text means depends on (toolchain, dependency revs, options).
snapshot_header() {
  echo "# Spec snapshot: every constant owned by a Spec module. Generated by scripts/check.sh"
  echo "# --update-snapshot; a change is a protected change (owner review)."
  python3 -I -c 'import json, sys, tomllib
tc = open("lean-toolchain").read().strip()
man = json.load(open("lake-manifest.json"))
lake = tomllib.load(open("lakefile.toml", "rb"))
print("toolchain", tc)
for p in man["packages"]:
    print("package", p["name"], p["rev"])
def flat(d, pre=""):  # dotted option names: TOML nests `pp.unicode.fun` as tables
    for k, v in d.items():
        yield from flat(v, pre + k + ".") if isinstance(v, dict) else [(pre + k, v)]
for k, v in sorted(flat(lake.get("leanOptions", {}))):
    print("option", k, "=", json.dumps(v))
for kind in ("lean_lib", "lean_exe"):
    for t in lake.get(kind, []):
        for k, v in sorted(flat(t.get("leanOptions", {}))):
            print("option", kind, t["name"], k, "=", json.dumps(v))'
}
make_snapshot() {  # make_snapshot <out> <modules...>
  local out="$1"
  shift
  snapshot_header >"$out" && echo >>"$out" && "${SURFACE[@]}" snapshot --modules "$@" >>"$out" &&
    grep -q '^## ' "$out"
}
step_surface() {
  set +e
  local rc=0 l ext_mods=()
  for l in "${EXT_LIBS[@]}"; do mapfile -t -O "${#ext_mods[@]}" ext_mods < <(inv_modules "$l"); done
  echo "  extensions over ${#ext_mods[@]} modules of ${EXT_LIBS[*]}"
  if ((update_extensions)); then
    "${SURFACE[@]}" extensions --allow /dev/null --modules "${ext_mods[@]}" |
      awk '$1 == "FAIL[ext]" { print $3 }' | LC_ALL=C sort -u >"$WORK/extensions.txt"
    { echo "# Persisted-extension whitelist of the Spec-side libraries; regenerated by check.sh --update-extensions."
      echo "# Review every added name: no parser/macro/elab/tactic/initializer/attribute-registration extension."
      cat "$WORK/extensions.txt"; } >scripts/spec-extensions.txt
    echo "  FAIL  extensions updated: review and commit scripts/spec-extensions.txt as a protected change"
    rc=1
  fi
  "${SURFACE[@]}" extensions --allow scripts/spec-extensions.txt --modules "${ext_mods[@]}" || rc=1
  echo "  snapshot over ${#SPEC_MODULES[@]} Spec modules"
  if make_snapshot "$WORK/spec-snapshot.txt" "${SPEC_MODULES[@]}"; then
    if ((update_snapshot)); then
      cp "$WORK/spec-snapshot.txt" scripts/spec-snapshot.txt
      echo "  FAIL  snapshot updated: review and commit scripts/spec-snapshot.txt as a protected change"
      rc=1
    elif ! diff -u scripts/spec-snapshot.txt "$WORK/spec-snapshot.txt" >"$WORK/snapshot.diff"; then
      echo "  FAIL[snapshot] the Spec changed (review the diff; accept it with --update-snapshot):"
      head -200 "$WORK/snapshot.diff"; rc=1
    fi
  else
    echo "  snapshot generation failed"; rc=1
  fi
  if [[ "$THEOREMS_MODE" == enforce ]]; then
    "${SURFACE[@]}" theorems --allow scripts/spec-theorems.txt --modules "${SPEC_MODULES[@]}" || rc=1
  else
    "${SURFACE[@]}" theorems --allow scripts/spec-theorems.txt --report --modules "${SPEC_MODULES[@]}" |
      tee "$WORK/theorems-report.txt" | tail -3
    [[ ${PIPESTATUS[0]} -eq 0 ]] || rc=1
    echo "  NOTE  theorems in report mode: $(grep -c '^REPORT' "$WORK/theorems-report.txt") ranged theorems in Spec modules (enforced from B3)"
  fi
  mapfile -t parents < <(inv_kind parent | grep -vxF -f <(printf '%s\n' "${NOCONST_EXEMPT[@]}" | awk NF) )
  echo "  noconst over ${#parents[@]} modules with descendants"
  ((${#NOCONST_EXEMPT[@]} == 0)) ||
    echo "  NOTE  exempt from noconst, hence not replayed by leanchecker here (step 10 lake check replays them): ${NOCONST_EXEMPT[*]}"
  "${SURFACE[@]}" noconst --modules "${parents[@]}" || rc=1
  set -e
  return "$rc"
}
# snap_compare <A> <B>: snapshots of two fixture modules (separate processes), `## ` lines dropped.
snap_compare() {  # prints the diff; exit 1 = they differ (expected), anything else is an error
  make_snapshot "$WORK/snapA" "$1" && make_snapshot "$WORK/snapB" "$2" || return 2
  diff <(grep -v '^## ' "$WORK/snapA") <(grep -v '^## ' "$WORK/snapB")
}
snap_differs() {  # snap_differs <A> <B> <var>: sets <var> to the diff; fails unless diff exited 1
  local out rc
  out="$(snap_compare "$1" "$2")" && rc=0 || rc=$?
  printf -v "$3" '%s' "$out"
  ((rc == 1)) || { echo "  snapshot comparison $1 / $2: exit $rc (expected 1)"; return 1; }
}
selftest_surface() {
  set +e
  local rc=0 m d
  for m in BadMacro BadInit BadScopedSyntax BadAttr BadLocalSyntax; do
    expect_fail 'FAIL[ext]' "${SURFACE[@]}" extensions --allow scripts/spec-extensions.txt --modules "CheckFixtures.$m" || rc=1
  done
  expect_pass "${SURFACE[@]}" extensions --allow scripts/spec-extensions.txt \
    --modules CheckFixtures.GoodSpec CheckFixtures.GoodSpec.A CheckFixtures.GoodSpec.B || rc=1
  expect_fail - "${SURFACE[@]}" extensions --allow scripts/spec-extensions.txt --modules || rc=1
  expect_fail - "${SURFACE[@]}" snapshot --modules CheckFixtures.DoesNotExist || rc=1
  # SnapA/SnapB: the readable line differs.
  snap_differs CheckFixtures.SnapA.Defs CheckFixtures.SnapB.Defs d || rc=1
  grep -qE '^[<>] def Snap\.cmp' <<<"$d" && echo "  ok: SnapA/SnapB readable line differs" ||
    { echo "  SnapA/SnapB: no readable difference: $d"; rc=1; }
  # SnapHidden: readable lines equal, only a hash line differs.
  snap_differs CheckFixtures.SnapA.Defs CheckFixtures.SnapHidden.Defs d || rc=1
  if [[ -n "$d" ]] && ! grep -E '^[<>] ' <<<"$d" | grep -qvE '^[<>]   #'; then
    echo "  ok: SnapA/SnapHidden differ only in a hash line"
  else echo "  SnapA/SnapHidden: expected only a hash difference: $d"; rc=1; fi
  # SnapAux: an unranged auxiliary line differs (same readable lines).
  snap_differs CheckFixtures.SnapAuxA.Defs CheckFixtures.SnapAuxB.Defs d || rc=1
  if [[ -n "$d" ]] && ! grep -E '^[<>] ' <<<"$d" | grep -qvE '^[<>] [a-z]+ [^ ]+ #'; then
    echo "  ok: SnapAuxA/SnapAuxB differ only in unranged auxiliary lines"
  else echo "  SnapAuxA/SnapAuxB: expected only unranged differences: $d"; rc=1; fi
  expect_fail 'FAIL[theorem]' "${SURFACE[@]}" theorems --allow /dev/null --modules CheckFixtures.BadTheorem.A || rc=1
  expect_fail 'FAIL[noconst]' "${SURFACE[@]}" noconst --modules CheckFixtures.RootDecl || rc=1
  expect_pass "${SURFACE[@]}" noconst --modules CheckFixtures.GoodSpec || rc=1
  d="$("${SURFACE[@]}" statements --modules CheckFixtures.ReviewBad.A)" || { echo "  statements failed"; rc=1; }
  [[ "$d" == $'CheckFixtures.ReviewBad.GoodStmt\nCheckFixtures.ReviewBad.Stmt\nCheckFixtures.ReviewBad.Stmt2' ]] &&
    echo "  ok: statements lists the Prop definitions" || { echo "  statements printed: $d"; rc=1; }
  set -e
  return "$rc"
}

# --- step 5: kernel replay (leanchecker, one leaf module per process) ------------------------------
# leanchecker expands its argument as a name prefix and replays every match in parallel, so it only
# ever gets one module without descendants: none in the inventory, no build directory below it.
replay_leaf() {
  local m="$1" t
  local d
  for d in "${SEARCH_PATH[@]}"; do
    if [[ -d "$d/${m//.//}" ]]; then
      echo "  refused: $m has descendant modules in $d (leanchecker would expand it as a prefix)"; return 1
    fi
  done
  if cut -f2 "$INV" | awk -v p="$m." 'index($0, p) == 1 { f = 1 } END { exit !f }'; then
    echo "  refused: $m has descendant modules in the inventory"; return 1
  fi
  t="$WORK/time.$m"
  /usr/bin/time -f '%M %e' -o "$t" lake env leanchecker "$m" || { echo "  leanchecker rejected $m"; return 1; }
  read -r kb secs <"$t"
  echo "  $m: ${secs}s, peak $((kb / 1024)) MB"
  ((kb > PEAK_KB)) && PEAK_KB=$kb
  return 0
}
PEAK_KB=0
SEARCH_PATH=()
step_replay() {
  set +e
  local rc=0 m n=0 start=$SECONDS
  load_search_path || { echo "  cannot determine the Lean search path"; return 1; }
  mapfile -t leaves < <(inv_kind leaf)
  ((${#leaves[@]} > 0)) || { echo "  no leaf modules"; return 1; }
  for m in "${leaves[@]}"; do replay_leaf "$m" || rc=1; n=$((n + 1)); done
  echo "  NOTE  leanchecker: $n leaf modules, $((SECONDS - start))s total, peak $((PEAK_KB / 1024)) MB"
  set -e
  return "$rc"
}
# The search path leanchecker scans: LEAN_PATH (lake env) plus the toolchain library.
load_search_path() {
  local lp lib
  lp="$(lake env printenv LEAN_PATH)" && lib="$(lake env lean --print-libdir)" || return 1
  IFS=: read -ra SEARCH_PATH <<<"$lp"
  SEARCH_PATH+=("$lib")
  ((${#SEARCH_PATH[@]} > 1)) || return 1
}
selftest_replay() {
  set +e
  local rc=0
  load_search_path || { echo "  cannot determine the Lean search path"; return 1; }
  expect_fail 'found a problem in CheckFixtures.BadSkipKernel.A' replay_leaf CheckFixtures.BadSkipKernel.A || rc=1
  expect_fail 'refused' replay_leaf CheckFixtures.GoodSpec || rc=1
  # Descendants only in another search-path directory (a dependency's build directory).
  expect_fail 'packages/mathlib/.lake/build/lib/lean' replay_leaf Mathlib.Logic || rc=1
  expect_pass replay_leaf CheckFixtures.GoodSpec.A || rc=1
  set -e
  return "$rc"
}

# --- step 6: review pins --------------------------------------------------------------------------
# review_imports <file> <module>: the header of <file> imports <module> directly (an import through a
# helper module does not count: the pins must be compiled as part of the root's own build).
review_imports() {
  lake env lean --deps-json "$1" |
    jq -e --arg m "$2" '.imports[0].errors == [] and any(.imports[0].result.imports[]; .module == $m)' >/dev/null ||
    { echo "  FAIL[review] $1 does not import $2 directly"; return 1; }
}
step_review() { review_imports "$(mod_file "$REVIEW_ROOT")" "$REVIEW_AXIOMS"; }  # compiled by step 1
selftest_review() {
  set +e
  local rc=0 c
  expect_pass review_imports "$FX/review-imports/Direct.lean" Fx.ReviewAxioms || rc=1
  for c in Indirect Missing; do
    expect_fail 'FAIL[review]' review_imports "$FX/review-imports/$c.lean" Fx.ReviewAxioms || rc=1
  done
  expect_fail 'does not match generated message' lake env lean "$FX/ReviewAxiomsBad.lean" || rc=1
  expect_fail 'Type mismatch' lake env lean "$FX/ReviewTypeBad.lean" || rc=1
  expect_pass lake env lean "$FX/ReviewAxiomsGood.lean" || rc=1
  set -e
  return "$rc"
}

# --- step 7: grep backstop ------------------------------------------------------------------------
# grep exit status: 0 = match, 1 = no match, >1 = error. Each scan prints its matches and fails on an error.
scan() {  # scan <ere> [-w] <files...>
  local re="$1" rc
  shift
  grep -nE "$@" -e "$re" 2>&1 && rc=0 || rc=$?
  ((rc <= 1)) || { echo "  grep failed (exit $rc)"; return 2; }
}
grep_7a() {
  local r=0
  scan 'sorry|admit|native_decide|admitGoal|sorryAx|mkSorry|mkLabeledSorry' -w "$@" || r=2
  scan 'skipKernelTC|decide \+native' "$@" || r=2
  return "$r"
}
grep_7b() { scan 'run_cmd|run_meta|run_elab|#eval|#exit|(builtin_)?initialize' -w "$@"; }
grep_7c() { scan 'skipKernelTC|plugins|moreLeanArgs|weakLeanArgs|moreServerArgs|loadDynlib|dynlibs|precompileModules|debug\.' "$@"; }
step_grep() {
  local files=() spec=() found rc=0
  mapfile -t files < <(cut -f2 "$INV" | while read -r m; do mod_file "$m"; done)
  mapfile -t spec < <(for m in "${SPEC_MODULES[@]}"; do mod_file "$m"; done)
  ((${#files[@]} > 0 && ${#spec[@]} > 0)) || { echo "  no files to scan"; return 1; }
  found="$({ grep_7a "${files[@]}" && grep_7b "${spec[@]}" && grep_7c lakefile.toml; } 2>&1)" || rc=1
  [[ -z "$found" && $rc -eq 0 ]] || { echo "$found"; return 1; }
  # Lake prefers lakefile.lean to lakefile.toml; every check here reads lakefile.toml (step 2 refuses it too).
  [[ ! -e lakefile.lean ]] || { echo "  lakefile.lean exists"; return 1; }
  echo "  scanned ${#files[@]} library files, ${#spec[@]} Spec files, lakefile.toml"
}
selftest_grep() {
  set +e
  local rc=0
  [[ $(grep_7a "$FX/grep/Bad.lean" | wc -l) -ge 8 ]] && echo "  ok: 7a flags grep/Bad.lean" || { echo "  7a misses grep/Bad.lean"; rc=1; }
  [[ $(grep_7b "$FX/grep/BadSpecMeta.lean" | wc -l) -eq 4 ]] && echo "  ok: 7b flags grep/BadSpecMeta.lean" || { echo "  7b misses grep/BadSpecMeta.lean"; rc=1; }
  [[ $(grep_7c "$FX/grep/lakefile-bad.toml" | wc -l) -ge 2 ]] && echo "  ok: 7c flags grep/lakefile-bad.toml" || { echo "  7c misses grep/lakefile-bad.toml"; rc=1; }
  [[ -z "$(grep_7a "$FX/ReviewAxiomsGood.lean")" ]] && echo "  ok: 7a passes a clean file" || { echo "  7a flags a clean file"; rc=1; }
  grep_7a "$FX/grep/does-not-exist.lean" >/dev/null; [[ $? -eq 2 ]] && echo "  ok: a missing file is an error" || { echo "  a missing file is not an error"; rc=1; }
  set -e
  return "$rc"
}

# --- step 8: vendored files -----------------------------------------------------------------------
step_vendor() { sha256sum --strict -c scripts/vendor.sha256; }

# --- step 9: comparator config (jq glue; the real comparator.json is added in B4) ------------------
# comparator_config_ok <config.json> <statements file>: exactly the four keys, the challenge and
# solution modules, one theorem per Prop statement (`Consensus.Review.S` -> `Consensus.Review.s`),
# the three standard axioms, and no `definition_names`.
comparator_config_ok() {
  jq -e -s --rawfile st "$2" --arg ch "$CHALLENGE" --arg so "$SOLUTION" '
    def lowerfirst: (.[:1] | ascii_downcase) + .[1:];
    def thm: (split(".") | .[:-1] + [(.[-1] | lowerfirst)] | join("."));
    ([$st | split("\n")[] | select(length > 0) | thm] | sort) as $want
    | length == 1 and (.[0] | type) == "object" and (.[0]
    | (keys == ["challenge_module", "permitted_axioms", "solution_module", "theorem_names"])
    and .challenge_module == $ch and .solution_module == $so and $ch != $so
    and ($want | length) > 0
    and (.theorem_names | length) == (.theorem_names | unique | length)
    and (.theorem_names | sort) == $want
    and (.permitted_axioms | sort) == ["Classical.choice", "Quot.sound", "propext"])' "$1" >/dev/null
}
step_comparator_config() {
  if [[ ! -f comparator.json ]]; then echo "  NOTE  no comparator.json yet (wired in B4)"; return 0; fi
  "${SURFACE[@]}" statements --modules "$STATEMENTS" >"$WORK/statements.txt" &&
    comparator_config_ok comparator.json "$WORK/statements.txt"
}
selftest_comparator_config() {
  set +e
  local rc=0 c
  expect_pass comparator_config_ok "$FX/comparator/config-good.json" "$FX/comparator/statements.txt" || rc=1
  for c in same defnames axioms names extra challenge multi; do
    expect_fail - comparator_config_ok "$FX/comparator/config-$c.json" "$FX/comparator/statements.txt" || rc=1
  done
  expect_fail - comparator_config_ok "$FX/comparator/config-empty.json" "$FX/comparator/statements-empty.txt" || rc=1
  set -e
  return "$rc"
}

# --- steps 10, 11: lake check / lake comparator (bwrap sandbox; SKIP and listed CI-only without it) -----
have_bwrap() { command -v bwrap >/dev/null; }
step_lake_check() {
  set +e
  local rc=0
  lake check || rc=1
  # Rejected for the intended reason (the user axiom), not for a broken fixture or sandbox.
  expect_fail "error: Axiom 'ax' is not permitted; it is used by 't'" lake -d "$FX/lakecheck-bad" check || rc=1
  expect_pass lake -d "$FX/lakecheck-good" check || rc=1
  set -e
  return "$rc"
}
step_lake_comparator() { lake comparator --config comparator.json; }

# --- driver ---------------------------------------------------------------------------------------
overall=0
partial=()
ci_only=()
run_step() {
  local label="$1"
  shift
  echo "--- $label ---"
  if "$@"; then printf 'PASS  %s\n' "$label"; else printf 'FAIL  %s\n' "$label"; overall=1; fi
}
run_selftest() {
  if ((quick)); then echo "SKIP  $1 (skipped: --quick)"; partial+=("$1"); else run_step "$@"; fi
}
needs_bwrap() {
  if have_bwrap; then run_step "$@"; else echo "SKIP  $1 (skipped: no bwrap)"; ci_only+=("$1"); fi
}

run_step "0 pins (toolchain + dependencies = scripts/pins.toml)" step_pins
run_selftest "0 pins self-test (fixtures/pins-*)" selftest_pins
run_step "1 build ($( ((no_build)) && echo 'freshness only, --no-build' || echo 'default targets') + ${EXTRA_TARGETS[*]})" step_build
run_step "2 imports (check-imports.py)" step_imports
if [[ ! -s "$INV" ]]; then
  echo "check.sh: no inventory; the remaining steps need it"; echo; echo "check.sh: FAILURES PRESENT" >&2; exit 1
fi
run_selftest "2 imports self-test (fixtures/imports)" selftest_imports
run_step "3 declarations (check-decls per library)" step_decls
run_selftest "3 declarations self-test (test_check_decls.sh, OrphanLib, EmptyScope)" selftest_decls
run_step "4 Spec surface (extensions, snapshot, theorems, noconst)" step_surface
run_selftest "4 Spec surface self-test (CheckFixtures)" selftest_surface
if ((quick)); then
  echo "SKIP  5 kernel replay (skipped: --quick)"; partial+=("5 kernel replay")
else
  run_step "5 kernel replay (leanchecker, every leaf module)" step_replay
fi
run_selftest "5 kernel replay self-test (BadSkipKernel, prefix refusal)" selftest_replay
run_step "6 review pins ($REVIEW_ROOT imports $REVIEW_AXIOMS)" step_review
run_selftest "6 review pins self-test (review-imports, ReviewAxiomsBad, ReviewTypeBad, ReviewAxiomsGood)" selftest_review
run_step "7 backstop (grep)" step_grep
run_selftest "7 backstop self-test (fixtures/grep)" selftest_grep
run_step "8 vendored files (scripts/vendor.sha256)" step_vendor
run_step "9 comparator config" step_comparator_config
run_selftest "9 comparator config self-test (fixtures/comparator)" selftest_comparator_config
needs_bwrap "10 lake check" step_lake_check
# leanchecker skips the noconst-exempt parents (step 5); step 10's replay covers them, when it runs.
have_bwrap || ((${#NOCONST_EXEMPT[@]} == 0)) || ci_only+=("kernel replay of ${NOCONST_EXEMPT[*]} (lake check)")
if [[ -f comparator.json ]]; then
  needs_bwrap "11 lake comparator" step_lake_comparator
else
  echo "NOTE  11 lake comparator: no comparator.json yet (wired in B4)"
fi
echo "NOTE  12 docs: wired in B5"

echo
((${#ci_only[@]} == 0)) || echo "CI-only: ${ci_only[*]}"
if ((overall)); then
  echo "check.sh: FAILURES PRESENT" >&2
elif ((${#partial[@]})); then
  echo "check.sh: PASSED (partial: ${partial[*]})"
else
  echo "check.sh: ALL CHECKS PASSED"
fi
exit "$overall"
