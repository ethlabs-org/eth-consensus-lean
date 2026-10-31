#!/usr/bin/env bash
# The trust checks of consensus-lean, end to end. Structure copied from verified-consensus
# scripts/verify.sh (CC0-1.0): one function per step, each reporting PASS/FAIL/SKIP, then a summary.
# Every path and module list comes from scripts/boundaries.toml (layout) and the inventory that
# scripts/check-boundaries.py derives from it; nothing here is find-derived.
#
#   0  pins             toolchain + every dependency = scripts/pins.toml, and   (check-pins.py)
#                       Lake resolves exactly those checkouts (LEAN_PATH)
#   1  build            default targets + extras with --wfail --iofail; the     (lake; warn.sorry = false)
#                       deliberately bad fixture libraries without
#   2  boundaries       layer matrix, Init chain, roots, inventory (source)     (check-boundaries.py)
#   3  declarations     axioms/sorry/opaque/unsafe/extern/csimp per library;    (EthLib check-decls)
#                       `sorry` only in the `sorry = true` layers (Lemmas, Proofs)
#   3b axiom audit      Solution closure and tests: only the three standard     (axiom-audit)
#                       axioms (gate); unfinished declarations of the default library (report)
#   4  Spec surface     persisted extensions, snapshot, theorems, noconst,      (SpecSurface.lean)
#                       reach (report)
#   5  kernel replay    every leaf module of every checked library              (leanchecker)
#   6  review pins      ReviewAxioms compiled into the tests root               (#guard_msgs)
#   7  backstop         grep for sorry/admit outside the sorry layers (count inside them reported), proof `example`s,
#                       native_decide, kernel/debug options, Spec meta commands, lakefile options
#   8  vendored         sha256 of every vendored copy                           (scripts/vendor.sha256)
#   9  comparator config  exact comparator.json + Challenge.lean            (jq, lean --deps-json)
#   10 lake check       sandboxed build + export + replay; of the default       (needs bwrap)
#                       targets only while no sorry layer holds `sorry` (plan §5)
#   11 lake comparator  Spec statements vs proofs, axioms, sandboxed replay by  (needs bwrap)
#                       Lean's kernel and every bundled external kernel (--paranoid)
#   12 docs             README spec-file list = the files of the Spec surface (trusted layers);
#                       names cited in the docs are in the name index (built: they exist);  (check-docs.py)
#                       CODEOWNERS = trusted_paths + codeowners_extra
#   13 metrics          depth, cones, expose and import counts (report)          (metrics-baseline.py)
#   14 rebuild canary   a proof-only edit rebuilds one module (report); a        (lake; --full or --canary)
#                       statement edit (control) must make an importer stale
# Every step with a negative fixture also runs it through the same function ("self-test" steps).
#
# Usage: scripts/check.sh [--fast | --full [--split main|lake-check] | --changed [<base>]] [--selftests] [--reach] [--canary]
#                         [--no-build] [--update-snapshot] [--update-extensions]
#   --fast (default)     every step except the heavy ones (5 kernel replay, 10 lake check, 11 lake
#                        comparator) and the self-tests: CI on every pull request and push to main
#   --full               everything, self-tests included: CI nightly, on demand and on milestone/release tags
#   --split <part>       with --full, one of two parts run as parallel CI jobs: `lake-check` = step 0 (pins, with
#                        its self-test) and step 10, `main` = every other step; each prints DEFER for the other
#                        part's steps and ends with `check.sh: PART PASSED (split <part>; ...)`
#   --changed [<base>]   the fast steps restricted to what changed since <base> (default: merge-base with
#                        origin/main; uncommitted and untracked files count): build the changed modules'
#                        downstream cone, check-decls on the affected libraries, Spec surface only if a Spec
#                        module changed, grep on the changed files. A change of scripts/ or of the build
#                        configuration falls back to --fast (with --selftests for scripts/). scripts/check-changed.sh
#   --reach              in --fast mode, also run step 4's reach report (a report, not a gate)
#   --canary             in --fast mode, also run step 14 (CI passes it when the build configuration changed)
#   --selftests          also run the self-tests (fixtures) in --fast mode; with --changed, runs --fast
#   --no-build           do not compile; `lake build --no-build` still fails on anything stale
#   --update-snapshot    rewrite scripts/spec-snapshot.txt (the run then FAILS: review + commit it)
#   --update-extensions  rewrite scripts/spec-extensions.txt likewise
# Every skipped step prints `SKIP  <step> (<reason>)`; only --full ends with `check.sh: ALL CHECKS PASSED`.
# With CI set, --update-* and --no-build are refused.
# On the shared box run it only inside `job --mem 16G ...` (it refuses to start without RUN_DIR or CI).

set -euo pipefail
# Under pipefail, never end a pipeline in `grep -q` (or any reader that stops early): it exits on the first match, the
# producer gets SIGPIPE (141) and the pipeline counts as failed, at random on a busy machine. Let grep read all of
# its input instead: `producer | grep ... >/dev/null`.
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

usage="usage: scripts/check.sh [--fast | --full [--split main|lake-check] | --changed [<base>]] [--selftests] [--reach] [--canary] [--no-build] [--update-snapshot] [--update-extensions]"
mode=fast base="" split="" selftests=0 reach=0 canary=0 no_build=0 update_snapshot=0 update_extensions=0
while (($#)); do
  case "$1" in
    --fast) mode=fast ;;
    --full) mode=full ;;
    --split) (($# > 1)) || { echo "--split needs a part" >&2; exit 2; }; split="$2"; shift ;;
    --changed) mode=changed; if (($# > 1)) && [[ "$2" != -* ]]; then base="$2"; shift; fi ;;
    --selftests) selftests=1 ;;
    --reach) reach=1 ;;
    --canary) canary=1 ;;
    --no-build) no_build=1 ;;
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
if [[ -n "${CI:-}" ]] && ((no_build || update_snapshot || update_extensions)); then
  echo "check.sh: --no-build and --update-* are refused in CI" >&2
  exit 2
fi
[[ "$mode" == full ]] && selftests=1 canary=1
if [[ -n "$split" ]] && { [[ "$mode" != full ]] || [[ "$split" != main && "$split" != lake-check ]]; }; then
  echo "check.sh: --split takes main or lake-check, with --full only" >&2; exit 2
fi
# The reach report (step 4) runs in --full, in --changed whenever step 4 runs (a Spec module changed), and
# in --fast only with --reach (CI passes it when the Spec, the challenge or scripts/ changed).
[[ "$mode" != fast ]] && reach=1
# The self-tests need the fixture libraries, which the changed-mode build does not compile.
if [[ "$mode" == changed ]] && ((selftests)); then
  echo "check.sh: --changed --selftests runs --fast --selftests (the self-tests need the fixture builds; <base> ignored)"
  mode=fast
fi

CFG=scripts/boundaries.toml
WORK="$(mktemp -d "${RUN_DIR:-${TMPDIR:-/tmp}}/check.XXXXXX")"
INV="$WORK/inventory.tsv"
FX=scripts/fixtures
SURFACE=(lake exe spec-surface)  # scripts/SpecSurface.lean, compiled (lakefile); built by step 1

# cfg <key>: a list or string of [checks] (or a top-level key) of boundaries.toml, one item per line.
cfg() {
  python3 -I -c 'import sys, tomllib
c = tomllib.load(open(sys.argv[1], "rb")); k = sys.argv[2]
if k == "libs":
    v = [l["name"] for l in c["lib"]]
elif k in ("default_libs", "test_libs"):
    v = [l["name"] for l in c["lib"] if l.get("default" if k == "default_libs" else "test_driver") is True]
elif k in ("sorry_layers", "sorry_prefixes"):  # the layers where `sorry` may stay (plan §5), and their prefixes
    ls = [l for l in c["layer"] if l.get("sorry") is True]
    v = [l["name"] for l in ls] if k == "sorry_layers" else [p for l in ls for p in l["prefixes"]]
else:
    v = c["checks"][k] if k in c.get("checks", {}) else c[k]
sys.stdout.write("".join(x + "\n" for x in v) if isinstance(v, list) else v + "\n")' "$CFG" "$1"
}
mapfile -t LIBS < <(cfg libs)
mapfile -t DEFAULT_LIBS < <(cfg default_libs)
mapfile -t TEST_LIBS < <(cfg test_libs)
mapfile -t SORRY_LAYERS < <(cfg sorry_layers)
mapfile -t SORRY_PREFIXES < <(cfg sorry_prefixes)
SORRY_OK="${SORRY_PREFIXES[*]}"  # check-decls --sorry-ok prefixes (space-separated module names)
CANARY_MODULE="$(cfg canary_module)"
mapfile -t CANARY_PROOF < <(cfg canary_proof_edit)
mapfile -t CANARY_STMT < <(cfg canary_statement_edit)
SPEC_MODULES=()  # every module of the inventory in a trusted layer (the Spec surface); filled after step 2
mapfile -t EXTRA_TARGETS < <(cfg extra_build_targets)
mapfile -t FIXTURE_LIBS < <(cfg fixture_libs)
mapfile -t NOCONST_EXEMPT < <(cfg noconst_exempt)
mapfile -t DOC_NAME_FILES < <(cfg doc_name_files)
NAME_INDEX="$(cfg name_index_module)"
CODE_OWNER="$(cfg code_owner)"
mapfile -t OWNED_PATHS < <(cfg trusted_paths; cfg codeowners_extra)
THEOREMS_MODE="$(cfg theorems_mode)"
REVIEW_AXIOMS="$(cfg review_axioms_module)"
REVIEW_ROOT="$(cfg review_root)"
CHALLENGE="$(cfg challenge_module)"
SOLUTION="$(cfg solution_module)"
STATEMENTS="$(cfg statements_module)"
mapfile -t MILESTONE_STATEMENTS < <(cfg milestone_statements_modules)
COMPARATOR_STATEMENTS=("$STATEMENTS" "${MILESTONE_STATEMENTS[@]}")  # step 9: the challenge imports exactly these
case "$THEOREMS_MODE" in report|enforce) ;; *) echo "check.sh: theorems_mode must be report or enforce" >&2; exit 2 ;; esac
((${#LIBS[@]} > 0 && ${#DEFAULT_LIBS[@]} > 0 && ${#EXTRA_TARGETS[@]} > 0)) ||
  { echo "check.sh: empty configuration" >&2; exit 2; }

# --- what each mode checks ------------------------------------------------------------------------
BUILD_EXTRA=()            # extra targets built next to the default targets (set by the driver)
DECL_LIBS=("${LIBS[@]}")  # libraries whose every module check-decls checks (step 3; a lib's name is its scope)
CHANGED=()                # --changed: paths changed since $base (committed, staged, unstaged, untracked)
CONE=()                   # --changed: checked-library modules changed or (transitively) importing one
BUILD_TARGETS=()          # --changed: what step 1 builds
do_surface=1 do_comparator_config=1
do_audit=1 do_audit_tests=1 do_audit_report=1  # step 3b: the gates (solution closure, tests); the unfinished report

# compute_changes: the change set since $base and its downstream cone (--changed). Falls back to --fast
# (setting `mode`) where no sound restriction exists: the check stack or the build configuration changed.
compute_changes() {
  local f infra=() scripts_changed=0 tag lib m
  if [[ -z "$base" ]]; then
    base="$(git merge-base HEAD origin/main)" || { echo "check.sh: no merge-base with origin/main; pass a base" >&2; exit 2; }
  fi
  git rev-parse -q --verify "$base^{commit}" >/dev/null || { echo "check.sh: unknown base $base" >&2; exit 2; }
  # NUL-delimited: git quotes unusual file names in its line output.
  mapfile -d '' -t CHANGED < <({ git diff -z --no-renames --name-only "$base" --; git ls-files -z --others --exclude-standard; } | LC_ALL=C sort -zu)
  echo "--- changes since $(git rev-parse --short "$base") (committed, staged, unstaged and untracked) ---"
  ((${#CHANGED[@]})) && printf '  %s\n' "${CHANGED[@]}" || echo "  (none)"
  for f in "${CHANGED[@]}"; do
    case "$f" in
      scripts/*) scripts_changed=1; infra+=("$f") ;;
      lean-toolchain|lake-manifest.json|lakefile.toml|lakefile.lean) infra+=("$f") ;;
    esac
  done
  if ((${#infra[@]})); then
    mode=fast; ((scripts_changed)) && selftests=1
    for f in "${infra[@]}"; do [[ "$f" == scripts/* ]] || canary=1; done
    echo "  NOTE  the check stack or the build configuration changed (${#infra[@]} files): no sound restriction;"
    echo "        running --fast on everything$( ((scripts_changed)) && echo ', with the self-tests (scripts/ changed)')"
    return 0
  fi
  # Only the graph is used here (step 2 reports the findings); it is written whenever the imports parse.
  python3 -I scripts/check-boundaries.py --config "$CFG" --lakefile lakefile.toml --graph-out "$WORK/graph.tsv" >/dev/null 2>&1 || true
  if [[ ! -s "$WORK/graph.tsv" ]]; then
    mode=fast
    echo "  NOTE  no import graph (lean --deps-json failed; step 2 shows why): running --fast on everything"
    return 0
  fi
  # cone: the changed modules and every module importing one, transitively; lib: a library with a module
  # in the cone or a deleted file under its directory; spec: a module of a trusted layer in the cone, or a
  # deleted file under a prefix of such a layer.
  DECL_LIBS=()
  local spec_changed=0
  while IFS=$'\t' read -r tag lib m; do
    case "$tag" in
      cone) CONE+=("$m") ;;
      lib) DECL_LIBS+=("$lib") ;;
      spec) spec_changed=1 ;;
    esac
  done < <(python3 -I - "$WORK/graph.tsv" "$CFG" "${CHANGED[@]}" <<'PY'
import sys, tomllib
graph, cfg, changed = sys.argv[1], tomllib.load(open(sys.argv[2], "rb")), sys.argv[3:]
def under(m, p): return m == p or m.startswith(p + ".")
def in_spec(m):  # the layer prefixes never overlap (check-boundaries.py)
    return any(l.get("trusted") is True and under(m, p) for l in cfg.get("layer", []) for p in l.get("prefixes", []))
lib_of, rdeps = {}, {}
for line in open(graph):
    l, m, i = line.rstrip("\n").split("\t")
    lib_of[m] = l
    if i != "-":
        rdeps.setdefault(i, set()).add(m)
libs, todo = set(), []
for f in changed:
    if not f.endswith(".lean"):
        continue
    m = f[:-len(".lean")].replace("/", ".")
    if m in lib_of:
        todo.append(m)
    else:  # deleted (or outside the checked libraries)
        libs |= {x["name"] for x in cfg["lib"] if under(m, x["name"])}
        if in_spec(m):
            print("spec", "", "", sep="\t")
cone = set()
while todo:
    m = todo.pop()
    if m not in cone:
        cone.add(m)
        todo += rdeps.get(m, ())
for m in sorted(cone):
    print("cone", lib_of[m], m, sep="\t")
for l in sorted(libs | {lib_of[m] for m in cone}):
    print("lib", l, "", sep="\t")
if any(in_spec(m) for m in cone):
    print("spec", "", "", sep="\t")
PY
  )
  ((spec_changed)) || do_surface=0
  do_comparator_config=$do_surface
  for f in "${CHANGED[@]}"; do
    [[ "$f" == comparator.json || "$f" == "$(mod_file "$CHALLENGE")" ]] && do_comparator_config=1
  done
  printf '%s\n' "${CONE[@]}" | grep -xF "$SOLUTION" >/dev/null && do_comparator_config=1
  printf '%s\n' "${CONE[@]}" | grep -xF "$SOLUTION" >/dev/null || do_audit=0
  printf '%s\n' "${CONE[@]}" | grep -xF -f <(printf '%s\n' "${TEST_LIBS[@]}" | awk NF) >/dev/null || do_audit_tests=0
  printf '%s\n' "${CONE[@]}" | grep -xF -f <(printf '%s\n' "${DEFAULT_LIBS[@]}") >/dev/null || do_audit_report=0
  BUILD_TARGETS=("${CONE[@]}")
  ((do_audit || do_audit_tests || do_audit_report)) && BUILD_TARGETS+=(axiom-audit)
  ((do_comparator_config)) && BUILD_TARGETS+=("$CHALLENGE")
  ((${#DECL_LIBS[@]})) && BUILD_TARGETS+=(check-decls)
  # steps 4 (Spec surface, or noconst alone for any Lean change) and 9 call it
  ((do_surface || do_comparator_config || ${#DECL_LIBS[@]})) && BUILD_TARGETS+=(spec-surface)
  echo "  downstream cone (built): ${#CONE[@]} modules"
  ((${#CONE[@]})) && printf '    %s\n' "${CONE[@]}"
  echo "  affected libraries (check-decls): ${DECL_LIBS[*]:-none}"
  return 0
}

# Inventory queries (written by step 2: lib, module, leaf|parent, layer, trusted|-): modules of a library;
# modules of the trusted layers (the Spec surface); leaf or parent modules of all libraries.
inv_modules() { awk -F'\t' -v l="$1" '$1 == l { print $2 }' "$INV"; }
inv_trusted() { awk -F'\t' '$5 == "trusted" { print $2 }' "$INV"; }
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
expect_silent() {  # exit 0 and no output (no warning, no message)
  local out
  if out="$("$@" 2>&1)" && [[ -z "$out" ]]; then echo "  ok (exit 0, no output): $*"; return 0; fi
  echo "  expected exit 0 and no output: $*"; echo "$out" | tail -20; return 1
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
  local rc=0 want lp lib probe
  local -a env_info=()
  # What Lake actually resolves (overrides, path dependencies, packagesDir) is in LEAN_PATH.
  # Load Lake once, not three times; still ask its selected Lean for the library and version.
  probe="$(lake env bash -ec 'printenv LEAN_PATH; lean --print-libdir; lean --version')" || { echo "  no Lake environment"; rc=1; }
  mapfile -t env_info <<<"$probe"
  lp="${env_info[0]:-}" lib="${env_info[1]:-}"
  pins_check lean-toolchain lake-manifest.json .lake/package-overrides.json lakefile.toml \
    --lean-path "$lp" --libdir "$lib" || rc=1
  want="$(python3 -I -c 'import tomllib; print(tomllib.load(open("scripts/pins.toml", "rb"))["lean_version"])')"
  if ! grep -F "version $want," <<<"${env_info[2]:-}" >/dev/null; then
    echo "  lean --version is not $want: ${env_info[2]:-missing}"; rc=1
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
# bad_fixture <target>: a deliberately bad fixture library (any fixture lib except the challenge): built
# without --wfail (its warnings are expected); everything else fails on any warning or info message.
# `warn.sorry = false` (lakefile) keeps `sorry` silent: where it may stay is steps 3, 3b and 7's business.
bad_fixture() { [[ "$1" != "$CHALLENGE" ]] && printf '%s\n' "${FIXTURE_LIBS[@]}" | grep -xF "$1" >/dev/null; }
build_strict() { lake build --wfail --iofail "$@"; }  # step 1 and its self-test
step_build() {  # default targets + BUILD_EXTRA; --changed: BUILD_TARGETS only
  set +e
  local rc=0 nb=() strict=() loose=() t
  ((no_build)) && nb=(--no-build)
  if [[ "$mode" == changed ]]; then
    build_strict "${nb[@]}" "${BUILD_TARGETS[@]}" || rc=1
  else
    build_strict "${nb[@]}" || rc=1
    for t in "${BUILD_EXTRA[@]}"; do
      if bad_fixture "$t"; then loose+=("$t"); else strict+=("$t"); fi
    done
    ((${#strict[@]} == 0)) || build_strict "${nb[@]}" "${strict[@]}" || rc=1
    ((${#loose[@]} == 0)) || lake build "${nb[@]}" "${loose[@]}" || rc=1
  fi
  set -e
  return "$rc"
}
# --wfail fails on a warning, also when Lake replays it from a built module (CheckFixtures.Warn is built by
# step 1); `warn.sorry = false` lets `sorry` pass it (CheckFixtures.SorryQuiet). With a machine-wide Lake artifact
# cache (the shared box, #39) step 1 may have restored the fixture from the cache, with a trace that holds no log,
# so nothing would replay: the self-test drops the fixture's trace and builds with the cache off, so it compiles.
selftest_build() {
  set +e
  local rc=0
  local -x LAKE_ARTIFACT_CACHE=false
  rm -f .lake/build/lib/lean/CheckFixtures/Warn.trace
  expect_fail 'has been deprecated' build_strict CheckFixtures.Warn || rc=1
  expect_pass lake build CheckFixtures.Warn || rc=1
  expect_pass build_strict CheckFixtures.SorryQuiet || rc=1
  set -e
  return "$rc"
}

# --- step 2: boundaries ---------------------------------------------------------------------------
step_boundaries() {
  set +e
  python3 -I scripts/check-boundaries.py --config "$CFG" --lakefile lakefile.toml --inventory-out "$INV"
  local rc=$?
  set -e
  [[ $rc -eq 0 && -s "$INV" ]] || { echo "  no inventory: every later step needs it"; return 1; }
  # Every module named in [checks] must be in the inventory (a typo would silently check less).
  local m l bad=0
  [[ -n "$(inv_trusted)" ]] || { echo "  FAIL[config] no module in a trusted layer"; bad=1; }
  for m in "$REVIEW_AXIOMS" "$REVIEW_ROOT" "${COMPARATOR_STATEMENTS[@]}" "$SOLUTION"; do
    cut -f2 "$INV" | grep -xF "$m" >/dev/null || { echo "  FAIL[config] $m (boundaries.toml [checks]) is not in the inventory"; bad=1; }
  done
  for m in "${NOCONST_EXEMPT[@]}"; do
    inv_kind parent | grep -xF "$m" >/dev/null || { echo "  FAIL[config] noconst_exempt $m is not a module with descendants"; bad=1; }
  done
  # The statements modules are frozen by the tag (step 9's challenge imports exactly them): the review
  # statements module is in a trusted layer, each milestone statements module's file is under `trusted_paths`.
  inv_trusted | grep -xF "$STATEMENTS" >/dev/null || { echo "  FAIL[config] $STATEMENTS is not in a trusted layer"; bad=1; }
  for m in "${MILESTONE_STATEMENTS[@]}"; do
    l="$(mod_file "$m")"
    cfg trusted_paths | awk -v f="$l" '$0 == f || index(f, $0 "/") == 1 { ok = 1 } END { exit !ok }' ||
      { echo "  FAIL[config] $l (milestone_statements_modules) is not under trusted_paths"; bad=1; }
  done
  # The canary's edits (step 14, which runs only with --full or --canary) still apply: each `old` occurs once.
  canary_applies || bad=1
  return "$bad"
}
selftest_boundaries() { python3 -I scripts/check-boundaries.py --self-test "$FX/boundaries"; }

# --- step 3: declarations (EthLib check-decls) ----------------------------------------------------
# decls_scope <scope> <baseline> <modules...>: one check-decls process importing every given module;
# fails on any finding, on a stale baseline entry, and on an empty scope (`0 declarations`). A `sorry` at a
# declaration of a module under a prefix in SORRY_OK (the sorry layers) is listed, not a finding (local patch).
decls_scope() {
  local scope="$1" baseline="$2" out rc n p ok=()
  shift 2
  (($# > 0)) || { echo "  no modules for scope $scope"; return 1; }
  for p in $SORRY_OK; do ok+=(--sorry-ok "$p"); done
  out="$(lake exe check-decls --scope "$scope" --baseline "$baseline" "${ok[@]}" "$@" 2>&1)" && rc=0 || rc=$?
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
  local inv="$1" baseline="$2"
  shift 2
  split_baseline "$baseline" "$WORK/bl" "$@" && decls_each "$inv" "$@"
}
decls_each() {  # decls_each <inventory> <libs...>: needs the split baseline in $WORK/bl
  local inv="$1" rc=0 l
  shift
  for l in "$@"; do
    mapfile -t mods < <(awk -F'\t' -v l="$l" '$1 == l { print $2 }' "$inv")
    echo "  check-decls --scope $l (${#mods[@]} modules)"
    decls_scope "$l" "$WORK/bl/baseline.$l" "${mods[@]}" || rc=1
  done
  return "$rc"
}
# The baseline is validated against every library; --changed checks only the affected ones (DECL_LIBS).
step_decls() { split_baseline scripts/check_decls_baseline.txt "$WORK/bl" "${LIBS[@]}" && decls_each "$INV" "${DECL_LIBS[@]}"; }
decls_scope_ok() { local SORRY_OK="$1"; shift; decls_scope "$@"; }  # decls_scope with other --sorry-ok prefixes
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
  # A checked definition reaching an opaque constant only through an unchecked definition (an exempt
  # `Proofs` one, a formatting instance) is reported.
  out="$(decls_scope CheckFixtures.HiddenOpaque /dev/null CheckFixtures.HiddenOpaque.Use 2>&1)" &&
    { echo "  HiddenOpaque passed"; rc=1; }
  for f in 'reaches-opaque CheckFixtures.HiddenOpaque.Use.user:' 'reaches-opaque CheckFixtures.HiddenOpaque.Use.user2:'; do
    grep -qF "$f" <<<"$out" && echo "  ok: HiddenOpaque reports ${f%:}" || { echo "  HiddenOpaque misses ${f%:}"; rc=1; }
  done
  # BadSkipKernel passes check-decls (no axiom): only kernel replay (step 5) rejects it.
  expect_pass decls_scope CheckFixtures.BadSkipKernel /dev/null CheckFixtures.BadSkipKernel.A || rc=1
  # `sorry` placement: allowed under a --sorry-ok prefix (listed), a finding elsewhere and without the prefix.
  local fxok=CheckFixtures.SorryPlace.Lemmas
  out="$(decls_scope_ok "$fxok" CheckFixtures.SorryPlace /dev/null CheckFixtures.SorryPlace.Lemmas.A 2>&1)" &&
    grep -qF 'allowed sorry CheckFixtures.SorryPlace.Lemmas.A.t' <<<"$out" &&
    echo "  ok: a sorry under $fxok passes and is listed" || { echo "  SorryPlace.Lemmas: $out" | tail -5; rc=1; }
  expect_fail 'sorry CheckFixtures.SorryPlace.Spec.t' \
    decls_scope_ok "$fxok" CheckFixtures.SorryPlace /dev/null CheckFixtures.SorryPlace.Lemmas.A CheckFixtures.SorryPlace.Spec || rc=1
  expect_fail 'sorry CheckFixtures.SorryPlace.Lemmas.A.t' \
    decls_scope_ok "" CheckFixtures.SorryPlace /dev/null CheckFixtures.SorryPlace.Lemmas.A || rc=1
  set -e
  return "$rc"
}

# --- step 3b: axiom audit (leanprover-community/axiom-audit, vendored) ----------------------------
# audit_closure <module> <roots...>: every declaration of a module under each root, in the import closure of
# <module>, depends only on propext, Classical.choice and Quot.sound: `sorry` (sorryAx), native_decide
# (Lean.ofReduceBool) and declared axioms fail, directly or through imports. An empty audit fails too.
audit_closure() {
  local m="$1" r rc=0
  shift
  for r in "$@"; do
    lake exe axiom-audit --root "$r" --modules "$m" || rc=1
  done
  return "$rc"
}
# audit_report <root> <modules,...>: the declarations under <root> (in the closure of the modules) that depend on
# sorryAx (unfinished) or another non-standard axiom. A report: it fails only when the tool cannot run.
audit_report() {
  local out rc
  out="$(lake exe axiom-audit --root "$1" --modules "$2" --json 2>&1)" && rc=0 || rc=$?
  if ((rc > 1)) || ! grep -q '^{' <<<"$out"; then
    echo "$out" | tail -5; echo "  axiom-audit could not run (exit $rc)"; return 1
  fi
  grep '^{' <<<"$out" | tail -1 | python3 -I -c 'import json, sys
r = json.load(sys.stdin)
if r["audited"] == 0: sys.exit("  axiom-audit audited 0 declarations under %s: miswired root or modules" % r["root"])
v = r["violations"]
unfinished = sorted(x["decl"] for x in v if "sorryAx" in x["axioms"])
other = sorted(x["decl"] + " -> " + ", ".join(x["axioms"]) for x in v if x["axioms"] != ["sorryAx"])
print("  NOTE  unfinished (report): %d of the %d declarations under %s depend on sorryAx" % (len(unfinished), r["audited"], r["root"]))
for d in unfinished[:50]: print("    " + d)
if len(unfinished) > 50: print("    ... and %d more" % (len(unfinished) - 50))
if other: print("  NOTE  %d depend on another non-standard axiom (step 3 fails them):" % len(other))
for d in other[:50]: print("    " + d)'
}
step_audit() {
  set +e
  local rc=0 r
  if ((do_audit)); then
    echo "  gate: the import closure of $SOLUTION (roots: ${DEFAULT_LIBS[*]} $SOLUTION)"
    audit_closure "$SOLUTION" "${DEFAULT_LIBS[@]}" "$SOLUTION" || rc=1
  else
    echo "  NOTE  gate not run: nothing in the closure of $SOLUTION changed"
  fi
  # A test, witness or rejection built on an unfinished lemma would prove nothing: no test declaration may
  # depend on sorryAx (or another non-standard axiom), also through an import. Main and the instances may
  # (plan §5: they are not certified); the report lists them.
  if ((do_audit_tests)); then
    for r in "${TEST_LIBS[@]}"; do
      echo "  gate: every declaration of the tests $r"
      audit_closure "$r" "$r" || rc=1
    done
  else
    echo "  NOTE  tests gate not run: no test module changed"
  fi
  if ((do_audit_report)); then
    for r in "${DEFAULT_LIBS[@]}"; do audit_report "$r" "$r" || rc=1; done
  else
    echo "  NOTE  report not run: no module of ${DEFAULT_LIBS[*]} changed"
  fi
  set -e
  return "$rc"
}
# Fixtures CheckFixtures.Audit.*: a solution with a direct sorry, one reaching a sorry through an import, one with
# a declared axiom and one with native_decide each fail; a clean one passes, and a sorry outside its closure
# (Outside) does not fail it but is listed by the report.
selftest_audit() {
  set +e
  local rc=0 fx=CheckFixtures.Audit out
  expect_pass audit_closure $fx.SolGood $fx || rc=1
  expect_fail "$fx.SolDirect.s → [sorryAx]" audit_closure $fx.SolDirect $fx || rc=1
  expect_fail "$fx.Lemma.helper → [sorryAx]" audit_closure $fx.SolTransitive $fx || rc=1
  expect_fail "$fx.SolTransitive.s → [sorryAx]" audit_closure $fx.SolTransitive $fx || rc=1
  # As the tests gate runs it (the root is the module itself): the sorry comes from outside the root.
  expect_fail "$fx.SolTransitive.s → [sorryAx]" audit_closure $fx.SolTransitive $fx.SolTransitive || rc=1
  expect_fail "$fx.SolAxiom.s → [$fx.SolAxiom.ax]" audit_closure $fx.SolAxiom $fx || rc=1
  # native_decide's auxiliary axiom (v4.35: a private `<decl>._native.native_decide.ax_*`), not Lean.ofReduceBool.
  expect_fail "$fx.SolNative.s → [_private.$fx.SolNative.0.$fx.SolNative.s._native.native_decide.ax_" \
    audit_closure $fx.SolNative $fx || rc=1
  expect_fail 'audited 0 declaration' audit_closure $fx.SolGood CheckFixtures.Nowhere || rc=1
  out="$(audit_report $fx "$fx.SolGood,$fx.Outside")" && grep -qF "    $fx.Outside.o" <<<"$out" &&
    grep -qF 'NOTE  unfinished (report): 1 of the' <<<"$out" &&
    echo "  ok: the report lists the sorry outside the closure" || { echo "  report: $out"; rc=1; }
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
  local rc=0 ext_mods=("${SPEC_MODULES[@]}")
  echo "  extensions over the ${#ext_mods[@]} modules of the trusted layers"
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
    echo "  NOTE  theorems in report mode: $(grep -c '^REPORT' "$WORK/theorems-report.txt") ranged theorems in Spec modules"
  fi
  # Report (not a gate): which Spec definitions the review statements reach.
  local seeds=() n_unreached
  if ((!reach)); then
    echo "  NOTE  reach (report) not run: --fast without --reach (it runs with --full, or when the Spec changed)"
  elif "${SURFACE[@]}" statements --modules "$STATEMENTS" >"$WORK/statements-reach.txt" &&
      mapfile -t seeds <"$WORK/statements-reach.txt" && ((${#seeds[@]} > 0)) &&
      "${SURFACE[@]}" reach --from "${seeds[@]}" --modules "${SPEC_MODULES[@]}" >"$WORK/reach.txt"; then
    n_unreached="$(grep -c '^UNREACHED' "$WORK/reach.txt")"
    echo "  NOTE  reach (report): the ${#seeds[@]} statements reach $(grep -vc '^UNREACHED' "$WORK/reach.txt") Spec constants; $n_unreached ranged Spec definitions are not reached (listed below)"
    grep '^UNREACHED' "$WORK/reach.txt" | sed 's/^/    /'
  else
    echo "  reach failed"; rc=1
  fi
  step_noconst || rc=1
  set -e
  return "$rc"
}
# noconst: no module with descendants (of any checked library) owns a constant (leanchecker, step 5,
# replays leaves only). Part of step 4; --changed runs it alone when no Spec module changed.
step_noconst() {
  local parents=()
  mapfile -t parents < <(inv_kind parent | grep -vxF -f <(printf '%s\n' "${NOCONST_EXEMPT[@]}" | awk NF) )
  echo "  noconst over ${#parents[@]} modules with descendants"
  ((${#NOCONST_EXEMPT[@]} == 0)) ||
    echo "  NOTE  exempt from noconst, hence not replayed by leanchecker here (step 10 lake check replays them): ${NOCONST_EXEMPT[*]}"
  "${SURFACE[@]}" noconst --modules "${parents[@]}"
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
  if [[ -n "$d" ]] && ! grep -E '^[<>] ' <<<"$d" | grep -vE '^[<>]   #' >/dev/null; then
    echo "  ok: SnapA/SnapHidden differ only in a hash line"
  else echo "  SnapA/SnapHidden: expected only a hash difference: $d"; rc=1; fi
  # SnapAux: an unranged auxiliary line differs (same readable lines).
  snap_differs CheckFixtures.SnapAuxA.Defs CheckFixtures.SnapAuxB.Defs d || rc=1
  if [[ -n "$d" ]] && ! grep -E '^[<>] ' <<<"$d" | grep -vE '^[<>] [a-z]+ [^ ]+ #' >/dev/null; then
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
  return 0
}
SEARCH_PATH=()
# Up to REPLAY_JOBS leaves at once, each still one module per leanchecker process. Each process is dominated by
# loading its environment (~3 s load vs ms of replay) and peaks at ~3.3 GB. Default: what the CPUs and memory
# available to this process allow (its cgroup's cpu.max and memory.max where set, else nproc and MemTotal),
# 3 GB per process, at least 1: 2 on the 2-vCPU / 7 GB CI runner (as before, #13), 5 in a 16 GB / 8-CPU box job.
# Output is printed per leaf, in order.
replay_jobs_default() {
  local cg cpus mem q p
  cg="/sys/fs/cgroup$(awk -F: '$1 == "0" { print $3 }' /proc/self/cgroup 2>/dev/null)"
  cpus="$(nproc)"
  if read -r q p 2>/dev/null <"$cg/cpu.max" && [[ "$q" =~ ^[0-9]+$ ]] && ((p > 0)); then
    q=$(((q + p - 1) / p)); ((q < cpus)) && cpus=$q
  fi
  mem="$(awk '/^MemTotal:/ { print $2 * 1024 }' /proc/meminfo)"
  if read -r q 2>/dev/null <"$cg/memory.max" && [[ "$q" =~ ^[0-9]+$ ]] && ((q < mem)); then mem=$q; fi
  q=$((mem / (3 * 1024 * 1024 * 1024)))
  ((q < cpus)) && cpus=$q
  echo $((cpus > 0 ? cpus : 1))
}
step_replay() {
  set +e
  local rc=0 m i k=0 n=0 kb peak=0 start=$SECONDS njobs="${REPLAY_JOBS:-$(replay_jobs_default)}" pids=()
  [[ "$njobs" =~ ^[1-9][0-9]*$ ]] || { echo "  REPLAY_JOBS must be a positive integer, not '$njobs'"; return 1; }
  load_search_path || { echo "  cannot determine the Lean search path"; return 1; }
  mapfile -t leaves < <(inv_kind leaf)
  ((${#leaves[@]} > 0)) || { echo "  no leaf modules"; return 1; }
  for i in "${!leaves[@]}"; do
    replay_leaf "${leaves[i]}" >"$WORK/replay.$i.out" 2>&1 &
    pids+=("$!")
    while ((${#pids[@]} - k >= njobs)); do
      wait "${pids[k]}" || rc=1; cat "$WORK/replay.$k.out"; k=$((k + 1))
    done
  done
  while ((k < ${#pids[@]})); do
    wait "${pids[k]}" || rc=1; cat "$WORK/replay.$k.out"; k=$((k + 1))
  done
  for m in "${leaves[@]}"; do
    n=$((n + 1))
    # The last line is "<KB> <s>"; a rejected leaf's file starts with GNU time's exit-status line.
    kb="$(tail -n 1 "$WORK/time.$m" 2>/dev/null | cut -d' ' -f1)"
    [[ "$kb" =~ ^[0-9]+$ ]] && ((kb > peak)) && peak=$kb
  done
  echo "  NOTE  leanchecker: $n leaf modules, $njobs at a time, $((SECONDS - start))s total, peak $((peak / 1024)) MB per process"
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
  expect_pass lake env lean "$FX/ReviewAxiomsGood.lean" || rc=1
  # The alpha-equality and completeness guards (ConsensusLeanTest/ReviewGuard.lean) on fixtures.
  expect_fail 'is not alpha-equal' lake env lean "$FX/ReviewEqBad.lean" || rc=1
  expect_fail 'does not have the binder kinds' lake env lean "$FX/ReviewBinderBad.lean" || rc=1
  # Statements in another namespace, `eq_1`, `_Extra` and `private` ones all need a pair: in the
  # current file, and in an imported module (`import all`, as the production file does).
  expect_fail 'no review pair for [CheckFixtures.Elsewhere.Extra, CheckFixtures.ReviewCompleteBad.Extra, CheckFixtures.ReviewCompleteBad._Extra, CheckFixtures.ReviewCompleteBad.eq_1, _private.scripts.fixtures.ReviewCompleteBad.0.CheckFixtures.ReviewCompleteBad.Priv]' \
    lake env lean "$FX/ReviewCompleteBad.lean" || rc=1
  expect_fail 'no review pair for [CheckFixtures.Elsewhere.Extra, CheckFixtures.ReviewEscape._Extra, CheckFixtures.ReviewEscape.eq_1, _private.CheckFixtures.ReviewEscape.0.CheckFixtures.ReviewEscape.Priv]' \
    lake env lean "$FX/ReviewEscapeBad.lean" || rc=1
  expect_silent lake env lean "$FX/ReviewGuardGood.lean" || rc=1
  # The production pins file, on temporary copies: unchanged it passes; without one pair, or with a
  # misspelt module, it fails (no vacuous pass).
  local f="$(mod_file "$REVIEW_AXIOMS")" d="$WORK/review-mut"
  mkdir -p "$d"
  cp "$f" "$d/Same.lean"
  grep -v '``Consensus.Review.HeldIffServed, ``Consensus.Model.Run.held_iff_served' "$f" |
    sed 's/``Consensus.Model.sysOf_log_faithful),/``Consensus.Model.sysOf_log_faithful)]/' >"$d/DropPair.lean"
  sed "s/checkComplete \`$STATEMENTS pairs/checkComplete \`${STATEMENTS}X pairs/" "$f" >"$d/Typo.lean"
  if cmp -s "$f" "$d/DropPair.lean" || cmp -s "$f" "$d/Typo.lean"; then
    echo "  a mutation of $f did not apply (its text changed: update the self-test)"; rc=1
  fi
  expect_silent lake env lean "$d/Same.lean" || rc=1
  expect_fail 'no review pair for [Consensus.Review.HeldIffServed]' lake env lean "$d/DropPair.lean" || rc=1
  expect_fail "module ${STATEMENTS}X is not imported" lake env lean "$d/Typo.lean" || rc=1
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
grep_7a() {  # every library file
  local r=0
  scan 'native_decide|admitGoal|sorryAx|mkSorry|mkLabeledSorry' -w "$@" || r=2
  scan 'skipKernelTC|decide \+native|debug\.[A-Za-z]' "$@" || r=2
  return "$r"
}
grep_sorry() { scan 'sorry|admit' -w "$@"; }  # the library files outside the sorry layers
# layer_files <inventory> <in|out> <layers...>: the files of the inventory's modules in (or outside) the layers.
layer_files() {
  local inv="$1" which="$2"
  shift 2
  awk -F'\t' -v which="$which" -v ls="$*" 'BEGIN { n = split(ls, a, " "); for (i = 1; i <= n; i++) s[a[i]] = 1 }
    (which == "in") == ($4 in s) { print $2 }' "$inv" | while read -r m; do mod_file "$m"; done
}
# lean_scan <sorry|example> <count|lines> <files...>: Lean source with comments (nested block comments and
# docstrings, line comments) removed, and string, raw string and char literals (interpolations included) masked;
# a name literal (`sorry) is not a match.
# `sorry`: the tokens sorry and admit. `example`: an `example` other than a bare `example := @Name` (or ``Name) reference
# (nothing after the name but the next command at column 0, or the end of the file: an argument must be
# indented, so none can follow). An example never enters the environment, so neither check-decls nor the axiom
# audit sees its proof (one built on an unfinished lemma would pass unseen). Prints the number of matches
# (count) or each as file:line: text (lines); fails on an unreadable file.
lean_scan() {
  python3 -I - "$@" <<'PY'
import re, sys
pats = {"sorry": r"(?<![\w.'`])(?:sorry|admit)(?![\w'!?])", "example": r"(?<![\w.'`])example(?![\w'!?])"}
ref = re.compile(r"example[ \t]*:=[ \t]*(?:@|``)[\w.'«»!?₀-₉]+[ \t]*(?:\n\s*)*")
def bare_ref(code, at):  # `example := @Name` or ``Name, then only the next command (a column-0 word, `#`, `@[`) or the end
    r = ref.match(code, at)
    if not r: return False
    k = r.end()
    return k == len(code) or (code[k - 1] == "\n" and (re.match(r"[A-Za-z_#]", code[k]) or code.startswith("@[", k)))
pat, mode, n = re.compile(pats[sys.argv[1]]), sys.argv[2], 0
L = "\x01"  # what a literal's characters become: no token, but not blank either (an argument stays visible)
for f in sys.argv[3:]:
    src, out, i, depth = open(f).read(), [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth, i = depth + 1, i + 2; out.append("  ")
        elif depth and src.startswith("-/", i): depth, i = depth - 1, i + 2; out.append("  ")
        elif depth: out.append("\n" if src[i] == "\n" else " "); i += 1
        elif src.startswith("--", i): i = src.find("\n", i) if "\n" in src[i:] else len(src)
        elif (c := re.compile(r"(?<![\w'.])'(?:\\.|[^\\'\n])'").match(src, i)):  # a char literal
            out.append(L * (c.end() - i)); i = c.end()
        elif (r := re.compile(r'(?<![\w.])r(#*)"').match(src, i)):  # a raw string r"...", r#"..."#
            j = src.find('"' + r.group(1), r.end())
            j = len(src) if j < 0 else j + 1 + len(r.group(1))
            out.append("".join(c if c == "\n" else L for c in src[i:j])); i = j
        elif src[i] == '"':  # a string literal (escapes skipped), newlines kept
            j = i + 1
            while j < len(src) and src[j] != '"': j += 2 if src[j] == "\\" else 1
            out.append("".join(c if c == "\n" else L for c in src[i:j + 1])); i = j + 1
        else: out.append(src[i]); i += 1
    code = "".join(out)
    for m in pat.finditer(code):
        if sys.argv[1] == "example" and bare_ref(code, m.start()): continue
        n += 1
        ln = code.count("\n", 0, m.start()) + 1
        if mode == "lines": print(f"{f}:{ln}: {src.split(chr(10))[ln - 1].strip()}")
if mode == "count": print(n)
PY
}
# sorry_count <inventory>: the sorry/admit tokens in the files of the sorry layers, comments removed: what step 7
# reports and step 10 decides by.
sorry_count() {
  local lax=()
  mapfile -t lax < <(layer_files "$1" in "${SORRY_LAYERS[@]}")
  lean_scan sorry count "${lax[@]}"
}
grep_7b() { scan 'run_cmd|run_meta|run_elab|#eval|#exit|(builtin_)?initialize' -w "$@"; }
grep_7c() { scan 'skipKernelTC|plugins|moreLeanArgs|weakLeanArgs|moreServerArgs|loadDynlib|dynlibs|precompileModules|debug\.' "$@"; }
only_changed() {  # only_changed <paths...>: those in CHANGED
  awk 'NR == FNR { c[$0] = 1; next } $0 in c' <(printf '%s\n' "${CHANGED[@]}") <(printf '%s\n' "$@")
}
step_grep() {
  local files=() spec=() strict=() found rc=0 what="" n
  mapfile -t files < <(cut -f2 "$INV" | while read -r m; do mod_file "$m"; done)
  mapfile -t spec < <(for m in "${SPEC_MODULES[@]}"; do mod_file "$m"; done)
  ((${#files[@]} > 0 && ${#spec[@]} > 0)) || { echo "  no files to scan"; return 1; }
  if [[ "$mode" == changed ]]; then
    mapfile -t files < <(only_changed "${files[@]}")
    mapfile -t spec < <(only_changed "${spec[@]}")
    what=" (changed files only)"
  fi
  mapfile -t strict < <(layer_files "$INV" out "${SORRY_LAYERS[@]}")
  [[ "$mode" != changed ]] || mapfile -t strict < <(only_changed "${strict[@]}")
  found="$({ { ((${#files[@]} == 0)) || grep_7a "${files[@]}"; } &&
    { ((${#strict[@]} == 0)) || grep_sorry "${strict[@]}"; } &&
    { ((${#files[@]} == 0)) || lean_scan example lines "${files[@]}"; } &&
    { ((${#spec[@]} == 0)) || grep_7b "${spec[@]}"; } && grep_7c lakefile.toml; } 2>&1)" || rc=1
  [[ -z "$found" && $rc -eq 0 ]] || { echo "$found"; return 1; }
  # Lake prefers lakefile.lean to lakefile.toml; every check here reads lakefile.toml (step 2 refuses it too).
  [[ ! -e lakefile.lean ]] || { echo "  lakefile.lean exists"; return 1; }
  echo "  scanned ${#files[@]} library files (sorry/admit: the ${#strict[@]} outside the sorry layers ${SORRY_LAYERS[*]}; no proof \`example\`), ${#spec[@]} Spec files$what, lakefile.toml"
  n="$(sorry_count "$INV")" || { echo "  cannot count sorry in the sorry layers"; return 1; }
  echo "  NOTE  sorry/admit in the sorry layers (report, every file, comments removed): $n"
}
selftest_grep() {
  set +e
  local rc=0 out
  [[ $(grep_7a "$FX/grep/Bad.lean" | wc -l) -eq 7 ]] && echo "  ok: 7a flags grep/Bad.lean" || { echo "  7a misses grep/Bad.lean"; rc=1; }
  [[ $(grep_sorry "$FX/grep/Bad.lean" | wc -l) -eq 2 ]] && echo "  ok: sorry/admit flagged in grep/Bad.lean" || { echo "  sorry/admit missed in grep/Bad.lean"; rc=1; }
  # Placement, through the inventory: a sorry in a Spec file is flagged, the one in a Lemmas file only counted.
  printf 'Fx\tscripts.fixtures.grep.sorry.Lemmas\tleaf\tLemmas\t-\nFx\tscripts.fixtures.grep.sorry.Spec\tleaf\tSpec\ttrusted\n' >"$WORK/fx-sorry-inv.tsv"
  out="$(layer_files "$WORK/fx-sorry-inv.tsv" out "${SORRY_LAYERS[@]}")"
  [[ "$out" == "$FX/grep/sorry/Spec.lean" ]] && [[ $(grep_sorry "$out" | wc -l) -eq 1 ]] &&
    echo "  ok: only the Spec fixture's sorry is outside the sorry layers" || { echo "  placement: '$out'"; rc=1; }
  [[ "$(sorry_count "$WORK/fx-sorry-inv.tsv")" == 1 ]] && echo "  ok: the Lemmas fixture's sorry is counted, its comments are not" ||
    { echo "  sorry_count: $(sorry_count "$WORK/fx-sorry-inv.tsv")"; rc=1; }
  out="$(lean_scan example lines "$FX/grep/Example.lean")"
  [[ "$out" == "$FX/grep/Example.lean:4: example : 1 = 1 := rfl
$FX/grep/Example.lean:6: example := @id (0 = 0) rfl
$FX/grep/Example.lean:7: example := @id
$FX/grep/Example.lean:11: example : 5 = 5 := rfl
$FX/grep/Example.lean:12: example := @id<|rfl
$FX/grep/Example.lean:13: example := @Nat.succ \"x\"
$FX/grep/Example.lean:14: example := @Nat.succ 'x'
$FX/grep/Example.lean:15: example := @Nat.succ r\"x\"
$FX/grep/Example.lean:18: example := \`\`Nat.succ rfl" ]] && echo "  ok: only the proof examples of grep/Example.lean are flagged" ||
    { echo "  example scan: '$out'"; rc=1; }
  [[ $(grep_7b "$FX/grep/BadSpecMeta.lean" | wc -l) -eq 4 ]] && echo "  ok: 7b flags grep/BadSpecMeta.lean" || { echo "  7b misses grep/BadSpecMeta.lean"; rc=1; }
  [[ $(grep_7c "$FX/grep/lakefile-bad.toml" | wc -l) -ge 2 ]] && echo "  ok: 7c flags grep/lakefile-bad.toml" || { echo "  7c misses grep/lakefile-bad.toml"; rc=1; }
  [[ -z "$(grep_7a "$FX/ReviewAxiomsGood.lean")" ]] && echo "  ok: 7a passes a clean file" || { echo "  7a flags a clean file"; rc=1; }
  grep_7a "$FX/grep/does-not-exist.lean" >/dev/null; [[ $? -eq 2 ]] && echo "  ok: a missing file is an error" || { echo "  a missing file is not an error"; rc=1; }
  set -e
  return "$rc"
}

# --- step 8: vendored files -----------------------------------------------------------------------
step_vendor() { sha256sum --strict -c scripts/vendor.sha256; }

# --- step 9: comparator config (jq glue) and the challenge module ----------------------------------
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
# challenge_ok <file> <statements file>: the challenge imports exactly the statements modules
# (COMPARATOR_STATEMENTS, in that order; lean --deps-json, besides the implicit `Init`), and its text with
# comments removed (`--` to the end of the line, nested `/- ... -/` blocks, wherever they occur) is exactly
# the template: `module`, one `public import <m>` per statements module (in that order),
# `@[expose] public section`, one `theorem <s> : <S> := sorry` per statement S (`s` its lower-first
# name; any order) and `end`. Nothing else, so no declaration can hide next to a comment.
challenge_ok() {
  local f="$1" st="$2"
  lake env lean --deps-json "$f" |
    jq -e --args '.imports[0].errors == [] and ([.imports[0].result.imports[].module | select(. != "Init")] == $ARGS.positional)' \
      "${COMPARATOR_STATEMENTS[@]}" >/dev/null ||
    { echo "  FAIL[challenge-imports] $f must import exactly ${COMPARATOR_STATEMENTS[*]}"; return 1; }
  python3 -I - "$f" "$st" "${COMPARATOR_STATEMENTS[@]}" <<'PY' || return 1
import sys
src, stmts, specs = open(sys.argv[1]).read(), open(sys.argv[2]).read().split(), sys.argv[3:]
out, i, depth = [], 0, 0
while i < len(src):  # drop comments (nested block comments, line comments); keep newlines
    if src.startswith("/-", i): depth, i = depth + 1, i + 2
    elif depth and src.startswith("-/", i): depth, i = depth - 1, i + 2
    elif depth: out.append("\n" if src[i] == "\n" else ""); i += 1
    elif src.startswith("--", i): i = src.find("\n", i) if "\n" in src[i:] else len(src)
    else: out.append(src[i]); i += 1
got = [" ".join(l.split()) for l in "".join(out).splitlines() if l.strip()]
def thm(s):
    *ns, last = s.split(".")
    return f"theorem {'.'.join(ns + [last[:1].lower() + last[1:]])} : {s} := sorry"
head = ["module", *(f"public import {m}" for m in specs), "@[expose] public section"]
ok = (depth == 0 and stmts and got[:len(head)] == head and got[-1:] == ["end"]
      and sorted(got[len(head):-1]) == sorted(thm(s) for s in stmts))
if not ok:
    print(f"  FAIL[challenge] {sys.argv[1]} (comments removed) is not the template for {len(stmts)} statements:")
    print("\n".join("    " + l for l in got))
sys.exit(0 if ok else 1)
PY
}
step_comparator_config() {
  [[ -f comparator.json ]] || { echo "  no comparator.json"; return 1; }
  local m
  for m in "${MILESTONE_STATEMENTS[@]}"; do  # a milestone module with no closed statement would certify nothing
    [[ -n "$("${SURFACE[@]}" statements --modules "$m")" ]] ||
      { echo "  FAIL[challenge] milestone statements module $m has no closed Prop statement"; return 1; }
  done
  "${SURFACE[@]}" statements --modules "${COMPARATOR_STATEMENTS[@]}" >"$WORK/statements.txt" &&
    comparator_config_ok comparator.json "$WORK/statements.txt" &&
    challenge_ok "$(mod_file "$CHALLENGE")" "$WORK/statements.txt" &&
    echo "  comparator.json and $(mod_file "$CHALLENGE") match the $(wc -l <"$WORK/statements.txt") statements of ${COMPARATOR_STATEMENTS[*]}"
}
selftest_comparator_config() {
  set +e
  local rc=0 c
  expect_pass comparator_config_ok "$FX/comparator/config-good.json" "$FX/comparator/statements.txt" || rc=1
  for c in same defnames axioms names extra challenge multi; do
    expect_fail - comparator_config_ok "$FX/comparator/config-$c.json" "$FX/comparator/statements.txt" || rc=1
  done
  expect_fail - comparator_config_ok "$FX/comparator/config-empty.json" "$FX/comparator/statements-empty.txt" || rc=1
  # The challenge module: the real one against fixture statements lists, and fixture challenges.
  "${SURFACE[@]}" statements --modules "${COMPARATOR_STATEMENTS[@]}" >"$WORK/statements.txt" || { echo "  statements failed"; rc=1; }
  head -n -1 "$WORK/statements.txt" >"$WORK/statements-short.txt"
  expect_fail 'is not the template' challenge_ok "$(mod_file "$CHALLENGE")" "$WORK/statements-short.txt" || rc=1
  expect_fail 'is not the template' challenge_ok "$(mod_file "$CHALLENGE")" /dev/null || rc=1
  for c in import fewer; do
    expect_fail 'FAIL[challenge-imports]' challenge_ok "$FX/comparator/challenge-$c.lean" "$WORK/statements.txt" || rc=1
  done
  for c in weaker extra hidden; do
    expect_fail 'is not the template' challenge_ok "$FX/comparator/challenge-$c.lean" "$WORK/statements.txt" || rc=1
  done
  set -e
  return "$rc"
}

# --- steps 10, 11: lake check / lake comparator (bwrap sandbox; SKIP and listed CI-only without it) -----
have_bwrap() { command -v bwrap >/dev/null; }
step_lake_check() {
  set +e
  local rc=0 n
  # `lake check` rejects every non-standard axiom of the default targets, so it applies only while no sorry layer
  # holds `sorry` (plan §5). After that, certified = the closure of the solution: step 3b's audit, the kernel
  # replay of every leaf (step 5) and the comparator's sandboxed replay (step 11).
  [[ -s "$INV" ]] || python3 -I scripts/check-boundaries.py --config "$CFG" --lakefile lakefile.toml --inventory-out "$INV" >/dev/null
  if ! n="$(sorry_count "$INV")" || [[ -z "$n" ]]; then
    echo "  cannot count sorry in the sorry layers"; rc=1
  elif ((n == 0)); then
    lake check || rc=1
  else
    echo "  NOTE  lake check of the default targets not run: $n sorry/admit in the sorry layers (plan §5);"
    echo "        the Solution closure and the tests are audited (3b), and the solution replayed (5, 11)"
    [[ -z "${CI:-}" ]] || echo "::warning title=lake check::not run on the default targets: $n sorry/admit in the sorry layers (plan §5)"
  fi
  # Rejected for the intended reason (the user axiom), not for a broken fixture or sandbox.
  expect_fail "error: Axiom 'ax' is not permitted; it is used by 't'" lake -d "$FX/lakecheck-bad" check || rc=1
  expect_pass lake -d "$FX/lakecheck-good" check || rc=1
  set -e
  return "$rc"
}
step_lake_comparator() {
  set +e
  local rc=0
  # --paranoid: also leanchecker-paranoid, lean4lean, nanoda, con-leche, con-ron (~3 min in CI, measured in B5).
  lake comparator --paranoid --config comparator.json || rc=1
  # Fixtures over CheckFixtures.Cmp.* (exit 1 = rejected; each for its intended reason).
  expect_pass lake comparator --config "$FX/comparator-good.json" || rc=1
  expect_fail "Challenge and solution theorem statement do not match: 'CheckFixtures.Cmp.t'" \
    lake comparator --config "$FX/comparator-stmt.json" || rc=1
  expect_fail "Illegal axiom detected" lake comparator --config "$FX/comparator-axiom.json" || rc=1
  expect_fail "Const does not match between challenge and target" lake comparator --config "$FX/comparator-def.json" || rc=1
  set -e
  return "$rc"
}

# --- step 12: docs --------------------------------------------------------------------------------
# docs_ok <README> <expected files...>: the backticked `*.lean` paths between the lines
# `<!-- spec-files -->` and `<!-- /spec-files -->` are exactly the expected files.
docs_ok() {
  local readme="$1" got want
  shift
  grep -qx '<!-- spec-files -->' "$readme" && grep -qx '<!-- /spec-files -->' "$readme" ||
    { echo "  FAIL[docs] $readme has no spec-files markers"; return 1; }
  got="$(sed -n '/^<!-- spec-files -->$/,/^<!-- \/spec-files -->$/p' "$readme" | grep -oE '`[^`]+\.lean`' | tr -d '`' | LC_ALL=C sort -u)"
  want="$(printf '%s\n' "$@" | LC_ALL=C sort -u)"
  [[ -n "$want" && "$got" == "$want" ]] ||
    { echo "  FAIL[docs] $readme lists other files than expected:"; diff <(echo "$want") <(echo "$got") | sed 's/^/    /'; return 1; }
}
DOCS=(python3 -I scripts/check-docs.py)
step_docs() {
  local files=() rc=0
  mapfile -t files < <(for m in "${SPEC_MODULES[@]}"; do mod_file "$m"; done)
  { docs_ok README.md "${files[@]}" && echo "  README.md lists the ${#files[@]} files of the trusted layers"; } || rc=1
  # The name index is a module of a test library, so step 1 builds it (and the generated root imports it).
  awk -F'\t' -v m="$NAME_INDEX" '$2 == m { print $1 }' "$INV" | grep -xF -f <(printf '%s\n' "${TEST_LIBS[@]}") >/dev/null ||
    { echo "  FAIL[docs] name_index_module $NAME_INDEX is not a module of a test library (${TEST_LIBS[*]})"; rc=1; }
  "${DOCS[@]}" names "$(mod_file "$NAME_INDEX")" "${DOC_NAME_FILES[@]}" || rc=1
  "${DOCS[@]}" codeowners .github/CODEOWNERS . "$CODE_OWNER" "${OWNED_PATHS[@]}" || rc=1
  return "$rc"
}
selftest_docs() {
  set +e
  local rc=0 good=("$FX/CheckFixtures/GoodSpec/A.lean" "$FX/CheckFixtures/GoodSpec/B.lean")
  expect_pass docs_ok "$FX/README-good.md" "${good[@]}" || rc=1
  expect_fail 'FAIL[docs]' docs_ok "$FX/README-missing.md" "${good[@]}" || rc=1
  expect_fail 'FAIL[docs]' docs_ok "$FX/README-good.md" "${good[0]}" || rc=1
  expect_fail 'FAIL[docs]' docs_ok "$FX/README-good.md" || rc=1
  expect_fail 'FAIL[docs] ' docs_ok "$FX/comparator/README.md" "${good[@]}" || rc=1
  local d="$FX/docs" own=(codeowners "$FX/docs/tree" @o f.txt D Spec)
  expect_pass "${DOCS[@]}" names "$d/Index.lean" "$d/good.md" || rc=1
  expect_fail 'does not list (example := ``Consensus.Absent)' "${DOCS[@]}" names "$d/Index.lean" "$d/unlisted.md" || rc=1
  expect_fail 'does not list (example := ``Consensus.InBlock)' "${DOCS[@]}" names "$d/Index.lean" "$d/block-comment.md" || rc=1
  expect_fail 'does not list (example := ``Consensus.InNested)' "${DOCS[@]}" names "$d/Index.lean" "$d/nested-comment.md" || rc=1
  expect_fail 'does not list (example := ``Consensus.InLine)' "${DOCS[@]}" names "$d/Index.lean" "$d/line-comment.md" || rc=1
  expect_fail 'Index-string.lean:3: not a' "${DOCS[@]}" names "$d/Index-string.lean" "$d/good.md" || rc=1
  expect_fail 'Index-guard.lean:2: not a' "${DOCS[@]}" names "$d/Index-guard.lean" "$d/good.md" || rc=1
  expect_fail 'Index-at.lean:2: not a' "${DOCS[@]}" names "$d/Index-at.lean" "$d/good.md" || rc=1
  expect_fail 'fenced.md cites `Consensus.Absent`' "${DOCS[@]}" names "$d/Index.lean" "$d/fenced.md" || rc=1
  expect_fail 'prose.md cites `Consensus.Absent`' "${DOCS[@]}" names "$d/Index.lean" "$d/prose.md" || rc=1
  expect_fail '`Consensus.«Listed»` is not a plain name' "${DOCS[@]}" names "$d/Index.lean" "$d/quoted.md" || rc=1
  expect_fail '`Consensus.Listed℘` is not a plain name' "${DOCS[@]}" names "$d/Index.lean" "$d/oddchar.md" || rc=1
  expect_fail 'cites `Consensus.Absent2`' "${DOCS[@]}" names "$d/Index.lean" "$d/quote-root.md" || rc=1
  expect_fail 'cites `Consensus.Absent3_`' "${DOCS[@]}" names "$d/Index.lean" "$d/quote-root.md" || rc=1
  expect_fail "cites \`Consensus.Absent'\`" "${DOCS[@]}" names "$d/Index.lean" "$d/quote.md" || rc=1
  expect_fail 'cannot read doc' "${DOCS[@]}" names "$d/Index.lean" "$d/good.md" "$d/absent.md" || rc=1
  expect_fail 'cannot read name index' "${DOCS[@]}" names "$d/absent.lean" "$d/good.md" || rc=1
  expect_fail 'no doc files given' "${DOCS[@]}" names "$d/Index.lean" || rc=1
  expect_pass "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-good" "${own[@]:1}" || rc=1
  expect_fail 'does not list B' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-good" "${own[@]:1}" B || rc=1
  expect_fail 'lists scripts, which is not' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-extra" "${own[@]:1}" || rc=1
  expect_fail 'is not anchored' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-unanchored" "${own[@]:1}" || rc=1
  expect_fail 'trailing slash, but f.txt is not a directory' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-fileslash" "${own[@]:1}" || rc=1
  expect_fail 'trailing slash, but Spec is not a directory' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-absentslash" "${own[@]:1}" || rc=1
  expect_fail 'is owned by nobody' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-ownerless" "${own[@]:1}" || rc=1
  expect_fail 'is owned by @o @x, not exactly @o' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-otherowner" "${own[@]:1}" || rc=1
  expect_fail 'is listed twice' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-duplicate" "${own[@]:1}" || rc=1
  expect_fail 'no paths given' "${DOCS[@]}" "${own[0]}" "$d/CODEOWNERS-good" "${own[@]:1:2}" || rc=1
  set -e
  return "$rc"
}

# --- step 13: metrics (report) --------------------------------------------------------------------
step_metrics() {
  local out
  out="$(python3 -I scripts/metrics-baseline.py --config "$CFG" --no-modules 2>&1)" || { echo "$out" | tail -5; return 1; }
  echo "  NOTE  report (scripts/metrics-baseline.py, totals):"
  sed -n '/^## Totals$/,/^Direct imports/p' <<<"$out" | grep '^- ' | cut -c1-400 | sed 's/^/    /'
}

# --- step 14: rebuild canary (report) --------------------------------------------------------------
# A proof-only edit (`canary_proof_edit` = [old, new] in boundaries.toml) of `canary_module` must rebuild that one
# module: its .olean.hash unchanged and every default target still up to date (plan §6; Lake module/test.sh). A
# regression is reported (a warning in CI), not failed. The control, a statement edit, must make the default
# targets stale; if it does not, the canary cannot see a rebuild, and the step fails, as it does when an edit no
# longer applies or the module cannot be restored.
canary_edit() {  # canary_edit <file> <old> <new> [--dry-run]: replace the one occurrence of <old>
  python3 -I - "$@" <<'PY'
import sys
f, old, new = sys.argv[1:4]
t = open(f).read()
if t.count(old) != 1:
    sys.exit(f"  FAIL[canary] {old!r} occurs {t.count(old)} times in {f}: update canary_* in scripts/boundaries.toml")
if sys.argv[4:] != ["--dry-run"]:
    open(f, "w").write(t.replace(old, new))
PY
}
canary_applies() {  # both edits of the canary apply to the committed module (no write, no build)
  ((${#CANARY_PROOF[@]} == 2 && ${#CANARY_STMT[@]} == 2)) ||
    { echo "  FAIL[canary] canary_proof_edit and canary_statement_edit must each be [old, new]"; return 1; }
  canary_edit "$(mod_file "$CANARY_MODULE")" "${CANARY_PROOF[@]}" --dry-run &&
    canary_edit "$(mod_file "$CANARY_MODULE")" "${CANARY_STMT[@]}" --dry-run
}
step_canary() {
  local f hash
  # Artifact cache off (#39): a module served from the cache does not rewrite its .olean.hash in .lake/build.
  local -x LAKE_ARTIFACT_CACHE=false
  f="$(mod_file "$CANARY_MODULE")" hash=".lake/build/lib/lean/${CANARY_MODULE//.//}.olean.hash"
  [[ -f "$f" ]] && git diff --quiet -- "$f" || { echo "  FAIL[canary] $f is missing or has local changes"; return 1; }
  canary_applies || return 1
  cp "$f" "$WORK/canary.orig"
  local rc=0
  # The subshell restores the module and rebuilds it on any exit (also after a failure or a signal).
  ( trap 'cp "$WORK/canary.orig" "$f"; lake build -q "$CANARY_MODULE" >/dev/null 2>&1' EXIT; trap 'exit 1' INT TERM
    canary_run "$f" "$hash" ) || rc=1
  # Restored: the module is back to its original interface, and nothing else is stale.
  lake build -q --no-build && git diff --quiet -- "$f" ||
    { echo "  FAIL[canary] the tree is not back to its built state after the canary"; rc=1; }
  return "$rc"
}
canary_run() {  # canary_run <file> <hash file>, in a subshell that restores <file> on exit
  local f="$1" hash="$2" h0 h1
  lake build -q --no-build >/dev/null 2>&1 && [[ -f "$hash" ]] ||
    { echo "  FAIL[canary] the default targets are not built: the canary needs a built tree"; exit 1; }
  h0="$(cat "$hash")"
  canary_edit "$f" "${CANARY_PROOF[@]}" || exit 1
  lake build -q "$CANARY_MODULE" || { echo "  FAIL[canary] the proof edit does not build"; exit 1; }
  h1="$(cat "$hash")"
  if [[ "$h0" == "$h1" ]] && lake build -q --no-build >/dev/null 2>&1; then
    echo "  NOTE  canary (report): the proof-only edit of $CANARY_MODULE rebuilt 1 module (.olean.hash unchanged)"
  else
    echo "  NOTE  canary (report): REGRESSION: a proof-only edit of $CANARY_MODULE leaves other modules stale (.olean.hash $h0 -> $h1)"
    [[ -z "${CI:-}" ]] || echo "::warning title=Rebuild canary::a proof-only edit of $CANARY_MODULE rebuilds more than one module"
  fi
  cp "$WORK/canary.orig" "$f"
  canary_edit "$f" "${CANARY_STMT[@]}" || exit 1
  lake build -q "$CANARY_MODULE" || { echo "  FAIL[canary] the statement edit does not build"; exit 1; }
  if lake build -q --no-build >/dev/null 2>&1; then
    echo "  FAIL[canary] control: the statement edit of $CANARY_MODULE left every importer up to date"; exit 1
  fi
  echo "  ok: control: the statement edit makes the default targets stale"
}

# --- driver ---------------------------------------------------------------------------------------
overall=0
skipped=()
step_times=()
build_failed=0
deferred=()
ci_only=()
# in_part <label>: whether this run's --split part runs the step (by its number): lake-check = 0 and 10.
in_part() {
  local n="${1%% *}"
  case "$split" in
    "") return 0 ;;
    lake-check) [[ "$n" == 0 || "$n" == 10 ]] ;;
    main) [[ "$n" != 10 ]] ;;
  esac
}
run_step() {
  local label="$1"
  shift
  if ! in_part "$label"; then
    echo "DEFER $label (the other --split part)"; deferred+=("$label"); return 0
  fi
  # After a failed build, the steps that read build outputs would report on stale artifacts (#50): not run.
  if ((build_failed)) && [[ " 3 3b 4 5 6 9 10 11 14 " == *" ${label%% *} "* ]]; then
    skip_step "$label" "not run: step 1 failed, so the build outputs it reads may be stale"; return 0
  fi
  echo "--- $label ---"
  local t0=$SECONDS v=PASS
  "$@" || { v=FAIL; overall=1; [[ "$label" != "1 build self-test"* && "${label%% *}" == 1 ]] && build_failed=1; }
  echo "  time: $((SECONDS - t0)) s"   # wall time of the step (#50); verdict lines unchanged
  step_times+=("$((SECONDS - t0))s ${label%% (*}")
  printf '%s  %s\n' "$v" "$label"
}
skip_step() { echo "SKIP  $1 ($2)"; skipped+=("$1"); }
run_if() {  # run_if <0|1> <reason to skip> <label> <step...>
  if (($1)); then run_step "${@:3}"; else skip_step "$3" "$2"; fi
}
run_selftest() { run_if "$selftests" "self-test: --full or --selftests" "$@"; }
full_only() {  # the heavy steps: --full only (CI: nightly, manual, milestone/release tags); bwrap ones need it
  if [[ "$mode" != full ]]; then
    skip_step "$1" "--full only: CI nightly"
  elif [[ "$2" == step_lake_* ]] && in_part "$1" && ! have_bwrap; then
    echo "SKIP  $1 (skipped: no bwrap)"; ci_only+=("$1")
  else
    run_step "$@"
  fi
}

if [[ "$mode" == changed ]]; then compute_changes; fi
# Self-test-only build targets: the fixture libraries except the comparator challenge (built in every
# mode, so a broken challenge fails before the nightly comparator run).
for t in "${EXTRA_TARGETS[@]}"; do
  if ((selftests)) || ! printf '%s\n' "${FIXTURE_LIBS[@]}" | grep -xF "$t" >/dev/null || [[ "$t" == "$CHALLENGE" ]]; then
    BUILD_EXTRA+=("$t")
  fi
done
echo "check.sh: mode $mode$( ((selftests)) && echo ', with self-tests')"
if [[ "$mode" == changed ]]; then
  build_label="1 build (the downstream cone: ${#CONE[@]} modules"
  if ((do_comparator_config)); then build_label+=" + $CHALLENGE"; fi
  if ((${#DECL_LIBS[@]})); then build_label+=" + check-decls"; fi
  if ((do_surface || do_comparator_config || ${#DECL_LIBS[@]})); then build_label+=" + spec-surface"; fi
  build_label+=")"
else
  build_label="1 build (default targets + ${BUILD_EXTRA[*]})"
fi
build_label+=", --wfail --iofail"
if ((no_build)); then build_label+=" (freshness only, --no-build)"; fi

run_step "0 pins (toolchain + dependencies = scripts/pins.toml)" step_pins
run_selftest "0 pins self-test (fixtures/pins-*)" selftest_pins
run_selftest "0 landing cancellation self-test (local Git remotes)" python3 -I scripts/test_push_main.py
run_selftest "0 box CI parity self-test (local Git remotes)" python3 -I scripts/test_orb_ci.py
run_selftest "0 warm worktree isolation self-test" python3 -I scripts/test_worktree_setup.py
if [[ "$mode" == changed ]] && ((${#BUILD_TARGETS[@]} == 0)); then
  skip_step "1 build" "no Lean module changed"
else
  run_step "$build_label" step_build
fi
run_selftest "1 build self-test (--wfail on a replayed warning; warn.sorry = false)" selftest_build
run_step "2 boundaries (check-boundaries.py, every checked library)" step_boundaries
if in_part 2 && [[ ! -s "$INV" ]]; then
  echo "check.sh: no inventory; the remaining steps need it"; echo; echo "check.sh: FAILURES PRESENT" >&2; exit 1
fi
! in_part 2 || mapfile -t SPEC_MODULES < <(inv_trusted)
run_selftest "2 boundaries self-test (fixtures/boundaries/cases.toml)" selftest_boundaries
run_if "${#DECL_LIBS[@]}" "no library affected" "3 declarations (check-decls: ${DECL_LIBS[*]:-none})" step_decls
run_selftest "3 declarations self-test (test_check_decls.sh, OrphanLib, EmptyScope, HiddenOpaque, SorryPlace)" selftest_decls
run_if "$((do_audit || do_audit_tests || do_audit_report))" "nothing in the closure of $SOLUTION, ${TEST_LIBS[*]} or ${DEFAULT_LIBS[*]} changed" \
  "3b axiom audit (closure of $SOLUTION, ${TEST_LIBS[*]}: gate; unfinished in ${DEFAULT_LIBS[*]}: report)" step_audit
run_selftest "3b axiom audit self-test (CheckFixtures.Audit)" selftest_audit
if ((do_surface)); then
  run_step "4 Spec surface (extensions, snapshot, theorems, noconst)" step_surface
else
  skip_step "4 Spec surface: extensions, snapshot, theorems" "no module of a trusted layer changed"
  run_if "${#DECL_LIBS[@]}" "no library affected" "4 noconst (every module with descendants)" step_noconst
fi
run_selftest "4 Spec surface self-test (CheckFixtures)" selftest_surface
full_only "5 kernel replay (leanchecker, every leaf module)" step_replay
run_selftest "5 kernel replay self-test (BadSkipKernel, prefix refusal)" selftest_replay
run_step "6 review pins ($REVIEW_ROOT imports $REVIEW_AXIOMS)" step_review
run_selftest "6 review pins self-test (review-imports, ReviewAxioms*, Review{Eq,Binder,Complete,Escape}Bad, ReviewGuardGood, mutations)" selftest_review
run_step "7 backstop (grep$([[ "$mode" == changed ]] && echo ', changed files'))" step_grep
run_selftest "7 backstop self-test (fixtures/grep)" selftest_grep
run_step "8 vendored files (scripts/vendor.sha256)" step_vendor
run_if "$do_comparator_config" "no change to the statements, the challenge, comparator.json or the solution's imports" \
  "9 comparator config" step_comparator_config
run_selftest "9 comparator config self-test (fixtures/comparator: configs, challenges)" selftest_comparator_config
full_only "10 lake check (+ fixtures/lakecheck-{bad,good})" step_lake_check
# leanchecker skips the noconst-exempt parents (step 5); step 10's replay covers them, when it runs.
[[ "$mode" != full ]] || have_bwrap || ((${#NOCONST_EXEMPT[@]} == 0)) || ci_only+=("kernel replay of ${NOCONST_EXEMPT[*]} (lake check)")
full_only "11 lake comparator --paranoid (+ fixtures/comparator-{good,stmt,axiom,def}.json)" step_lake_comparator
run_step "12 docs (README spec-files = the files of the trusted layers; cited names; CODEOWNERS)" step_docs
run_selftest "12 docs self-test (README-good, README-missing, fixtures/docs)" selftest_docs
run_step "13 metrics (report)" step_metrics
if [[ "$mode" == changed ]] || ((!canary)); then
  skip_step "14 rebuild canary" "--full, or --canary (CI: when the build configuration changed)"
else
  run_step "14 rebuild canary (report; the control must rebuild)" step_canary
fi

echo
echo "Step times (wall, longest first; $((SECONDS)) s in all):"
printf '%s\n' "${step_times[@]}" | sort -rn | sed 's/^/  /'
((${#ci_only[@]} == 0)) || echo "CI-only: ${ci_only[*]}"
if ((overall)); then
  echo "check.sh: FAILURES PRESENT" >&2
elif ((${#skipped[@]})); then
  echo "check.sh: PASSED ($mode mode; ${#skipped[@]} steps skipped, listed as SKIP above)"
elif [[ -n "$split" ]]; then
  echo "check.sh: PART PASSED (split $split; ${#deferred[@]} steps deferred to the other part)"
else
  echo "check.sh: ALL CHECKS PASSED"
fi
exit "$overall"
