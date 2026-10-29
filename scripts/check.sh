#!/usr/bin/env bash
# The single check driver (local and CI). Usage: scripts/check.sh [--quick] [--update-snapshot]
#
#   0. build         `lake build` (default targets) and `lake build CheckFixtures`, always (also with
#                    --quick: a no-op replay when fresh), so no check reads stale .olean files.
#   1. sanity        every metadata query of scripts/CheckSpec.lean answers correctly on known
#                    constants (no silently empty extension state).
#   2. axioms        every declaration of every project module, roots included, uses only
#                    propext, Classical.choice, Quot.sound.
#   3. source bans   no sorry/admit/native_decide (and kernel-bypass options) in the sources.
#   4. self-tests    every check subcommand on good and bad fixtures (scripts/fixtures): every
#                    negative fixture must fail with its tag, every positive one must pass.
#                    Skipped with --quick.
#
# Layout status (reorganisation batch B1): the project still has the six old libraries. The import,
# Spec-content, snapshot and review checks exist (scripts/CheckSpec.lean) and are self-tested here,
# but run on the real Spec only once it exists (batches B2-B4).
#
# Every failure line carries a stable tag `FAIL[<rule>]`. Exit 0 iff every step passed.

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

quick=0
update_snapshot=0
while (($#)); do
  case "$1" in
    --quick) quick=1; shift ;;
    --update-snapshot) update_snapshot=1; shift ;;
    -h|--help) sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

# Project libraries (old layout until batch B4), roots included by CheckSpec's inventory.
LIBS=(ConsensusProblem ConsensusModel ConsensusModelProofs ConsensusBlocks ConsensusShape ConsensusShapeTests)
# Sources scanned by the source bans.
SOURCES=(ConsensusProblem ConsensusProblem.lean ConsensusModel ConsensusModel.lean
  ConsensusModelProofs ConsensusModelProofs.lean ConsensusBlocks ConsensusBlocks.lean
  ConsensusShape ConsensusShape.lean ConsensusShapeTests ConsensusShapeTests.lean
  CheckConsensusAxioms.lean scripts/CheckSpec.lean)

FIX=scripts/fixtures
FIXSRC=(--src "$FIX")
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

checkspec() { lake env lean --run scripts/CheckSpec.lean "$@"; }

lib_args() { local l; for l in "$@"; do printf -- '--lib\n%s\n' "$l"; done; }

# --- reusable checks (also the code paths of the self-tests) -----------------------------------

# Source bans: words that admit an unproved statement or bypass the kernel.
# Fail-closed: every input must exist, and a grep error (status 2) is a failure, not "no match".
source_ban() {
  local found="" out p rc
  if [[ $# -eq 0 ]]; then echo "FAIL[source] no inputs"; return 1; fi
  for p in "$@"; do
    if [[ ! -e "$p" ]]; then echo "FAIL[source] missing input $p"; return 1; fi
  done
  for p in 'sorry|admit|native_decide|sorryAx|ofReduceBool|trustCompiler' \
           'decide +\+native|set_option +debug\.skipKernelTC'; do
    rc=0
    if [[ $p == sorry* ]]; then
      out="$(grep -rnwE --include='*.lean' "$p" "$@")" || rc=$?
    else
      out="$(grep -rnE --include='*.lean' "$p" "$@")" || rc=$?
    fi
    if [[ $rc -gt 1 ]]; then echo "FAIL[source] grep error (status $rc) on $*"; return 1; fi
    if [[ -n "$out" ]]; then found+="$out"$'\n'; fi
  done
  found="${found%$'\n'}"
  if [[ -n "$found" ]]; then
    while IFS= read -r line; do echo "FAIL[source] $line"; done <<<"$found"
    return 1
  fi
  echo "PASS source bans: $*"
}

# Snapshot gate: regenerate the readable and canonical snapshots of a library and diff them
# against the checked-in files. Usage: snapshot_check <lib> <readable> <canonical> [CheckSpec args]
snapshot_check() {
  local lib="$1" readable="$2" canonical="$3"; shift 3
  local out_r="$TMP/snap.readable" out_c="$TMP/snap.canonical" rc=0
  checkspec snapshot --lib "$lib" "$@" --out "$out_r" || return 2
  checkspec snapshot --canonical --lib "$lib" "$@" --out "$out_c" || return 2
  if [[ $update_snapshot -eq 1 ]]; then
    cp "$out_r" "$readable"; cp "$out_c" "$canonical"
    echo "updated $readable $canonical"
    return 0
  fi
  if ! diff -u "$readable" "$out_r"; then echo "FAIL[snapshot] readable $readable"; rc=1; fi
  if ! diff -u "$canonical" "$out_c"; then echo "FAIL[snapshot] canonical $canonical"; rc=1; fi
  [[ $rc -eq 0 ]] && echo "PASS snapshot $lib"
  return $rc
}

# Docs: the README's spec-files list equals the .lean files under a directory.
# Usage: docs_check <readme> <dir>
docs_check() {
  local readme="$1" dir="$2" listed actual
  listed="$(sed -n '/<!-- spec-files -->/,/<!-- \/spec-files -->/p' "$readme" \
    | grep -oE "${dir}/[A-Za-z0-9_/]+\.lean" | sort -u)"
  actual="$(find "$dir" -name '*.lean' | sort -u)"
  if [[ "$listed" != "$actual" ]]; then
    diff <(echo "$listed") <(echo "$actual") | sed 's/^/  /'
    echo "FAIL[docs] $readme does not list exactly the files under $dir"
    return 1
  fi
  echo "PASS docs $readme"
}

# --- self-test helpers ---------------------------------------------------------------------------

selftest_fail=0
selftest_count=0

# expect_fail <tag> <must-contain-regex|""> -- cmd...: exit status 1 (a check that ran and failed; a
# crash or usage error exits otherwise) and a line `FAIL[<tag>] ...` that also matches the regex.
expect_fail() {
  local tag="$1" extra="$2"; shift 3
  local out rc tagged
  selftest_count=$((selftest_count + 1))
  set +e; out="$("$@" 2>&1)"; rc=$?; set -e
  tagged="$(grep -F "FAIL[$tag]" <<<"$out" || true)"
  if [[ $rc -eq 1 && -n "$tagged" ]] && { [[ -z "$extra" ]] || grep -qE "$extra" <<<"$tagged"; }; then
    echo "  ok   expect FAIL[$tag]${extra:+ ($extra)}: $*"
  else
    echo "  BAD  expected FAIL[$tag]${extra:+ ($extra)} on one line and exit 1 (rc=$rc): $*"
    sed 's/^/       | /' <<<"$out" | tail -20
    selftest_fail=1
  fi
}

expect_pass() {
  local out rc
  selftest_count=$((selftest_count + 1))
  set +e; out="$("$@" 2>&1)"; rc=$?; set -e
  if [[ $rc -eq 0 ]] && ! grep -q 'FAIL\[' <<<"$out"; then
    echo "  ok   expect pass: $*"
  else
    echo "  BAD  expected pass (rc=$rc): $*"
    sed 's/^/       | /' <<<"$out" | tail -20
    selftest_fail=1
  fi
}

# expect_pass_out <regex> -- cmd...: passes and the output matches the regex.
expect_pass_out() {
  local extra="$1"; shift 2
  local out rc
  selftest_count=$((selftest_count + 1))
  set +e; out="$("$@" 2>&1)"; rc=$?; set -e
  if [[ $rc -eq 0 ]] && ! grep -q 'FAIL\[' <<<"$out" && grep -qE "$extra" <<<"$out"; then
    echo "  ok   expect pass ($extra): $*"
  else
    echo "  BAD  expected pass and /$extra/ (rc=$rc): $*"
    sed 's/^/       | /' <<<"$out" | tail -20
    selftest_fail=1
  fi
}

# expect_nonzero <must-contain-regex> -- cmd...: for mechanisms without a tag (#guard_msgs).
expect_nonzero() {
  local extra="$1"; shift 2
  local out rc
  selftest_count=$((selftest_count + 1))
  set +e; out="$("$@" 2>&1)"; rc=$?; set -e
  if [[ $rc -ne 0 ]] && grep -qE "$extra" <<<"$out"; then
    echo "  ok   expect nonzero exit ($extra): $*"
  else
    echo "  BAD  expected nonzero exit and /$extra/ (rc=$rc): $*"
    sed 's/^/       | /' <<<"$out" | tail -20
    selftest_fail=1
  fi
}

# --- steps ---------------------------------------------------------------------------------------

step_build() {
  lake build && lake build CheckFixtures
}

step_sanity() {
  checkspec sanity --lib ConsensusProblem --lib ConsensusShape
}

step_axioms() {
  # shellcheck disable=SC2046
  checkspec axioms $(lib_args "${LIBS[@]}")
}

step_source() {
  source_ban "${SOURCES[@]}"
}

step_selftests() {
  selftest_fail=0
  selftest_count=0
  local g F="$FIX" CF="$FIX/CheckFixtures"
  local IMP=(--root-covers --no-root-imports)

  echo "imports"
  expect_pass checkspec imports --lib CheckFixtures.GoodSpec "${FIXSRC[@]}" --allowed CheckFixtures.GoodSpec "${IMP[@]}"
  for g in BadImport BadMacro RootImport GenDep; do
    expect_fail import 'CheckFixtures.Proof' -- checkspec imports --lib "CheckFixtures.$g" "${FIXSRC[@]}" --allowed "CheckFixtures.$g" "${IMP[@]}"
  done
  expect_fail root 'BadRoot.Orphan' -- checkspec imports --lib CheckFixtures.BadRoot "${FIXSRC[@]}" --allowed CheckFixtures.BadRoot "${IMP[@]}"
  expect_fail root-import 'ChildImportsRoot.A' -- checkspec imports --lib CheckFixtures.ChildImportsRoot "${FIXSRC[@]}" --allowed CheckFixtures.ChildImportsRoot --no-root-imports

  echo "content"
  expect_pass checkspec content --lib CheckFixtures.GoodSpec "${FIXSRC[@]}" --allowlist "$F/goodspec-allowlist.txt"
  expect_pass checkspec content --lib CheckFixtures.BadMacro "${FIXSRC[@]}"   # why R1 is needed
  expect_fail theorem 'GoodSpec.instCountableColor' -- checkspec content --lib CheckFixtures.GoodSpec "${FIXSRC[@]}"
  expect_fail root-decl 'RootDecl.r' -- checkspec content --lib CheckFixtures.RootDecl "${FIXSRC[@]}"
  expect_fail theorem 'BadTheorem.t' -- checkspec content --lib CheckFixtures.BadTheorem "${FIXSRC[@]}"
  expect_fail theorem 'BadDefProp.h ' -- checkspec content --lib CheckFixtures.BadDefProp "${FIXSRC[@]}"
  expect_fail theorem 'BadDefProp.h2' -- checkspec content --lib CheckFixtures.BadDefProp "${FIXSRC[@]}"
  expect_fail theorem 'BadMetaThm.sneaky' -- checkspec content --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  expect_fail theorem 'BadMetaThm.Foo._proof_99 \(not reachable' -- checkspec content --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  # rangeless (injected) auxiliaries: nested namespace, forged companion, suffix on the wrong parent kind
  expect_fail theorem 'BadMetaThm.Bar.Inner._proof_1 \(no parent' -- checkspec content --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  expect_fail theorem 'BadMetaThm.Foo2._proof_1 \(not reachable' -- checkspec content --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  for g in Foo.injEq Foo.inj Foo.sizeOf_spec Foo._flat_ctor Foo.ofNat_ctorIdx Foo._sizeOf_1_eq Foo._default \
      Col.injEq Col.eq_1 Col._default Col._proof_1; do
    expect_fail theorem "BadMetaThm\\.${g} \\(suffix" -- checkspec content --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  done
  for g in Foo.eq_1 Foo.eq_def Foo.eq_unfold Foo.splitter Foo.congr_simp; do
    expect_fail theorem "BadMetaThm\\.${g} \\(type does not mention" -- checkspec content --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  done
  # proofs written by hand under generated names (they have declaration ranges)
  for g in foo.inj earlier.eq_999 bar._proof_99 Foo.injEq Foo.sizeOf_spec Foo._default Foo.splitter \
      Foo._flat_ctor Col.injEq baz.Inner._proof_1 wh.proof_1; do
    expect_fail theorem "BadGenName\\.${g} \\(a proof declared in the source" -- checkspec content --lib CheckFixtures.BadGenName "${FIXSRC[@]}"
  done
  expect_fail theorem 'BadAllowlisted.t2' -- checkspec content --lib CheckFixtures.BadAllowlisted "${FIXSRC[@]}" --allowlist "$F/bad-allowlist.txt"
  expect_fail theorem 'BadAllowlisted.t3' -- checkspec content --lib CheckFixtures.BadAllowlisted "${FIXSRC[@]}" --allowlist "$F/bad-allowlist.txt"
  expect_fail theorem 'BadAllowlisted.t4 .*class=Nonempty' -- checkspec content --lib CheckFixtures.BadAllowlisted "${FIXSRC[@]}" --allowlist "$F/bad-allowlist.txt"
  expect_fail allowlist-stale 'GoodSpec.nope' -- checkspec content --lib CheckFixtures.GoodSpec "${FIXSRC[@]}" --allowlist "$F/stale-allowlist.txt"
  expect_fail axiom 'BadAxiom.ax' -- checkspec content --lib CheckFixtures.BadAxiom "${FIXSRC[@]}"
  expect_fail opaque 'BadOpaque.o' -- checkspec content --lib CheckFixtures.BadOpaque "${FIXSRC[@]}"
  expect_fail unsafe 'BadUnsafe.f' -- checkspec content --lib CheckFixtures.BadUnsafe "${FIXSRC[@]}"
  expect_fail partial 'BadPartial.loop' -- checkspec content --lib CheckFixtures.BadPartial "${FIXSRC[@]}"
  expect_fail implemented-by 'BadImplBy.f' -- checkspec content --lib CheckFixtures.BadImplBy "${FIXSRC[@]}"
  expect_fail extern 'BadExtern.f' -- checkspec content --lib CheckFixtures.BadExtern "${FIXSRC[@]}"
  expect_fail csimp 'BadCSimp.f_eq' -- checkspec content --lib CheckFixtures.BadCSimp "${FIXSRC[@]}"
  expect_fail theorem 'BadCSimp.f_eq' -- checkspec content --lib CheckFixtures.BadCSimp "${FIXSRC[@]}"
  expect_fail dep 'GenDep.b._proof_1 uses CheckFixtures.Proof.le_helper' -- checkspec content --lib CheckFixtures.GenDep "${FIXSRC[@]}"

  echo "axioms"
  expect_pass checkspec axioms --lib CheckFixtures.GoodSpec "${FIXSRC[@]}"
  # the root module is in the inventory (RootDecl.r is declared in the root file)
  expect_pass_out 'in 2 modules' -- checkspec axioms --lib CheckFixtures.RootDecl "${FIXSRC[@]}"
  expect_fail axiom-use 'RootAxiom.u uses CheckFixtures.RootAxiom.ax' -- checkspec axioms --lib CheckFixtures.RootAxiom "${FIXSRC[@]}"
  expect_fail axiom-use 'BadAxiom.u uses CheckFixtures.BadAxiom.ax' -- checkspec axioms --lib CheckFixtures.BadAxiom "${FIXSRC[@]}"
  expect_fail axiom-use 'BadSorry.s uses sorryAx' -- checkspec axioms --lib CheckFixtures.BadSorry "${FIXSRC[@]}"
  expect_fail axiom-use 'BadNative.n uses .*native_decide' -- checkspec axioms --lib CheckFixtures.BadNative "${FIXSRC[@]}"

  echo "pinned axioms (#guard_msgs)"
  expect_pass lake env lean "$F/ReviewAxiomsGood.lean"
  expect_nonzero 'does not match' -- lake env lean "$F/ReviewAxiomsBad.lean"

  echo "review"
  local R=(--lib CheckFixtures.ReviewBad "${FIXSRC[@]}" --stmt-module CheckFixtures.ReviewBad.A --thm-module CheckFixtures.ReviewBad.A)
  local W=(--wired CheckFixtures.ReviewBad:CheckFixtures.ReviewBad.A)
  expect_pass checkspec review "${R[@]}" --pairs "$F/review-pairs-good.txt" "${W[@]}"
  expect_fail review-type 'ReviewBad.stmt ' -- checkspec review "${R[@]}" --pairs "$F/review-pairs-bad.txt" "${W[@]}"
  expect_fail review-source 'ReviewBad.Stmt2' -- checkspec review "${R[@]}" --pairs "$F/review-pairs-badsource.txt" "${W[@]}"
  expect_fail review-wired 'does not import' -- checkspec review "${R[@]}" --pairs "$F/review-pairs-good.txt" --wired CheckFixtures.ReviewBad:CheckFixtures.Proof
  # without --wired the production pair is required (absent here), so the wiring check cannot be skipped
  expect_fail review-wired 'ConsensusTests does not import ConsensusTests.ReviewAxioms' -- checkspec review "${R[@]}" --pairs "$F/review-pairs-good.txt"

  echo "snapshot"
  local saved_update=$update_snapshot
  update_snapshot=0
  expect_pass snapshot_check CheckFixtures.GoodSpec "$F/goodspec.snapshot" "$F/goodspec.canonical" "${FIXSRC[@]}"
  expect_pass snapshot_check CheckFixtures.SnapA "$F/snapA.snapshot" "$F/snapA.canonical" "${FIXSRC[@]}" --no-root
  expect_fail snapshot 'readable' -- snapshot_check CheckFixtures.SnapB "$F/snapA.snapshot" "$F/snapA.canonical" "${FIXSRC[@]}" --no-root
  # SnapHidden prints exactly like SnapA (instance argument hidden): the readable file is equal,
  # only the canonical file sees the change.
  expect_fail snapshot 'FAIL\[snapshot\] canonical' -- snapshot_check CheckFixtures.SnapHidden "$F/snapA.snapshot" "$F/snapA.canonical" "${FIXSRC[@]}" --no-root
  selftest_count=$((selftest_count + 1))
  checkspec snapshot --lib CheckFixtures.SnapHidden "${FIXSRC[@]}" --no-root --out "$TMP/hidden.readable" >/dev/null 2>&1 || true
  if diff -q "$F/snapA.snapshot" "$TMP/hidden.readable" >/dev/null; then
    echo "  ok   SnapHidden readable snapshot equals SnapA's (the canonical file is the meaning check)"
  else
    echo "  BAD  SnapHidden readable snapshot differs from SnapA's: the fixture no longer shows a hidden change"
    selftest_fail=1
  fi
  update_snapshot=$saved_update

  echo "spec source"
  expect_pass checkspec spec-source --lib CheckFixtures.GoodSpec "${FIXSRC[@]}"
  expect_fail spec-source 'run_cmd' -- checkspec spec-source --lib CheckFixtures.BadMetaThm "${FIXSRC[@]}"
  expect_fail spec-source 'example' -- checkspec spec-source --lib CheckFixtures.BadExample "${FIXSRC[@]}"
  # indented commands (Lean accepts them; the run_cmd ran at compile time)
  expect_fail spec-source 'BadIndented/A.lean:12: example' -- checkspec spec-source --lib CheckFixtures.BadIndented "${FIXSRC[@]}"
  expect_fail spec-source 'BadIndented/A.lean:13: theorem' -- checkspec spec-source --lib CheckFixtures.BadIndented "${FIXSRC[@]}"
  expect_fail spec-source 'BadIndented/A.lean:14: run_cmd' -- checkspec spec-source --lib CheckFixtures.BadIndented "${FIXSRC[@]}"
  # wrapped (`set_option … in`, `open … in`) and multi-line commands
  expect_fail spec-source 'BadWrapped/A.lean:11: example' -- checkspec spec-source --lib CheckFixtures.BadWrapped "${FIXSRC[@]}"
  expect_fail spec-source 'BadWrapped/A.lean:14: example' -- checkspec spec-source --lib CheckFixtures.BadWrapped "${FIXSRC[@]}"
  expect_fail spec-source 'BadWrapped/A.lean:18: theorem' -- checkspec spec-source --lib CheckFixtures.BadWrapped "${FIXSRC[@]}"
  # a character literal '"' does not hide code; raw strings are reported
  expect_fail spec-source 'BadCharLit/A.lean:11: example' -- checkspec spec-source --lib CheckFixtures.BadCharLit "${FIXSRC[@]}"
  expect_fail spec-source 'BadCharLit/A.lean:14: raw string' -- checkspec spec-source --lib CheckFixtures.BadCharLit "${FIXSRC[@]}"
  # source-only fixtures (not compiled): attributes that register user code, and look-alike words
  expect_fail spec-source 'SrcAttr/A.lean:3: attribute init' -- checkspec spec-source --lib SrcAttr --src "$F/source" --no-root
  expect_fail spec-source 'SrcAttr/A.lean:4: attribute tactic' -- checkspec spec-source --lib SrcAttr --src "$F/source" --no-root
  expect_fail spec-source 'SrcAttr/A.lean:7: attribute app_unexpander' -- checkspec spec-source --lib SrcAttr --src "$F/source" --no-root
  expect_pass checkspec spec-source --lib SrcGood --src "$F/source" --no-root

  echo "source bans"
  expect_pass source_ban "$CF/GoodSpec" "$CF/GoodSpec.lean"
  expect_fail source 'sorry' -- source_ban "$CF/BadSorry"
  expect_fail source 'native_decide' -- source_ban "$CF/BadNative"
  expect_fail source 'missing input' -- source_ban "$CF/GoodSpec" "$CF/DoesNotExist"

  echo "docs"
  expect_pass docs_check "$F/README-good.md" "$CF/GoodSpec"
  expect_fail docs 'README-missing' -- docs_check "$F/README-missing.md" "$CF/GoodSpec"

  echo "$selftest_count self-tests"
  return $selftest_fail
}

# --- driver --------------------------------------------------------------------------------------

overall=0
run_step() {
  local label="$1"; shift
  echo "--- $label ---"
  local rc=0
  set +e; "$@"; rc=$?; set -e
  if [[ $rc -eq 0 ]]; then
    printf 'PASS  %s\n' "$label"
  else
    printf 'FAIL  %s\n' "$label"
    overall=1
  fi
  return 0
}

run_step "0 build (lake build; lake build CheckFixtures)" step_build
if [[ $overall -ne 0 ]]; then
  echo "check.sh: build failed; no check runs on stale .olean files" >&2
  exit 1
fi
run_step "1 sanity (metadata queries)" step_sanity
run_step "2 axioms (${LIBS[*]}, roots included)" step_axioms
run_step "3 source bans" step_source
if [[ $quick -eq 1 ]]; then
  echo "SKIP  4 self-tests (--quick)"
else
  run_step "4 self-tests (scripts/fixtures)" step_selftests
fi

echo
if [[ $overall -eq 0 ]]; then
  echo "check.sh: ALL CHECKS PASSED"
else
  echo "check.sh: FAILURES PRESENT" >&2
fi
exit "$overall"
