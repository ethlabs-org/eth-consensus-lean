#!/usr/bin/env bash
# FGSA checks: build (--wfail), root imports, native evaluation outside
# comments, the direct-import allowlist with its directory rules, the Q1/Q5
# boundary grep, the axiom check (with build coverage and the import-closure
# check), the lease-instance check, the ext-name check of the FG pin table, and
# the negative controls of these checks.
# Import headers are parsed after comment removal (G13 Astra M2, Opus m1). The
# parser fails closed, and the axiom script checks the same allowlist again on
# the compiled import data (G13 fold MINOR-2). Source files: `find -L` with
# `-iname '*.lean'` (symbolic links followed, extension in any case).
# Run: bash scripts/check-fgsa.sh. Exit 0 when every check passes.
# JOBS bounds this script's pool (default Mac 3, Linux 6; env wins).
# GATE_SLOTS caps shared controls and heavy steps (Mac 3, Linux 4; env wins).
# JOBS alone does not set machine concurrency.
# --no-negative or NEG=0 keeps all positive checks without negative controls.
# SOURCE_ONLY=1 runs the static checks and exits before compiled checks or controls.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/gate-common.sh
source scripts/import-policy.sh
if [ "${SOURCE_ONLY:-0}" != 1 ]; then
  gate_options "$@"
  for f in scripts/CheckFGSAAxioms.lean scripts/CheckFGSALease.lean scripts/CheckFGSAExt.lean \
      scripts/CheckFGSAOldReads.lean scripts/baselines/fgsa-old-reads.txt; do
    [ -f "$f" ] || { echo "MISSING CHECK SCRIPT: $f"; exit 2; }
  done
fi

# Remove comments with a small tokenizer that knows strings, character
# literals, raw strings (r"...", r#"..."#) and nested block comments. A "--"
# in a string does not start a comment, and a "/-" in a line comment does not
# open a block comment.
strip_comments='
  local $/; my $s = <STDIN>; my $o = ""; my $d = 0;
  while ((pos($s) // 0) < length $s) {
    if ($d > 0) {
      if    ($s =~ /\G\/-/gc)   { $d++ }
      elsif ($s =~ /\G-\//gc)   { $d--; $o .= " " }
      elsif ($s =~ /\G(\n)/gc)  { $o .= $1 }
      else                      { $s =~ /\G./gcs }
    }
    elsif ($s =~ /\G--[^\n]*/gc)                         { }
    elsif ($s =~ /\G\/-/gc)                              { $d = 1 }
    elsif ($s =~ /\Gr(#*)".*?"\1/gcs)                    { $o .= "\"\"" }
    elsif ($s =~ /\G"(?:\\.|[^"\\])*"/gcs)               { $o .= "\"\"" }
    elsif ($s =~ /\G([\w\p{N}.!?][\w\p{N}.!?\x27]*)/gc)  { $o .= $1 }
    elsif ($s =~ /\G\x27(?:\\.|[^\\\x27])\x27/gc)        { $o .= "c" }
    else                                                 { $s =~ /\G(.)/gcs; $o .= $1 }
  }
  print $o;'
# The modules of the import header of a file, one per line, after comment
# removal: [module] then [public] [meta] import [all] <Name>, any whitespace.
# Fail closed: if the rest of the file still has the token `import` or
# `prelude` (for example after a `prelude` line or a module name with `«`), it
# prints the line `!UNPARSED`.
header_imports='
  local $/; my $s = <STDIN>;
  $s =~ s/^\s+//; $s =~ s/^module\s+//;
  while ($s =~ s/^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z0-9_.]*)\s*//) {
    print "$1\n";
  }
  print "!UNPARSED\n" if $s =~ /(?<![\w.\x27!?])(?:import|prelude)(?![\w\x27!?])/;'
imports_of() { perl -CSD -e "$strip_comments" < "$1" | perl -CSD -e "$header_imports"; }
# The FGSA source files under base directory $1, relative to it.
source_files() { gate_source_files "$1" AvailableChainFGSA; }

# Root imports under base directory $1: every source file outside Tests/ is a root import.
# Tests/ modules need no root import (backlog C23, lead 2026-10-01): the library
# glob `AvailableChainFGSA.*` builds every module. A new root import of a test fails
# check-layers B7-TESTS; the older test imports of the root stay (baseline).
check_lib_glob() {
  local lakefile=$1
  python3 - "$lakefile" <<'PY' || { echo "MISSING GLOB: AvailableChainFGSA needs globs = [\"AvailableChainFGSA.*\"] (tests are built only by the glob)"; return 1; }
import sys, tomllib
libs = tomllib.load(open(sys.argv[1], "rb")).get("lean_lib", [])
lib = [l for l in libs if l.get("name") == "AvailableChainFGSA"]
sys.exit(0 if len(lib) == 1 and lib[0].get("globs") == ["AvailableChainFGSA.*"] else 1)
PY
}
test_modules() {
  source_files "$1" | grep -i '^AvailableChainFGSA/Tests/' |
    sed -E 's/\.[lL][eE][aA][nN]$//; s|/|.|g' || true
}
check_root_imports() {
  local base=$1 missing
  missing=$(comm -23 \
    <(source_files "$base" | grep -iv '^AvailableChainFGSA/Tests/' |
        sed -E 's/\.[lL][eE][aA][nN]$//; s|/|.|g' | sort) \
    <(imports_of "$base/$(gate_source_file "$base" AvailableChainFGSA.lean)" | sort))
  [ -z "$missing" ] || { echo "NOT IMPORTED BY THE ROOT: $missing"; return 1; }
  if imports_of "$base/$(gate_source_file "$base" AvailableChainFGSA.lean)" |
      grep -qx '!UNPARSED'; then
    echo "UNPARSED IMPORT HEADER: AvailableChainFGSA.lean"; return 1
  fi
}

# The direct-import allowlist (plan, Global Constraints "Imports") under base
# directory $1. Internal imports follow the layers: Model/ imports Model/;
# Statements/ imports Model/ and Statements/; Proofs/ imports Model/,
# Statements/ and Proofs/; Tests/ and the root import any FGSA module. The root
# imports only FGSA modules. External: AvailableChainModel.*,
# AvailableChainGridCO.Model.Protocol, AvailableChainSA.Model.Protocol,
# AvailableChainSimplexFG.*, Mathlib.*; AvailableChainGridCO.Proofs.* only in
# Proofs/; AvailableChainKitFG.* only in Statements/ and Proofs/;
# AvailableChainGeneric.Proofs.* only in Proofs/ (GEN-FIRST/F-31: FG-SA proofs instantiate
# the Gen proofs; lead ruling 2026-10-01, SYN L56; was Proofs.Pure.Fold only, the F-13 switch).
check_direct_imports() {
  local base=$1 bad=0 f rel layer m
  for f in $(source_files "$base") AvailableChainFGSA.lean; do
    rel=${f#AvailableChainFGSA/}
    if [ "$f" = AvailableChainFGSA.lean ]; then layer=root; else layer=${rel%%/*}; fi
    for m in $(imports_of "$base/$(gate_source_file "$base" "$f")"); do
      if [ "$m" = '!UNPARSED' ]; then echo "UNPARSED IMPORT HEADER: $f"; bad=1; continue; fi
      fgsa_import_allowed "$layer" "$m" && continue
      echo "IMPORT NOT ALLOWED: $f imports $m"; bad=1
    done
  done
  return $bad
}

# Q1/Q5 boundary (plan, Global Constraints) on comment-free text.
check_boundary() {
  local base=$1 bad=0 f
  for f in $(source_files "$base") AvailableChainFGSA.lean; do
    if perl -CSD -e "$strip_comments" < "$base/$(gate_source_file "$base" "$f")" |
        grep -nE 'ProtocolSpec|Generic\.Run|(^|[^A-Za-z0-9_])(Run|Env)([^A-Za-z0-9_]|$)|World|Interface|Claims|pendingRow'; then
      echo "ENGINE REFERENCE in $f"; bad=1
    fi
  done
  return $bad
}

if [ "${SOURCE_ONLY:-0}" != 1 ]; then
  echo "== lake build --wfail AvailableChainFGSA"
  gate_build --wfail AvailableChainFGSA
  # The check support library (scripts/AvailableChainCheckSupport/) is not a
  # default target: build it here, so that a clean checkout works.
  echo "== lake build --wfail AvailableChainCheckSupport"
  gate_build --wfail AvailableChainCheckSupport
fi
echo "== no protocol library imports the check support library"
! python3 -B scripts/source_layout.py --nul files |
  xargs -0 grep -lE 'import[[:space:]]+AvailableChainCheckSupport' || {
    echo "PROTOCOL LIBRARY IMPORTS AvailableChainCheckSupport"; exit 1; }
python3 -B scripts/current-inventory.py fgsa scripts/fgsa-expected.txt
echo "== root imports"
check_root_imports . || exit 2
echo "== library glob (tests are built by the glob)"
check_lib_glob lakefile.toml || exit 2
echo "== native evaluation"
status=0
for f in $(source_files .) AvailableChainFGSA.lean; do
  if perl -CSD -e "$strip_comments" < "$(gate_source_file . "$f")" |
      grep -nE '(^|[^A-Za-z0-9_.])native_decide([^A-Za-z0-9_]|$)|\+native|native := true|ofReduceBool|ofReduceNat' >/dev/null; then
    echo "native evaluation in $f"; status=1
  fi
done
[ $status -eq 0 ] || exit 1
echo "== direct imports"
check_direct_imports . || exit 1
echo "== Q1/Q5 boundary"
check_boundary . || exit 1
if [ "${SOURCE_ONLY:-0}" = 1 ]; then
  echo "FGSA source checks: PASS"
  exit 0
fi
echo "== axioms, build coverage, import closure"
# Tests/ modules need no root import (C23): check them as extra roots.
TEST_ROOTS=()
for m in $(test_modules .); do TEST_ROOTS+=(--root "$m"); done
gate_inventory_args scripts/fgsa-expected.txt
gate_with_slot python3 -B scripts/write-check-inventories.py --scope fgsa --check
# The contract remains explicit and independent of the generated inventory.
gate_with_slot lake env lean --run scripts/CheckFGSAAxioms.lean "${TEST_ROOTS[@]}" --expect \
  AvailableChain.FGSA.parentFoldState AvailableChain.FGSA.Next.headVoteNext "${GATE_INVENTORY[@]}"
echo "== lease instances"
gate_with_slot lake env lean --run scripts/CheckFGSALease.lean
# Old-read audit (fg5-rulings STOP 6, ruling 7): no old SimplexFG store fold, old
# row validity or finality read of the old derive in the active FG-SA path except
# the `allow` lines, and no height-only read of the old derive except the `height`
# lines (ruling 7 named exceptions) of scripts/baselines/fgsa-old-reads.txt (DATA).
# NEG=1 also runs the in-process negative controls (planted direct, KitFG-
# lemma, `(derive …).F` and height-only reads; dropped and extra data lines).
echo "== old-read audit"
gate_build --wfail AvailableChainFGSAClaims AvailableChainFGSAProofs AvailableChainFGSARun
if [ "$NEG" = 1 ]; then
  gate_with_slot lake env lean --run scripts/CheckFGSAOldReads.lean --controls
else
  gate_with_slot lake env lean --run scripts/CheckFGSAOldReads.lean
fi
# The `leanIn "AvailableChainFGSA"` names of AvailableChainKitFG/Pins.lean get
# the checks of a `.lean` name (existence, the library of the declaring module,
# the three standard axioms) in this environment; see scripts/CheckFGSAExt.lean.
# FGPinIds.lean rejects a library that is not on its allowlist. The pin gate for
# a pin with `leanIn` evidence is check-fg.sh plus this script.
# A lower bound on the records: when the comment-free source of Pins.lean has a
# `.leanIn "…"` clause, the emitter must print at least one ext record.
echo "== ext names of the FG pin table"
neg=$(mktemp -d "$PWD/.lake/fgsa-neg.XXXXXX")
trap 'rm -rf "$neg"' EXIT
gate_build --wfail AvailableChainSimplexFG AvailableChainKitFG
pins=$(gate_source_path AvailableChainKitFG.Pins)
nlean=$(perl -CSD -e "$strip_comments" < "$pins" | grep -o '\.leanIn ""' |
  wc -l | tr -d ' ')
check_ext() {  # EMITTER: its ext records, the lower bound, and CheckFGSAExt.lean
  lake env lean --run "$1" --ext > "$neg/extrecs" || {
    local rc=$?
    [ "$rc" -lt 128 ] || return "$rc"
    echo "EMITTER FAILED (--ext)"; return 2
  }
  local n
  n=$(tail -1 "$neg/extrecs" | sed -n 's/^END ext \([0-9][0-9]*\)$/\1/p')
  if [ "$nlean" -gt 0 ] && [ "${n:-0}" -eq 0 ]; then
    echo "NO EXT RECORDS: $nlean leanIn clauses in Pins.lean"; return 1
  fi
  lake env lean --run scripts/CheckFGSAExt.lean "$neg/extrecs"
}
gate_with_slot check_ext scripts/FGPinIds.lean

# Keep each fixture private; only completed logs go to stdout.
gate_pool_init "$neg/controls"
if [ "$NEG" = 1 ]; then echo "== negative controls"
else echo "negative controls: SKIPPED (NEG=0)"; fi
# expect_fail NAME CODE OUT PATTERN...: the check failed with CODE and printed
# every PATTERN (fixed strings).
expect_fail() {
  local name=$1 code=$2 out=$3 p; shift 3
  gate_control_check "$name" "$code" "$out" || exit 1
  if [ "$code" -eq 0 ]; then echo "$out"; echo "NEGATIVE CONTROL NOT DETECTED: $name"; exit 1; fi
  for p in "$@"; do
    if [[ $out != *"$p"* ]]; then
      echo "$out"; echo "NEGATIVE CONTROL $name: missing \"$p\""; exit 1
    fi
  done
  echo "rejected, as expected: $name"
}
# A scratch copy of the source tree for the import controls.
mk_tree() {
  mkdir -p "$neg/tree"
  cp -R "$(gate_source_dir AvailableChainFGSA)" \
    "$(gate_source_path AvailableChainFGSA)" "$neg/tree/"
  printf '[[lean_lib]]\nname = "AvailableChainFGSA"\nglobs = ["AvailableChainFGSA.*"]\n' \
    > "$neg/tree/lakefile.toml"; }
run() { set +e; out=$("$@" 2>&1); code=$?; set -e; }

control_unlisted() {
mk_tree
printf 'module\npublic import AvailableChainLStar.Model.Protocol\n' > "$neg/tree/AvailableChainFGSA/Model/NegA.lean"
echo 'public import AvailableChainFGSA.Model.NegA' >> "$neg/tree/AvailableChainFGSA.lean"
run check_direct_imports "$neg/tree"
expect_fail "unlisted library" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/NegA.lean imports AvailableChainLStar.Model.Protocol"
}

control_layer() {
mk_tree
printf 'module\npublic import AvailableChainKitFG.Correspondence\n' > "$neg/tree/AvailableChainFGSA/Model/NegB.lean"
printf 'module\npublic import AvailableChainFGSA.Proofs.Carrier\n' > "$neg/tree/AvailableChainFGSA/Statements/NegB.lean"
printf 'module\npublic import AvailableChainGeneric.Proofs.Pure.Walk\n' > "$neg/tree/AvailableChainFGSA/Statements/NegB2.lean"
run check_direct_imports "$neg/tree"
expect_fail "wrong-layer import" $code "$out" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/NegB.lean imports AvailableChainKitFG.Correspondence" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Statements/NegB.lean imports AvailableChainFGSA.Proofs.Carrier" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Statements/NegB2.lean imports AvailableChainGeneric.Proofs.Pure.Walk"
}

control_import_forms() {
mk_tree
printf 'module\npublic import /- dependency -/ AvailableChainFramework.Profile\npublic\n  import\n  AvailableChainSAPC.Model.Choice\n' \
  > "$neg/tree/AvailableChainFGSA/Proofs/NegC.lean"
run check_direct_imports "$neg/tree"
expect_fail "import after a comment and a line break" $code "$out" \
  "imports AvailableChainFramework.Profile" "imports AvailableChainSAPC.Model.Choice"
}

orphan_tree() {
mk_tree
# Tests/ needs no root import (C23), so the orphans live in Model/.
printf 'module\n@[expose] public section\ntheorem negOrphan : False := sorry\nend\n' \
  > "$neg/tree/AvailableChainFGSA/Model/NegOrphan.lean"
printf 'module\n@[expose] public section\ntheorem negOrphanC : False := sorry\nend\n' \
  > "$neg/tree/AvailableChainFGSA/Model/NegOrphanC.LEAN"
echo '/- public import AvailableChainFGSA.Model.NegOrphan -/' >> "$neg/tree/AvailableChainFGSA.lean"
}

control_orphan() {
orphan_tree
run check_root_imports "$neg/tree"
expect_fail "orphan modules behind a commented import and with a .LEAN name (root check)" \
  $code "$out" "NOT IMPORTED BY THE ROOT: AvailableChainFGSA.Model.NegOrphan" \
  "AvailableChainFGSA.Model.NegOrphanC"
}

control_glob() {
# C23: without the library glob a test module (no root import) escapes the build.
sed '/^globs = \["AvailableChainFGSA\.\*"\]$/d' lakefile.toml > "$neg/lakefile-noglob.toml"
run check_lib_glob "$neg/lakefile-noglob.toml"
expect_fail "library glob removed (tests escape the build)" $code "$out" "MISSING GLOB: AvailableChainFGSA"
}

# C23 (lead 2026-10-01): a broken Tests/ module that the root does not import must
# fail the build step (`lake build AvailableChainFGSA` builds the glob). The module
# is in a private copy of the current tree and all stable Lake data. The copy
# uses file clones where supported; it never shares writable build outputs.
control_glob_build() {
local m=NegBuildC23 f
f=$(gate_source_path AvailableChainFGSA.Tests.NegBuildC23)
[ ! -e "$f" ] || { echo "CONTROL SETUP FAIL: $f exists"; exit 1; }
local tree=$neg/build-tree
gate_copy_control_tree "$PWD" "$tree"
local body='trap "rm -f $0; find .lake/build -path \"*AvailableChainFGSA/Tests/$1.*\" -delete 2>/dev/null; true" EXIT
printf "module\n\npublic section\n\ntheorem negBuildC23 : False := rfl\n" > "$0"
lake build AvailableChainFGSA'
run bash -c 'cd "$1" || exit; shift; exec bash -c "$@"' \
  control-build "$tree" "$body" "$f" "$m"
[ ! -e "$tree/$f" ] || { echo "CONTROL CLEANUP FAIL: $tree/$f was left behind"; exit 1; }
[ ! -e "$f" ] || { echo "CONTROL CLEANUP FAIL: $f was left behind"; exit 1; }
expect_fail "broken unimported test module fails the library build" $code "$out" \
  "AvailableChainFGSA.Tests.NegBuildC23"
}

control_closure() {
orphan_tree
# The compiled checks: the orphan file (with a sorry) against the build, and a
# forbidden library in the import closure.
cat > "$neg/FGSAClosureNeg.lean" <<'LEAN'
import AvailableChainSAPC.Model.Choice
LEAN
lake env lean -o "$neg/FGSAClosureNeg.olean" "$neg/FGSAClosureNeg.lean"
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSAAxioms.lean --root FGSAClosureNeg --files "$0/tree/AvailableChainFGSA"' "$neg"
expect_fail "orphan modules and forbidden closure (axiom script)" $code "$out" \
  "NOT IN THE BUILD: AvailableChainFGSA.Model.NegOrphan " \
  "NOT IN THE BUILD: AvailableChainFGSA.Model.NegOrphanC " \
  "FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: AvailableChainSAPC"
}

header_tree() {
# Header forms and file names that an earlier parser missed (G13 fold MINOR-2;
# the auditor's files in scripts/fgsa-controls/): a module name with «», a
# `prelude` line, a .LEAN file, and a linked directory. Each imports L*, which
# the allowlist forbids. First the text checks, then the compiled check (the
# four modules compiled as FGSA modules, over a copy of the FGSA build).
mk_tree
cp scripts/fgsa-controls/AdvG.lean scripts/fgsa-controls/AdvP.lean \
  scripts/fgsa-controls/AdvCase.LEAN "$neg/tree/AvailableChainFGSA/Model/"
mkdir -p "$neg/sub" && cp scripts/fgsa-controls/Sub/X.lean "$neg/sub/"
ln -s "$neg/sub" "$neg/tree/AvailableChainFGSA/Model/Sub"
printf 'public import AvailableChainFGSA.Model.%s\n' AdvG AdvP AdvCase Sub.X \
  >> "$neg/tree/AvailableChainFGSA.lean"
}

control_header_text() {
header_tree
run check_direct_imports "$neg/tree"
expect_fail "header forms and file names (text allowlist)" $code "$out" \
  "UNPARSED IMPORT HEADER: AvailableChainFGSA/Model/AdvG.lean" \
  "UNPARSED IMPORT HEADER: AvailableChainFGSA/Model/AdvP.lean" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/AdvCase.LEAN imports AvailableChainLStar.Model.Protocol" \
  "IMPORT NOT ALLOWED: AvailableChainFGSA/Model/Sub/X.lean imports AvailableChainLStar.Model.Protocol"
}

control_boundary() {
header_tree
run check_boundary "$neg/tree"
expect_fail "Q1/Q5 grep in a .LEAN file and a linked directory" $code "$out" \
  "ENGINE REFERENCE in AvailableChainFGSA/Model/AdvCase.LEAN" \
  "ENGINE REFERENCE in AvailableChainFGSA/Model/Sub/X.lean"
}

control_header_compiled() {
header_tree
mkdir -p "$neg/c"
cp -R .lake/build/lib/lean/AvailableChainFGSA .lake/build/lib/lean/AvailableChainFGSA.* "$neg/c/"
for m in AdvG:AdvG.lean AdvP:AdvP.lean AdvCase:AdvCase.LEAN Sub/X:Sub/X.lean; do
  mkdir -p "$neg/c/AvailableChainFGSA/Model/Sub"
  lake env lean -o "$neg/c/AvailableChainFGSA/Model/${m%%:*}.olean" "$neg/tree/AvailableChainFGSA/Model/${m#*:}"
done
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSAAxioms.lean --root AvailableChainFGSA.Model.AdvG --root AvailableChainFGSA.Model.AdvP --root AvailableChainFGSA.Model.AdvCase --root AvailableChainFGSA.Model.Sub.X --files "$0/tree/AvailableChainFGSA"' "$neg"
expect_fail "header forms and file names (compiled allowlist)" $code "$out" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.AdvG imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.AdvP imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.AdvCase imports AvailableChainLStar.Model.Protocol" \
  "COMPILED IMPORT NOT ALLOWED: AvailableChainFGSA.Model.Sub.X imports AvailableChainLStar.Model.Protocol"
}

control_lease() {
# Lease controls: a direct default-instance call; the anchored gate and tick
# (`gateFrom`, `clockFrom`) at the grid policy (spec sync C1); an alias wrapper
# with its own policy parameter in another namespace (Astra M1); a generic
# wrapper whose policy binder has an alias type (Opus m2); an imported wrapper
# that fixes the default instance inside.
cat > "$neg/FGSALeaseNeg.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.FGSA
/-- A GridCO gate at the default instance `gridLeasePolicy`. -/
def leaseNegControl (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.gate p st r
/-- The anchored GridCO gate at `gridLeasePolicy`. -/
def leaseNegGateFrom (p : GridCO.Params) (a : Block) (st : GridCO.State 1) (r : Nat) :
    GridCO.State 1 :=
  @GridCO.gateFrom GridCO.gridLeasePolicy p 1 .block a st r
/-- The anchored GridCO tick at `gridLeasePolicy`. -/
def leaseNegClockFrom (p : GridCO.Params) (a : Block) (st : GridCO.State 1) (t : Int) :
    GridCO.State 1 :=
  @GridCO.clockFrom GridCO.gridLeasePolicy p 1 .block a st t
end AvailableChain.FGSA
namespace AvailableChain.LeaseAuditAlias
def gate (_policy : GridCO.LeasePolicy) (p : GridCO.Params)
    (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.gate GridCO.gridLeasePolicy p 1 .block st r
end AvailableChain.LeaseAuditAlias
namespace AvailableChain.FGSA
def badGate (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  AvailableChain.LeaseAuditAlias.gate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
namespace AvailableChain.GridCO
abbrev PolicyAlias : Type := LeasePolicy
def sneakyGate [PolicyAlias] (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
end AvailableChain.GridCO
namespace AvailableChain.FGSA
def badGate2 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  @GridCO.sneakyGate GridCO.slowLeasePolicy p st r
end AvailableChain.FGSA
LEAN
cat > "$neg/FGSALeaseLib.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.GridCO
/-- An imported wrapper with no policy parameter that fixes the default. -/
def fixedGate (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
end AvailableChain.GridCO
namespace LeaseMk
/-- Outside `AvailableChain`: a new policy value built with the constructor. -/
def mkGate (p : AvailableChain.GridCO.Params) (st : AvailableChain.GridCO.State 1) (r : Nat) :
    AvailableChain.GridCO.State 1 :=
  @AvailableChain.GridCO.gate ⟨false⟩ p 1 .block st r
end LeaseMk
LEAN
cat > "$neg/FGSALeaseUse.lean" <<'LEAN'
import FGSALeaseLib
namespace AvailableChain.FGSA
def badGate3 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  GridCO.fixedGate p st r
def badGate4 (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) : GridCO.State 1 :=
  LeaseMk.mkGate p st r
end AvailableChain.FGSA
LEAN
for m in FGSALeaseNeg FGSALeaseLib FGSALeaseUse; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean FGSALeaseNeg FGSALeaseUse' "$neg"
expect_fail "lease controls" $code "$out" \
  "leaseNegControl: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "leaseNegGateFrom: AvailableChain.GridCO.gateFrom at AvailableChain.GridCO.gridLeasePolicy" \
  "leaseNegClockFrom: AvailableChain.GridCO.clockFrom at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.LeaseAuditAlias.gate: has a policy parameter" \
  "AvailableChain.GridCO.sneakyGate: has a policy parameter" \
  "AvailableChain.GridCO.fixedGate: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "LeaseMk.mkGate: mentions AvailableChain.GridCO.LeasePolicy.mk (reach)"
}

control_imported_lease() {
# Imported definitions (G13 fold MINOR-1; the auditor's AdvLib/AdvUse in
# scripts/fgsa-controls/): a let-bound and a beta-bound default policy, a
# private wrapper, an irreducible alias of the policy type, and a wrapper
# outside the namespace AvailableChain (the reachability backstop).
cp scripts/fgsa-controls/AdvLib.lean scripts/fgsa-controls/AdvUse.lean "$neg/"
for m in AdvLib AdvUse; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean AdvUse' "$neg"
expect_fail "lease controls in imported definitions" $code "$out" \
  "AvailableChain.GridCO.fixedLet: AvailableChain.GridCO.gate at #0" \
  "AvailableChain.GridCO.fixedBeta: AvailableChain.GridCO.gate at #0" \
  "AdvLib.0.AvailableChain.GridCO.fixedPriv: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.FGSA.useIrr: AvailableChain.GridCO.genI at cast" \
  "Evil.fixedGate: mentions AvailableChain.GridCO.gridLeasePolicy (reach)"
}

lease_owner_files() {
# Generated constants (T7.2 R-A; the owner map of
# scripts/AvailableChainCheckSupport/GeneratedOwner.lean). NEGATIVE: an
# imported definition with no policy parameter that fixes the default policy,
# used through its generated equation (`eq_def`): its owner is inspected and
# refused. POSITIVE: `split` and `simp` over `GridCO.admitVote` and
# `GridCO.excludes` (private matcher equations and sparse `casesOn`
# equations): no report. OWNER PATH ONLY: a generated equation with a policy
# parameter, realized in the scanned module, is skipped, and only its owner's
# inspection refuses it. No control separates the owner map from the earlier
# `eq_<k>`/`eq_def` rule: that rule was stricter than needed, never unsound (it
# scanned a private generated constant as an ordinary one). The owner map is
# safe: every generated constant that it skips has its owner inspected, and
# the policy is checked at every use.
cat > "$neg/LeaseOwnLib.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.GridCO
/-- An imported definition with no policy parameter that fixes the default. -/
def ownerFixedGate (p : Params) (st : State 1) (r : Nat) : State 1 :=
  @gate gridLeasePolicy p 1 .block st r
/-- A policy-generic imported definition that passes its own policy through a
beta-redex: at `gate` the policy is a bound variable, not an own parameter. -/
def ownerBetaGen [L : LeasePolicy] (p : Params) (st : State 1) (r : Nat) : State 1 :=
  (fun (pol : LeasePolicy) => @gate pol p 1 .block st r) L
end AvailableChain.GridCO
LEAN
cat > "$neg/LeaseOwnOnly.lean" <<'LEAN'
import LeaseOwnLib
-- Realizes the equation `ownerBetaGen.eq_1` (it has the policy parameter `L`)
-- in this scanned module; no declaration of this module mentions the owner.
attribute [simp] AvailableChain.GridCO.ownerBetaGen.eq_1
namespace AvailableChain.FGSA
def ownOnlyAnchor : Nat := 0
end AvailableChain.FGSA
LEAN
cat > "$neg/LeaseOwnNeg.lean" <<'LEAN'
import LeaseOwnLib
namespace AvailableChain.FGSA
theorem negLeaseOwner (p : GridCO.Params) (st : GridCO.State 1) (r : Nat) :
    GridCO.ownerFixedGate p st r = GridCO.ownerFixedGate p st r := by
  rw [GridCO.ownerFixedGate.eq_def]
end AvailableChain.FGSA
LEAN
cat > "$neg/LeaseOwnPos.lean" <<'LEAN'
import AvailableChainFGSA
namespace AvailableChain.FGSA
theorem posLeaseSplit (q : GridCO.Params) {n : Nat} (st : GridCO.State n) (o : GridCO.Wire n) :
    (GridCO.admitVote q st o).now = st.now := by
  unfold GridCO.admitVote
  split
  · dsimp only; split <;> rfl
  · rfl
theorem posLeaseSimp (q : GridCO.Params) {n : Nat} {st st' : GridCO.State n}
    (hv : st'.votes = st.votes) (hn : st'.now = st.now) (o : GridCO.Wire n) :
    GridCO.excludes q st' o = GridCO.excludes q st o := by
  simp only [GridCO.excludes, GridCO.votesAt, hv, hn]
end AvailableChain.FGSA
LEAN
}

compile_lease_owner() {
for m in "$@"; do
  lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean -o "$0/$1.olean" "$0/$1.lean"' "$neg" "$m"
done
}

control_lease_owner() {
lease_owner_files
compile_lease_owner LeaseOwnLib LeaseOwnNeg
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean LeaseOwnNeg' "$neg"
expect_fail "lease: a policy-fixing definition through its generated equation (owner)" $code "$out" \
  "AvailableChain.GridCO.ownerFixedGate: AvailableChain.GridCO.gate at AvailableChain.GridCO.gridLeasePolicy" \
  "AvailableChain.FGSA.negLeaseOwner: mentions AvailableChain.GridCO.gridLeasePolicy (reach)"
}

control_lease_owner_only() {
lease_owner_files
compile_lease_owner LeaseOwnLib LeaseOwnOnly
# OWNER PATH ONLY: the generated equation with a policy parameter is skipped
# (it is not scanned as a constant of the scanned module, so no "has a policy
# parameter" report), and its owner is inspected and refused. No other report
# (no backstop "reach" line): the owner mentions no default policy.
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean LeaseOwnOnly' "$neg"
expect_fail "lease: a policy-generic owner caught only through its skipped equation" $code "$out" \
  "BAD LEASE INSTANCE AvailableChain.GridCO.ownerBetaGen: AvailableChain.GridCO.gate at #0"
if [ "$(printf '%s\n' "$out" | grep -cF 'BAD LEASE INSTANCE')" -ne 1 ]; then
  echo "$out"; echo "NEGATIVE CONTROL lease owner path: a report other than the owner's"; exit 1
fi
}

positive_lease_owner() {
lease_owner_files
compile_lease_owner LeaseOwnPos
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGSALease.lean LeaseOwnPos' "$neg"
gate_control_check "lease owner map" "$code" "$out" || exit 1
if [ "$code" -ne 0 ] || [[ $out == *'BAD LEASE INSTANCE'* ]]; then
  echo "$out"; echo "POSITIVE CONTROL lease owner map: split/simp over GridCO.admitVote was refused"; exit 1
fi
echo "accepted, as expected: lease: generated equations of Grid CO model definitions (owner)"
}

control_ext_missing() {
printf 'ext AvailableChainFGSA AvailableChain.FGSA.noSuchName\nEND ext 1\n' > "$neg/extA"
run lake env lean --run scripts/CheckFGSAExt.lean "$neg/extA"
expect_fail "ext name that does not exist" $code "$out" \
  "EXT NAME NOT FOUND: AvailableChain.FGSA.noSuchName"
}

control_ext_library() {
printf 'ext AvailableChainFGSA AvailableChain.KitFG.finalLock\nEND ext 1\n' > "$neg/extB"
run lake env lean --run scripts/CheckFGSAExt.lean "$neg/extB"
expect_fail "ext name outside its library" $code "$out" \
  "EXT NAME OUTSIDE AvailableChainFGSA: AvailableChain.KitFG.finalLock"
}

control_ext_unknown() {
sed 's/^def table : List Pin := pins$/def table : List Pin := pins ++ [{ id := "neg.ctl.v1", sources := [], clauses := [⟨"control", .leanIn "AvailableChainFGSAX" [`AvailableChain.FGSA.gateStep]⟩] }]/' \
  scripts/FGPinIds.lean > "$neg/FGPinIdsC.lean"
grep -q 'AvailableChainFGSAX' "$neg/FGPinIdsC.lean" ||
  { echo "NEGATIVE CONTROL unknown ext library: the table line did not change"; exit 1; }
run env FGPINIDS="$neg/FGPinIdsC.lean" bash scripts/check-fg-pins.sh
expect_fail "unknown ext library (check-fg-pins.sh step 0)" $code "$out" \
  "UNKNOWN EXT LIBRARY: AvailableChainFGSAX (pin neg.ctl.v1, name AvailableChain.FGSA.gateStep)" \
  "EMITTER FAILED"
}

control_ext_empty() {
sed 's/^def table : List Pin := pins$/def table : List Pin := []/' scripts/FGPinIds.lean \
  > "$neg/FGPinIdsE.lean"
grep -q '^def table : List Pin := \[\]$' "$neg/FGPinIdsE.lean" ||
  { echo "NEGATIVE CONTROL no ext records: the table line did not change"; exit 1; }
run check_ext "$neg/FGPinIdsE.lean"
expect_fail "no ext records while Pins.lean has leanIn clauses" $code "$out" \
  "NO EXT RECORDS: $nlean leanIn clauses in Pins.lean"
}

control_ext_record() {
printf 'ext AvailableChainFGSA\nEND ext 1\n' > "$neg/extM"
run lake env lean --run scripts/CheckFGSAExt.lean "$neg/extM"
expect_fail "malformed ext record" $code "$out" "MALFORMED EXT RECORD: ext AvailableChainFGSA"
}

control_ext_trailer() {
printf 'ext AvailableChainFGSA AvailableChain.FGSA.gateStep\nEND ext 2\n' > "$neg/extT"
run lake env lean --run scripts/CheckFGSAExt.lean "$neg/extT"
expect_fail "malformed ext trailer" $code "$out" "MALFORMED TRAILER: END ext 2 (1 records)"
}

control_ext_axiom() {
# A private copy replaces the earlier dependency on the header control.
mkdir -p "$neg/c"
cp -R .lake/build/lib/lean/AvailableChainFGSA .lake/build/lib/lean/AvailableChainFGSA.* "$neg/c/"
printf 'theorem AvailableChain.FGSA.negExtAx : False := sorry\n' > "$neg/NegExtAx.lean"
lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean -o "$0/c/AvailableChainFGSA/NegExtAx.olean" "$0/NegExtAx.lean"' \
  "$neg" >/dev/null 2>&1 || {
    local rc=$?
    [ "$rc" -lt 128 ] || exit "$rc"
    echo "NEGATIVE CONTROL bad axiom: the module did not compile"; exit 1
  }
printf 'ext AvailableChainFGSA AvailableChain.FGSA.negExtAx\nEND ext 1\n' > "$neg/extX"
run lake env bash -c 'LEAN_PATH="$0/c:$LEAN_PATH" lean --run scripts/CheckFGSAExt.lean --root AvailableChainFGSA.NegExtAx "$0/extX"' "$neg"
expect_fail "ext name with a bad axiom" $code "$out" \
  "BAD AXIOM: AvailableChain.FGSA.negExtAx uses sorryAx"
}

control_fg_closure() {
# The FG import closure with AvailableChainFGSA in it (CheckFGAxioms.lean; the
# FG-environment control of check-fg.sh uses a stand-in library).
printf 'import AvailableChainFGSA\n' > "$neg/FGClosureNegFGSA.lean"
lake env lean -o "$neg/FGClosureNegFGSA.olean" "$neg/FGClosureNegFGSA.lean"
run lake env bash -c 'LEAN_PATH="$0:$LEAN_PATH" lean --run scripts/CheckFGAxioms.lean --root FGClosureNegFGSA' "$neg"
expect_fail "AvailableChainFGSA in the FG import closure" $code "$out" \
  "FORBIDDEN LIBRARY IN THE FG IMPORT CLOSURE: AvailableChainFGSA"
}

if [ "$NEG" = 1 ]; then
  gate_pool_add control_unlisted
  gate_pool_add control_layer
  gate_pool_add control_import_forms
  gate_pool_add control_orphan
  gate_pool_add control_glob
  gate_pool_add control_closure
  gate_pool_add control_header_text
  gate_pool_add control_boundary
  gate_pool_add control_header_compiled
  gate_pool_add control_lease
  gate_pool_add control_imported_lease
  gate_pool_add control_lease_owner
  gate_pool_add control_lease_owner_only
fi
# Keep the positive controls in their original order in both tiers.
gate_control_serial positive_lease_owner
if [ "$NEG" = 1 ]; then
  gate_pool_add control_ext_missing
  gate_pool_add control_ext_library
  # check-fg-pins has a build step. Drain the pool and use its build lock.
  gate_control_serial control_ext_unknown
  # The build control edits the real tree: run it alone, under the build lock.
  gate_control_serial control_glob_build
  gate_pool_add control_ext_empty
  gate_pool_add control_ext_record
  gate_pool_add control_ext_trailer
  gate_pool_add control_ext_axiom
  gate_pool_add control_fg_closure
fi
gate_pool_wait
echo "all FGSA checks pass"
