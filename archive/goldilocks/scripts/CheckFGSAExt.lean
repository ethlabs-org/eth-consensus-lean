import AvailableChainFGSA
import Lean.Util.CollectAxioms
open Lean

/-! Checks the `leanIn "AvailableChainFGSA"` names of `AvailableChainKitFG/Pins.lean`
in the FGSA environment. Input: a file with the output of `lake env lean --run
scripts/FGPinIds.lean --ext`, records `ext <lib> <name>` and the last line
`END ext <n>`. `scripts/check-fgsa.sh` runs it.

Parity with a `.lean` name of the pin table. A `.lean` name gets three checks:
it elaborates in `Pins.lean` (`example := @n`: it exists), it is a constant of a
module of the FG libraries (`FGPinIds.lean --check-names`), and its axioms are
only `propext`, `Classical.choice` and `Quot.sound` (`CheckFGAxioms.lean`).
There is no kind rule: a `.lean` name can be a theorem or a definition. Each
`ext` name gets the same three checks here: it is a constant of this
environment, the module that declares it is under the prefix `<lib>`, and its
axioms are only the three standard ones.

It checks BUILT data. Run `lake build AvailableChainFGSA` first, or use
`bash scripts/check-fgsa.sh`.
Run: `lake env lean --run scripts/CheckFGSAExt.lean [--root M] <records file>`.
`--root M` imports one more module (negative controls only).
Exit codes: 0 clean; 1 a name fails a check; 2 a usage error, a malformed
record or trailer, or a library that this environment does not check. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The library that this environment checks. -/
def lib : String := "AvailableChainFGSA"

def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFGSAExt", fileMap := .ofString "" } { env := env }

def main (args : List String) : IO UInt32 := do
  let usage := "USAGE: lake env lean --run scripts/CheckFGSAExt.lean [--root M] <file>"
  let (extra, file) ← match args with
    | ["--root", m, f] => pure (#[m.toName], f)
    | [f] => pure (#[], f)
    | _ => do IO.eprintln usage; return 2
  let ls := (← IO.FS.lines file).toList.filter (· != "")
  let some last := ls.getLast? | IO.println "NO END TRAILER"; return 2
  let recs := ls.dropLast
  unless last == s!"END ext {recs.length}" do
    IO.println s!"MALFORMED TRAILER: {last} ({recs.length} records)"; return 2
  let mut names : Array Name := #[]
  for r in recs do
    match r.splitOn " " with
    | ["ext", l, n] =>
      if l != lib then
        IO.println s!"EXT LIBRARY NOT CHECKED HERE: {l} ({n})"; return 2
      names := names.push n.toName
    | _ => IO.println s!"MALFORMED EXT RECORD: {r}"; return 2
  initSearchPath (← findSysroot)
  let env ← importModules ((#[`AvailableChainFGSA] ++ extra).map ({ module := · })) {}
  let mut bad := false
  for n in names do
    unless env.contains n do
      IO.println s!"EXT NAME NOT FOUND: {n}"; bad := true; continue
    let inLib := match env.getModuleIdxFor? n with
      | some i => (lib.toName).isPrefixOf env.header.moduleNames[i.toNat]!
      | none => false
    unless inLib do
      IO.println s!"EXT NAME OUTSIDE {lib}: {n}"; bad := true
    for a in ← axiomsOf env n do
      unless allowed.contains a do
        IO.println s!"BAD AXIOM: {n} uses {a}"; bad := true
  IO.println s!"checked {names.size} ext names ({lib})"
  return if bad then 1 else 0
