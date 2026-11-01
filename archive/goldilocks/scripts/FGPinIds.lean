import AvailableChainKitFG.Pins
import Lean
open Lean AvailableChain.KitFG  -- the namespace of Pins.lean

/-! Prints the manifest of `Pins.lean` from the elaborated values (`manifest`),
with `--check-names` checks the pinned names (`checkNames`), or with `--ext`
prints the `leanIn` names as records `ext <lib> <name>` and a trailer
`END ext <n>` (`scripts/check-fgsa.sh` checks them with
`scripts/CheckFGSAExt.lean`). In every mode it first checks that each `leanIn`
library is on `extLibs`; else it prints `UNKNOWN EXT LIBRARY` on stderr and
exits 2 (so the manifest step of `scripts/check-fg-pins.sh` fails in the FG
environment). It reads BUILT data: `lean --run` imports the `.olean` files and
does not compare them with the sources. Run it after `lake build
AvailableChainSimplexFG AvailableChainKitFG`: `lake env lean --run
scripts/FGPinIds.lean [--check-names | --ext]`, or use `bash scripts/check-fg.sh`,
which builds and then runs every FG check. `scripts/check-fg-pins.sh` builds,
then runs it without an argument. -/

/-- The table that this script reads. The negative controls of
`scripts/check-fgsa.sh` replace this line in a copy. -/
def table : List Pin := pins

/-- The libraries that a `leanIn` clause can name (a literal allowlist). Each one
needs a checker in its own environment: `AvailableChainFGSA` is checked by
`scripts/CheckFGSAExt.lean`, run by `scripts/check-fgsa.sh`. -/
def extLibs : List String := ["AvailableChainFGSA"]

/-- Every `leanIn` library is on `extLibs`. Exit 0 when all are; 2 otherwise. -/
def checkExtLibs (ps : List Pin) : IO UInt32 := do
  let bad := (extNames ps).filter fun (_, lib, _) => !extLibs.contains lib
  for (p, lib, n) in bad do IO.eprintln s!"UNKNOWN EXT LIBRARY: {lib} (pin {p}, name {n})"
  return if bad.isEmpty then 0 else 2

/-- Every pinned name is a constant of a module of `AvailableChainSimplexFG` or
`AvailableChainKitFG`, so `CheckFGAxioms.lean` checks its axioms (Astra T02).
Exit 0 when all are; 2 otherwise. -/
def checkNames (ns : List Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := `AvailableChainSimplexFG }, { module := `AvailableChainKitFG }] {}
  let inFG (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i =>
      let m := env.header.moduleNames[i.toNat]!
      (`AvailableChainSimplexFG).isPrefixOf m || (`AvailableChainKitFG).isPrefixOf m
    | none => false
  if ns.isEmpty then
    IO.println "NO PIN NAMES"
    return 2
  let bad := ns.filter (!inFG ·)
  for n in bad do IO.println s!"NOT AN FG CONSTANT: {n}"
  IO.println s!"checked {ns.length} pinned names"
  return if bad.isEmpty then 0 else 2

def main (args : List String) : IO UInt32 := do
  let rc ← checkExtLibs table
  if rc != 0 then return rc
  if args == ["--check-names"] then
    checkNames (pinNames table defPins helpers)
  else if args == ["--ext"] then
    let recs := ((extNames table).map fun (_, lib, n) => (lib, n)).eraseDups
    for (lib, n) in recs do IO.println s!"ext {lib} {n}"
    IO.println s!"END ext {recs.length}"
    return 0
  else
    for l in manifest table defPins notFormalized historicalPins do IO.println l
    return 0
