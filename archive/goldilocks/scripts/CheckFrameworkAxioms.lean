import AvailableChainFramework
import AvailableChainRegistry
import AvailableChainKit
import AvailableChainEngineV2
import AvailableChainKitV2
import Lean.Util.CollectAxioms
open Lean

/-! Framework axiom check. It imports the library roots
`AvailableChainFramework`, `AvailableChainRegistry`, `AvailableChainKit`,
`AvailableChainEngineV2` and `AvailableChainKitV2`, and every module under
`AvailableChainEngineV2/Tests/` and `AvailableChainKitV2/Tests/` (found at run
time; the roots do not import them). Every non-internal constant of an imported module of these five
libraries may depend only on `propext`, `Classical.choice` and `Quot.sound`
(`collectAxioms`, proofs included). Modules of these libraries that no root
and no test module imports are not checked; `example`s are not constants and
are not checked. This rejects `sorryAx`, the auxiliary axioms of
`native_decide` and project axioms. It is modelled on
`scripts/CheckFGAxioms.lean`.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainFramework
AvailableChainRegistry AvailableChainKit AvailableChainEngineV2 AvailableChainKitV2`
first.

Run from the repository root: `lake env lean --run scripts/CheckFrameworkAxioms.lean`.
Exit codes: 0 clean; 1 a bad axiom; 2 nothing found or a usage error. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The libraries whose modules are checked. -/
def libraries : List Name :=
  [`AvailableChainFramework, `AvailableChainRegistry, `AvailableChainKit, `AvailableChainEngineV2,
    `AvailableChainKitV2]

def inLibraries (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      libraries.any (·.isPrefixOf m)
  | none => false

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

/-- The directories of the engine v2 and Kit v2 test modules, relative to the
repository root. -/
def testsDirs : IO (Array String) :=
  layoutOutput #["dir", "AvailableChainEngineV2.Tests", "AvailableChainKitV2.Tests"]

/-- Enumerate test identities independently of facade imports. -/
def testModules : IO (Array Name) := do
  return (← layoutOutput #["modules", "AvailableChainEngineV2.Tests",
    "AvailableChainKitV2.Tests"]).map String.toName

/-- The axioms `n` transitively depends on. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFrameworkAxioms", fileMap := .ofString "" } { env := env }

def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "USAGE: lake env lean --run scripts/CheckFrameworkAxioms.lean"
    return 2
  for dir in ← testsDirs do
    unless ← (System.FilePath.mk dir).isDir do
      IO.eprintln s!"NO DIRECTORY {dir}: run from the repository root"
      return 2
  let tests ← testModules
  initSearchPath (← findSysroot)
  let modules := libraries.toArray ++ tests
  let env ← importModules (modules.map ({ module := · })) {}
  let cs := env.constants.toList.filter (fun (n, _) => !n.isInternal && inLibraries env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let mut badAxioms := false
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
  IO.println s!"checked {cs.length} constants (test modules: {tests})"
  return if badAxioms then 1 else 0
