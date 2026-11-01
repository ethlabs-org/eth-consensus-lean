import AvailableChainFGSA
import Lean.Util.CollectAxioms
import AvailableChainCheckSupport.ImportPolicy
open Lean

/-! FGSA axiom check. Every compiled constant of the modules of
`AvailableChainFGSA` may depend only on
`propext`, `Classical.choice` and `Quot.sound`. This rejects `sorryAx`, the
auxiliary `_native` axiom of `native_decide` or `decide +native` (for example
`t._native.native_decide.ax_1_1` on v4.30.0-rc2; older toolchains:
`Lean.ofReduceBool`) and project axioms.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainFGSA` first, or
use `bash scripts/check-fgsa.sh`, which builds and then runs every FGSA check.

It also checks three import facts on the COMPILED import graph (G13 Astra M2,
Opus m1; G13 fold MINOR-2):
- build coverage: every `.lean` file (extension in any case) under the source
  directory (default `AvailableChainFGSA`; symbolic links are followed) is a
  module of the import closure, so a file that the root does not import (for
  example behind a commented-out import) cannot escape the build and this
  axiom check;
- direct imports: the direct imports of every `AvailableChainFGSA` module in
  the closure, as the `.olean` files record them, obey the allowlist and the
  layer rules of `scripts/check-fgsa.sh` (`allowedImport`). This check does
  not depend on the header syntax, the file name or the directory layout;
- closure: no module of `AvailableChainFramework`, `AvailableChainRegistry`,
  `AvailableChainSAPC` or `AvailableChainWitnesses` is in the import closure.
  `AvailableChainStatements` is allowed there (the declared transitive
  dependency through `AvailableChainGridCO.Proofs.Basic`), and so is
  `AvailableChainKit` (Engine): after plan 1b's Kit split (main c79b473), the
  Grid CO proofs import `AvailableChainKit.Engine.{EngineClock, Execution}`,
  which hold the engine-generic lemmas (namespace `AvailableChain.Engine`).

Run: `lake env lean --run scripts/CheckFGSAAxioms.lean [--root M …] [--files D]
[--expect N …]`, with the options in this order. `--root M` imports one more
root module (negative controls); `--files D` sets the source directory (its
last component must be `AvailableChainFGSA`). With `--expect`, each named
constant must be a checked constant (a short name matches a qualified one by
suffix).
Exit codes: 0 clean; 1 a bad axiom, a source file outside the build, a direct
import outside the allowlist, or a forbidden library in the closure; 2 nothing found, a usage error (an unknown
argument, or `--expect` without a name), or an expected name missing. Each
missing expected name forces exit 2, also after a bad axiom or after other
expected names that are present. -/

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def forbiddenRoots : List Name :=
  [`AvailableChainFramework, `AvailableChainRegistry, `AvailableChainSAPC,
    `AvailableChainWitnesses]

/-- The same generated policy as the source checks. -/
def allowedImport (mod imp : Name) : Bool :=
  AvailableChainCheckSupport.ImportPolicy.fgsaAllowedImport mod imp

/-- The module names of the `.lean` files under `dir`, whose last component is
`AvailableChainFGSA`. -/
def sourceModules (dir : System.FilePath) : IO (Array Name) := do
  let files ← dir.walkDir
  let mut out := #[]
  for f in files do
    if f.extension.map String.toLower == some "lean" then
      let parts := (f.withExtension "").components.drop dir.components.length
      out := out.push (parts.foldl (fun n s => Name.str n s) `AvailableChainFGSA)
  return out

def inFGSA (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
      let m := env.header.moduleNames[idx.toNat]!
      (`AvailableChainFGSA).isPrefixOf m
  | none => false

/-- The axioms `n` transitively depends on. Uses the `Core.CoreM.toIO'`
pattern of `scripts/Registry.lean`: the toolchain's `CollectAxioms` API is
called through `Lean.Util.CollectAxioms`'s `collectAxioms` in `CoreM`. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFGSAAxioms", fileMap := .ofString "" } { env := env }

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

def main (args : List String) : IO UInt32 := do
  let usage := "USAGE: lake env lean --run scripts/CheckFGSAAxioms.lean \
    [--root M …] [--files D] [--expect N …]"
  let mut rest := args
  let mut extra : Array Name := #[]
  let mut dir : System.FilePath := ""
  unless args.contains "--files" do
    dir := (← layoutOutput #["dir", "AvailableChainFGSA"])[0]!
  while rest.head? == some "--root" do
    match rest with
    | _ :: m :: r => extra := extra.push m.toName; rest := r
    | _ => IO.eprintln usage; return 2
  if rest.head? == some "--files" then
    match rest with
    | _ :: d :: r => dir := d; rest := r
    | _ => IO.eprintln usage; return 2
  -- Reject an unknown argument: a typo must not skip the `--expect` test.
  unless rest.isEmpty || (rest.head? == some "--expect" && rest.length ≥ 2) do
    IO.eprintln usage
    return 2
  let expected := rest.drop 1
  initSearchPath (← findSysroot)
  let env ← importModules
    ((#[`AvailableChainFGSA] ++ extra).map ({ module := · })) {}
  let mods := env.header.moduleNames
  let mut badImports := false
  for m in ← sourceModules dir do
    unless mods.contains m do
      IO.println s!"NOT IN THE BUILD: {m} (the root does not import it)"
      badImports := true
  let mut fgsaMods := 0
  for h : i in [0:mods.size] do
    let m := mods[i]
    unless (`AvailableChainFGSA).isPrefixOf m do continue
    fgsaMods := fgsaMods + 1
    for imp in env.header.moduleData[i]!.imports do
      unless allowedImport m imp.module do
        IO.println s!"COMPILED IMPORT NOT ALLOWED: {m} imports {imp.module}"
        badImports := true
  for m in mods do
    if forbiddenRoots.any (·.isPrefixOf m) then
      IO.println s!"FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: {m}"
      badImports := true
  let cs := env.constants.toList.filter (fun (n, _) => inFGSA env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let thms := cs.filterMap fun (n, ci) => if ci matches .thmInfo _ then some n else none
  let mut badAxioms := false
  for (n, _) in cs do
    let axs ← axiomsOf env n
    let bad := axs.filter (fun a => !allowed.contains a)
    unless bad.isEmpty do
      IO.println s!"BAD AXIOMS {n}: {bad}"
      badAxioms := true
  -- Count the missing names; no later name can clear an earlier miss.
  let mut missing := 0
  for s in expected do
    unless cs.any (fun (n, _) => s.toName.isSuffixOf n) do
      IO.println s!"NOT CHECKED: {s}"
      missing := missing + 1
  IO.println s!"checked {cs.length} constants, {thms.length} theorems, {mods.size} modules \
    in the import closure, direct imports of {fgsaMods} FGSA modules"
  if missing > 0 then
    IO.println s!"{missing} expected names not checked"
    return 2
  return if badAxioms || badImports then 1 else 0
