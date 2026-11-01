import AvailableChainFGSARun
import AvailableChainCheckSupport.GeneratedOwner
import Lean
import AvailableChainCheckSupport.ImportPolicy
open Lean AvailableChainCheckSupport

/-! FGSA run-library axiom and import check (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` §3.1, T7.1). Adapted from
`scripts/CheckFGSAAxioms.lean`.

Every compiled constant of the modules of `AvailableChainFGSARun` may depend
only on `propext`, `Classical.choice` and `Quot.sound`. This rejects
`sorryAx`, the auxiliary `_native` axiom of `native_decide` or `decide +native`
and project axioms.

It checks BUILT data: `lean --run` imports the `.olean` files and does not
compare them with the sources. Run `lake build AvailableChainFGSARun` first, or
use `bash scripts/check-fgsa-run.sh`, which builds and then runs every check.

It also checks four facts on the COMPILED data:
- build coverage: every `.lean` file (extension in any case) under the source
  directory (default `AvailableChainFGSARun`; symbolic links are followed) is
  a module of the import closure;
- direct imports: the direct imports of every `AvailableChainFGSARun` module,
  as the `.olean` files record them, obey the allowlist and the layer rules of
  `scripts/check-fgsa-run.sh` (`allowedImport`). This check does not depend on
  the header syntax, the file name or the directory layout;
- closure: no module of `AvailableChainFramework`, `AvailableChainRegistry`,
  `AvailableChainSAPC`, `AvailableChainLStar` or `AvailableChainWitnesses` is
  in the import closure. The v1 Kit, `AvailableChainStatements`, the Grid CO
  proofs and the v1 engine are in the closure (the store models import the v1
  engine, and `AvailableChainFGSA.Proofs.StoreInv` reaches the others), so
  the closure test cannot forbid them;
- used constants (plan §3.1): no constant of an `AvailableChainFGSARun`
  module refers directly (in its type or its value, proofs included) to a
  constant of a module of `AvailableChainKit`, `AvailableChainStatements` or
  `AvailableChainGridCO.Proofs`, or of the module
  `AvailableChainModel.Generic.Run`. Store theorems of
  `AvailableChainFGSA.Proofs` may use such constants in their own proofs.
  A generated constant (an equation, a splitter, a congruence equation, a
  sparse `casesOn` or its fallback equation, also with a private name) is
  judged by its owner definition (`generatedOwner`, in
  `scripts/AvailableChainCheckSupport/GeneratedOwner.lean`), not by the module that
  realized it: the owner must be a definition in a module that is not
  forbidden. Skipped as a checked constant: a generated constant of a
  definition of another library. Lean realizes it in the module that unfolds
  the definition, and it states the body of that definition, which is not a
  T7 declaration. The rule has no list of names.

Run: `lake env lean --run scripts/CheckFGSARunAxioms.lean [--root M …]
[--files D] [--expect N …]`, with the options in this order.
`--root M` imports one more root module (negative controls); `--files D` sets
the source directory (its last component must be `AvailableChainFGSARun`).
With `--expect`, each named constant must be a checked constant (a short name
matches a qualified one by suffix).
Exit codes: 0 clean; 1 a bad axiom, a source file outside the build, a direct
import outside the allowlist, a forbidden library in the closure, or a
forbidden used constant; 2 nothing found, a usage error (an unknown argument,
or `--expect` without a name), or an expected name missing. Each missing
expected name forces exit 2, also after other failures. -/

def lib : Name := `AvailableChainFGSARun

def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def forbiddenRoots : List Name :=
  [`AvailableChainFramework, `AvailableChainRegistry, `AvailableChainSAPC,
    `AvailableChainLStar, `AvailableChainWitnesses]

/-- The modules whose constants no run-library constant may use directly. -/
def forbiddenConstModule (m : Name) : Bool :=
  (`AvailableChainKit).isPrefixOf m || (`AvailableChainStatements).isPrefixOf m ||
    (`AvailableChainGridCO.Proofs).isPrefixOf m || m == `AvailableChainModel.Generic.Run

/-- A strict submodule of the library `r` (not its root). -/
def under (r m : Name) : Bool := r.isPrefixOf m && m != r

/-- The same generated policy as the source checks. -/
def allowedImport (mod imp : Name) : Bool :=
  AvailableChainCheckSupport.ImportPolicy.runAllowedImport mod imp

/-- The module names of the `.lean` files under `dir`, whose last component is
`AvailableChainFGSARun`. -/
def sourceModules (dir : System.FilePath) : IO (Array Name) := do
  let files ← dir.walkDir
  let mut out := #[]
  for f in files do
    if f.extension.map String.toLower == some "lean" then
      let parts := (f.withExtension "").components.drop dir.components.length
      out := out.push (parts.foldl (fun n s => Name.str n s) lib)
  return out

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def inLib (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => lib.isPrefixOf m
  | none => false

/-- A generated constant (`generatedOwner`) of a definition of another
library. Lean realizes it in the module that unfolds the definition, and it
states the body of that definition, which is not a T7 declaration. -/
def generatedEqn (env : Environment) (n : Name) : Bool :=
  (generatedOfOther env (inLib env) n).isSome

/-- The used constant `u` is forbidden. A generated constant is judged by its
owner: the owner must be a definition in a module that is not forbidden (the
module that realized `u` does not count). Every other constant is judged by
its own module. The reason is printed. -/
def forbiddenUse (env : Environment) (u : Name) : Option String :=
  match generatedOwner env u with
  | some o =>
      let mo := moduleOf env o
      if !ownerIsDefn env o then some s!"owner {o} is not a definition"
      else if mo.any forbiddenConstModule then some s!"owner {o} ({mo.getD .anonymous})"
      else none
  | none =>
      match moduleOf env u with
      | some m => if forbiddenConstModule m then some s!"{m}" else none
      | none => none

/-- The axioms `n` transitively depends on (the pattern of
`scripts/CheckFGSAAxioms.lean`). -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n)
    { fileName := "CheckFGSARunAxioms", fileMap := .ofString "" } { env := env }

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
  let usage := "USAGE: lake env lean --run scripts/CheckFGSARunAxioms.lean \
    [--root M …] [--files D] [--expect N …]"
  let mut rest := args
  let mut extra : Array Name := #[]
  let mut dir : System.FilePath := ""
  unless args.contains "--files" do
    dir := (← layoutOutput #["dir", "AvailableChainFGSARun"])[0]!
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
  let env ← importModules ((#[lib] ++ extra).map ({ module := · })) {}
  let mods := env.header.moduleNames
  let mut badImports := false
  for m in ← sourceModules dir do
    unless mods.contains m do
      IO.println s!"NOT IN THE BUILD: {m} (the root does not import it)"
      badImports := true
  let mut libMods := 0
  for h : i in [0:mods.size] do
    let m := mods[i]
    unless lib.isPrefixOf m do continue
    libMods := libMods + 1
    for imp in env.header.moduleData[i]!.imports do
      unless allowedImport m imp.module do
        IO.println s!"COMPILED IMPORT NOT ALLOWED: {m} imports {imp.module}"
        badImports := true
  for m in mods do
    if forbiddenRoots.any (·.isPrefixOf m) then
      IO.println s!"FORBIDDEN LIBRARY IN THE IMPORT CLOSURE: {m}"
      badImports := true
  let cs := env.constants.toList.filter (fun (n, _) => inLib env n)
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
  -- Used constants: the type and the value (proofs included) of every
  -- library constant, except generated equation lemmas of other libraries.
  let mut badUses := false
  let mut skipped := 0
  for (n, ci) in cs do
    if generatedEqn env n then
      skipped := skipped + 1
      continue
    let mut used := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
    for u in used.toList.eraseDups do
      if let some why := forbiddenUse env u then
        IO.println s!"FORBIDDEN CONSTANT: {n} uses {u} ({why})"
        badUses := true
  -- Count the missing names; no later name can clear an earlier miss.
  let mut missing := 0
  for s in expected do
    unless cs.any (fun (n, _) => s.toName.isSuffixOf n) do
      IO.println s!"NOT CHECKED: {s}"
      missing := missing + 1
  IO.println s!"checked {cs.length} constants, {thms.length} theorems, {mods.size} modules \
    in the import closure, direct imports of {libMods} library modules, used constants of \
    {cs.length - skipped} constants ({skipped} generated equation lemmas skipped)"
  if missing > 0 then
    IO.println s!"{missing} expected names not checked"
    return 2
  return if badAxioms || badImports || badUses then 1 else 0
