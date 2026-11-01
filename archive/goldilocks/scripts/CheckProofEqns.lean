import Lean
import Lake.Toml.Load
import AvailableChainCheckSupport.GeneratedOwner

open Lean AvailableChainCheckSupport
open Lean.Meta

/-! Check (d), BUILD §7.2 B3a and §7.3: equation-like exports of proof modules.
Source: `claude-files/a0/check-sketches/CheckProofEqns.lean`.

Run from the repository root after the default targets have been built:
  lake build AvailableChainCheckSupport
  lake env lean --run scripts/CheckProofEqns.lean --baseline scripts/baselines/check-proof-eqns.txt
  lake env lean --run scripts/CheckProofEqns.lean --write-baseline

Roots come from `defaultTargets` in lakefile.toml. Extra command-line modules
are additional roots. Proof and Statements source modules are also imported,
so they need not appear in their library facade to be checked. Missing compiled
modules are errors; this script does not build or use the network.

Only `.exported` module data is scanned. Each module's own constant list is
checked, because the combined constant map keeps only the first module index
for a name that more than one module exports. Private matcher copies are
included. The baseline key is `<exporting module> <generated constant>`;
diagnostics also give the owner from the shared GeneratedOwner API. An owner
in another library does not exempt an export in a proof module.
If an owner's declaration is private, its module's private data is loaded
only for the owner lookup. That data never supplies the list of findings.

Kit and FGSAProofs submodules are proof modules except facades, Tests,
KitV2.ClockLaws, and the KitFG definition list used by checks (b) and (e).
Gen findings cannot be accepted by a baseline. Baseline generation writes
only non-Gen findings and returns 1 if there are Gen findings. The initial
baseline records the existing exports at 03bd912, including FGSARun.
Exit codes: 0 accepted; 1 unaccepted exports; 2 usage or input error.

The default run also checks non-exposed public Statements predicates. Each
needs a public `<name>_def` theorem in its owning module, with the defining
equality or iff. Exposed predicates do not need this backstop.
`--coverage FILE` checks required audit lines from a caller-supplied inventory:
`<owning module> <declaration> <audit module>`, one row per line. The audit must
be imported by the roots. Only active, fully qualified `#print axioms` commands
in that module count. The gate/source inventory is a separate check.
`--complete-coverage` also checks all audit commands, including namespace-local
names and declarations imported from other libraries. It requires an inventory
entry for each command. `--write-coverage FILE` generates that inventory for the
explicit audit roots. Generation is a separate action; normal checks never write it.
`--controls` tests the added checks in the same run.
-/

def baselinePath : System.FilePath := "scripts/baselines/check-proof-eqns.txt"

def eqLike (s : String) : Bool :=
  s == "eq_def" || s == "splitter" || s == "eq_unfold" || s == "induct" ||
  s == "fun_cases" ||
    (s.startsWith "eq_" && !(s.drop 3).isEmpty && (s.drop 3).all Char.isDigit)

def dataLines (path : System.FilePath) : IO (List String) := do
  return (← IO.FS.lines path).toList.filterMap fun line =>
    let line := (line.splitOn "#").head!.trimAscii.toString
    if line.isEmpty then none else some line

def kitFGDefinitions : IO (Std.HashSet Name) := do
  let names ← dataLines "scripts/baselines/kitfg-def-modules.txt"
  return Std.HashSet.ofList <| names.map fun s =>
    (if s.startsWith "AvailableChainKitFG." then s else "AvailableChainKitFG." ++ s).toName

def isProofModule (definitions : Std.HashSet Name) (m : Name) : Bool :=
  let parts := m.components
  parts.contains `Proofs ||
    (!parts.contains `Tests && !definitions.contains m && m != `AvailableChainKitV2.ClockLaws &&
      parts.length > 1 &&
        [`AvailableChainKit, `AvailableChainKitV2, `AvailableChainKitFG,
          `AvailableChainFGSAProofs, `AvailableChainPCSAProofs].contains parts.head!)

def tomlString (v : Lake.Toml.Value) : IO String :=
  match v with
  | .string _ s => pure s
  | _ => throw <| IO.userError "lakefile.toml: expected a string"

def defaultRoots (definitions : Std.HashSet Name) : IO (Array Name) := do
  let path := "lakefile.toml"
  let input ← IO.FS.readFile path
  let table ← (Lake.Toml.loadToml (Parser.mkInputContext input path)).toIO fun errors =>
    IO.userError s!"cannot parse lakefile.toml: {errors.toList.length} errors"
  let some (.array _ targets) := table.find? `defaultTargets |
    throw <| IO.userError "lakefile.toml: defaultTargets must be an array"
  if targets.isEmpty then throw <| IO.userError "lakefile.toml: no default targets"
  let some (.array _ libraries) := table.find? `lean_lib |
    throw <| IO.userError "lakefile.toml: no lean_lib tables"
  let mut roots := #[]
  for target in targets do
    let name ← tomlString target
    roots := roots.push name.toName
    let mut found := false
    for library in libraries do
      let .table _ library := library | continue
      let some n := library.find? `name | continue
      unless (← tomlString n) == name do continue
      found := true
      let srcDir ← match library.find? `srcDir with
        | some v => System.FilePath.mk <$> tomlString v
        | none => pure "."
      let dir := srcDir / name
      unless ← dir.isDir do continue
      for file in ← dir.walkDir do
        unless file.extension == some "lean" do continue
        let parts := (file.withExtension "").components.drop srcDir.components.length
        let m := parts.foldl Name.str .anonymous
        if isProofModule definitions m || m.components.contains `Statements then
          roots := roots.push m
    unless found do throw <| IO.userError s!"default target is not a lean_lib: {name}"
  return (Std.HashSet.ofList roots.toList).toArray.qsort Name.lt

/-- The shared API covers equations and splitters. The other three checked
suffixes are not in generatedSuffix; their declared prefix is the owner. -/
def equationOwner (env : Environment) (n : Name) : Option Name :=
  generatedOwner env n <|> match n with
    | .str pre s =>
      if s == "eq_unfold" || s == "induct" || s == "fun_cases" then declaredName env pre
      else none
    | _ => none

structure Finding where
  mod : Name
  constant : Name
  owner : Option Name

def Finding.key (finding : Finding) : String := s!"{finding.mod} {finding.constant}"

def findings (env : Environment) (definitions : Std.HashSet Name) : Array Finding := Id.run do
  let mut out := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless isProofModule definitions m do continue
    for n in env.header.moduleData[i]!.constNames do
      let .str _ s := n | continue
      unless eqLike s do continue
      out := out.push { mod := m, constant := n, owner := equationOwner env n }
  return out.qsort fun a b => a.key < b.key

/-- Some exported equations refer to private definitions or tactic matchers
whose declarations are not exported. Add their compiled declarations to a
lookup environment, so GeneratedOwner can resolve them without importing
the private data of the full dependency tree. Keep the exported scan intact. -/
def resolveOwners (env : Environment) (rows : Array Finding) : IO (Array Finding) := do
  let missing := rows.filter (·.owner.isNone)
  if missing.isEmpty then return rows
  let modules := Std.HashSet.ofList (missing.toList.map (·.mod))
  let prefixes := Std.HashSet.ofList (missing.toList.map (·.constant.getPrefix))
  let mut lookup := env
  for m in modules.toArray do
    let path ← findOLean m
    let parts ← readModuleDataParts
      #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path]
    for (data, _) in parts do
      for info in data.constants do
        unless prefixes.contains info.name && !lookup.contains info.name do continue
        let addition ← lookup.addConstAsync info.name (.ofConstantInfo info) (reportExts := false)
        addition.commitConst lookup (some info) (some info)
        addition.commitCheckEnv lookup
        lookup := addition.mainEnv
  return rows.map fun row =>
    { row with owner := row.owner <|> equationOwner lookup row.constant }

structure CheckOptions where
  roots : Array Name := #[]
  baseline : Option System.FilePath := none
  write : Bool := false
  coverage : Option System.FilePath := none
  completeCoverage : Bool := false
  writeCoverage : Option System.FilePath := none
  controls : Bool := false
  rootsOnly : Bool := false

def parseArgs : List String → CheckOptions → Except String CheckOptions
  | [], options =>
    if options.write && options.baseline.isSome then
      .error "--write-baseline and --baseline cannot be used together"
    else if options.completeCoverage && options.coverage.isNone then
      .error "--complete-coverage requires --coverage"
    else if options.writeCoverage.isSome && options.coverage.isSome then
      .error "--write-coverage and --coverage cannot be used together"
    else .ok options
  | "--baseline" :: path :: rest, options =>
    if path.startsWith "--" || options.baseline.isSome then .error "invalid --baseline"
    else parseArgs rest { options with baseline := some path }
  | "--write-baseline" :: rest, options => parseArgs rest { options with write := true }
  | "--coverage" :: path :: rest, options =>
    if path.startsWith "--" || options.coverage.isSome then .error "invalid --coverage"
    else parseArgs rest { options with coverage := some path }
  | "--roots-only" :: rest, options => parseArgs rest { options with rootsOnly := true }
  | "--controls" :: rest, options => parseArgs rest { options with controls := true }
  | "--complete-coverage" :: rest, options =>
    parseArgs rest { options with completeCoverage := true }
  | "--write-coverage" :: path :: rest, options =>
    if path.startsWith "--" || options.writeCoverage.isSome then .error "invalid --write-coverage"
    else parseArgs rest { options with writeCoverage := some path }
  | arg :: rest, options =>
    if arg.startsWith "-" then .error s!"unknown or incomplete option: {arg}"
    else parseArgs rest { options with roots := options.roots.push arg.toName }

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)

/-- Compare the theorem with the definition's actual body, after its binders. -/
def definingEquation (d : DefinitionVal) (t : Expr) : MetaM Bool := do
  let tail := t.getForallBody.consumeMData
  let args := tail.getAppArgs
  let lhs? := if tail.getAppFn.isConstOf ``Eq && args.size == 3 then some args[1]!
    else if tail.getAppFn.isConstOf ``Iff && args.size == 2 then some args[0]! else none
  unless lhs?.any (·.getAppFn.isConstOf d.name) do return false
  forallTelescope d.type fun xs _ => do
    let lhs := mkAppN (mkConst d.name (d.levelParams.map Level.param)) xs
    let rhs := d.value.beta xs
    let relation ← if tail.getAppFn.isConstOf ``Iff then mkAppM ``Iff #[lhs, rhs]
      else mkEq lhs rhs
    let expected ← mkForallFVars xs relation
    -- Keep the predicate opaque here. Otherwise `P = P` can pass after
    -- unfolding P, although it gives an importing module no defining equation.
    withCanUnfoldPred (fun cfg ci => do
      if ci.name == d.name then return false
      canUnfoldDefault cfg ci) <| isDefEq t expected

def homeEquation (env : Environment) (m : Name) (d : DefinitionVal) : MetaM (Option String) := do
  let n := d.name.appendAfter "_def"
  unless env.contains n do
    return some s!"STATEMENT DEF MISSING name={d.name} module={m}"
  unless moduleOf env n == some m do
    return some s!"STATEMENT DEF WRONG MODULE name={n} expected={m}"
  -- Exported theorems can have only an axiom-shaped signature. Their private
  -- module data supplies the declaration kind; the public map supplies visibility.
  let some (.thmInfo thm) := (← getEnv).find? n |
    return some s!"STATEMENT DEF NOT THEOREM name={n} module={m}"
  let ty := thm.type.instantiateLevelParams thm.levelParams (d.levelParams.map Level.param)
  unless thm.levelParams.length == d.levelParams.length && (← definingEquation d ty) do
    return some s!"STATEMENT DEF WRONG TYPE name={n} module={m}"
  return none

def runMeta (env : Environment) (x : MetaM α) : IO α :=
  x.run' {} |>.toIO' { fileName := "CheckProofEqns", fileMap := .ofString "" } { env }

/-- Read private definition values only for public, non-exposed Statements names.
The exported environment still decides visibility and equation ownership. -/
def statementCoverage (env : Environment) : IO (Array String) := do
  let mut out := #[]
  let mut checked := 0
  let mut hidden : Array (Name × DefinitionVal) := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless m.components.contains `Statements &&
        m.components.head!.toString.startsWith "AvailableChain" do continue
    let candidates := env.header.moduleData[i]!.constNames.filter fun n =>
      !isPrivateName n && !n.isInternal && moduleOf env n == some m && !env.hasExposedBody n
    if candidates.isEmpty then continue
    let path ← findOLean m
    let parts ← readModuleDataParts
      #[path, OLeanLevel.server.adjustFileName path, OLeanLevel.private.adjustFileName path]
    let mut seen : Std.HashSet Name := {}
    for (data, _) in parts do
      for ci in data.constants do
        let .defnInfo d := ci | continue
        unless candidates.contains d.name && !seen.contains d.name do continue
        seen := seen.insert d.name
        hidden := hidden.push (m, d)
  if !hidden.isEmpty then
    -- Private data also resolves hidden aliases for Prop. It never decides
    -- whether the predicate or its equation is public.
    let modules := Std.HashSet.ofList (hidden.toList.map (·.1))
    let lookup ← importModules (modules.toArray.map fun m => { module := m }) {}
      (level := .private)
    for (m, d) in hidden do
      let prop ← runMeta lookup <| forallTelescopeReducing d.type fun _ t => do
        return (← whnf t).isProp
      unless prop do continue
      checked := checked + 1
      if let some error ← runMeta lookup (homeEquation env m d) then out := out.push error
  IO.println s!"CheckProofEqns: {checked} non-exposed Statements predicates"
  return out

/-- Use the Lean parser so comments, strings and short names cannot supply a line. -/
def auditNames (env : Environment) (text : String) (complete := false) :
    IO (Std.HashSet Name) := do
  let input := Parser.mkInputContext text "audit coverage"
  let (_, initial, messages) ← Parser.parseHeader input
  let mut state := initial
  let mut messages := messages
  let mut out : Std.HashSet Name := {}
  let mut scopes : List Name := []
  let mut ns := Name.anonymous
  repeat
    let (command, next, log) := Parser.parseCommand input { env, options := {} } state messages
    state := next
    messages := log
    if complete then
      if command.getKind == ``Parser.Command.namespace then
        scopes := ns :: scopes
        ns := ns ++ command[1].getId
      else if command.getKind == ``Parser.Command.section then
        scopes := ns :: scopes
      else if command.getKind == ``Parser.Command.end then
        ns := scopes.headD .anonymous
        scopes := scopes.drop 1
    if command.getKind == ``Parser.Command.printAxioms then
      let name := command[2].getId
      let name := if complete && env.contains (ns ++ name) then ns ++ name else name
      out := out.insert name
    if Parser.isTerminalCommand command then break
  if messages.hasErrors then
    for message in messages.toList do IO.eprintln (← message.toString)
    throw <| IO.userError "COVERAGE PARSE UNSUPPORTED"
  return out

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

def auditFiles (audits : Array Name) : IO (Std.HashMap Name System.FilePath) := do
  if audits.isEmpty then return {}
  let paths ← layoutOutput (#["path"] ++ audits.map Name.toString)
  unless paths.size == audits.size do throw <| IO.userError "audit source count mismatch"
  let mut out := {}
  for i in [:audits.size] do out := out.insert audits[i]! (System.FilePath.mk paths[i]!)
  return out

def writeAuditCoverage (env : Environment) (audits : Array Name) (path : System.FilePath) :
    IO Unit := do
  let files ← auditFiles audits
  let mut rows := #[]
  for audit in audits do
    let names ← auditNames env (← IO.FS.readFile files[audit]!) true
    for name in names.toArray.qsort Name.lt do
      let some owner := moduleOf env name |
        throw <| IO.userError s!"AUDIT OWNER MISSING name={name} audit={audit}"
      rows := rows.push s!"{owner} {name} {audit}\n"
  IO.FS.writeFile path (String.join rows.toList)

def auditCoverage (env : Environment) (path : System.FilePath) (complete := false) :
    IO (Array String) := do
  let lines ← dataLines path
  let audits := (lines.filterMap fun line =>
    ((line.splitOn " ").filter (!·.isEmpty))[2]?.map String.toName).toArray
  let files ← auditFiles audits
  let mut out := #[]
  let mut cache : Std.HashMap Name (Std.HashSet Name) := {}
  let mut required : Std.HashMap Name (Std.HashSet Name) := {}
  for line in lines do
    let [owner, decl, audit] := (line.splitOn " ").filter (!·.isEmpty) |
      throw <| IO.userError s!"invalid coverage row: {line}"
    let m := owner.toName
    let n := decl.toName
    let a := audit.toName
    required := required.insert a ((required[a]?.getD {}).insert n)
    unless moduleOf env n == some m && !isPrivateName n do
      out := out.push s!"AUDIT DECLARATION MISSING name={n} module={m}"
    unless (complete || m.components.head? == a.components.head?) &&
        env.header.moduleNames.contains a do
      out := out.push s!"AUDIT MODULE NOT COVERED name={n} audit={a}"
      continue
    let names ← match cache[a]? with
      | some ns => pure ns
      | none =>
          let file := files[a]!
          let ns ← try auditNames env (← IO.FS.readFile file) complete
            catch error => throw <| IO.userError s!"{file}: {error}"
          cache := cache.insert a ns
          pure ns
    unless names.contains n do out := out.push s!"AUDIT LINE MISSING name={n} audit={a}"
  if complete then
    for (audit, names) in cache.toArray do
      for name in names.toArray do
        unless (required[audit]?.getD {}).contains name do
          out := out.push s!"AUDIT INVENTORY MISSING name={name} audit={audit}"
  return out

def coverageControls (env : Environment) : IO Bool := do
  let add (env : Environment) (ci : ConstantInfo) : IO Environment := do
    let result ← env.addConstAsync ci.name (.ofConstantInfo ci) (reportExts := false)
    result.commitConst env (some ci) (some ci)
    result.commitCheckEnv env
    return result.mainEnv
  let n := `CoverageControl.predicate
  let d : DefinitionVal :=
    { name := n, levelParams := [], type := mkSort .zero
      value := mkConst ``True, hints := .opaque, safety := .safe }
  let fixture ← add env (.defnInfo d)
  let good ← runMeta fixture (mkEq (mkConst n) (mkConst ``True))
  let bad ← runMeta fixture (mkEq (mkConst n) (mkConst ``False))
  let valid ← runMeta fixture (definingEquation d good)
  let unrelated ← runMeta fixture (definingEquation d (mkConst ``True))
  let wrongBody ← runMeta fixture (definingEquation d bad)
  let missing ← runMeta fixture (homeEquation fixture `CoverageControl.Statements d)
  let thm : TheoremVal :=
    { name := n.appendAfter "_def", levelParams := []
      type := good, value := mkConst ``True.intro }
  let withThm ← add fixture (.thmInfo thm)
  let wrongModule ← runMeta withThm (homeEquation withThm `CoverageControl.Statements d)
  let printed ← auditNames env "-- #print axioms CoverageControl.hidden\n\
    /- #print axioms CoverageControl.hidden -/\n\
    def text := \"#print axioms CoverageControl.hidden\"\n\
    #print axioms CoverageControl.predicate\n#print axioms predicate\n"
  let ok := valid && !unrelated && !wrongBody && missing.isSome &&
    wrongModule.any (·.startsWith "STATEMENT DEF WRONG MODULE") && printed.contains n &&
    !printed.contains `CoverageControl.hidden && !printed.contains `Other.predicate
  IO.println s!"CONTROL home equation / audit coverage: {if ok then "PASS" else "FAIL"}"
  return ok

def runCheck (options : CheckOptions) : IO UInt32 := do
  let definitions ← kitFGDefinitions
  let roots ← if options.rootsOnly then do
      if options.roots.isEmpty then throw <| IO.userError "--roots-only needs an audit root"
      pure options.roots
    else do pure ((← defaultRoots definitions) ++ options.roots)
  let baseline := Std.HashSet.ofList (← match options.baseline with
    | some path => dataLines path
    | none => pure [])
  initSearchPath (← findSysroot)
  -- The command parser needs imported syntax extensions. Keep one exported
  -- environment; loading a second private proof environment exceeds the cap.
  let parseAudits := options.coverage.isSome || options.writeCoverage.isSome
  if parseAudits then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun m => { module := m }) {}
    (loadExts := parseAudits) (level := .exported)
  if let some path := options.writeCoverage then
    writeAuditCoverage env options.roots path
    return 0
  let rows ← resolveOwners env (findings env definitions)
  let mut bad := 0
  let mut coverageErrors ← statementCoverage env
  if let some path := options.coverage then
    coverageErrors := coverageErrors ++ (← auditCoverage env path options.completeCoverage)
  for error in coverageErrors do IO.println error
  bad := coverageErrors.size
  if options.controls then
    if !(← coverageControls env) then bad := bad + 1
  let mut legacy : Array String := #[]
  let mut counts : Std.HashMap Name Nat := {}
  for row in rows do
    let lib := row.mod.components.head!
    counts := counts.insert lib (counts[lib]?.getD 0 + 1)
    let genModule := (`AvailableChainGeneric).isPrefixOf row.mod
    if !genModule then legacy := legacy.push row.key
    if genModule || (!options.write && !baseline.contains row.key) then
      let owner := row.owner.map toString |>.getD "UNRESOLVED"
      IO.println s!"EQ EXPORT {row.key} OWNER {owner}"
      bad := bad + 1
  if options.write then
    IO.FS.writeFile baselinePath (String.join <| legacy.toList.map (· ++ "\n"))
    IO.println s!"CheckProofEqns: wrote {legacy.size} legacy entries to {baselinePath}"
  let proofModules := env.header.moduleNames.filter (isProofModule definitions)
  IO.println s!"CheckProofEqns: {proofModules.size} proof modules; \
    {rows.size} exports; {bad} unaccepted"
  for lib in counts.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    IO.println s!"CheckProofEqns: {lib.1} {lib.2}"
  let gen := rows.filter (fun row => (`AvailableChainGeneric).isPrefixOf row.mod)
  IO.println s!"CheckProofEqns: Gen {gen.size} exports"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error error => IO.eprintln s!"CheckProofEqns: {error}"; return 2
  | .ok options =>
    try runCheck options catch error =>
      IO.eprintln s!"CheckProofEqns: {error}"
      return 2
