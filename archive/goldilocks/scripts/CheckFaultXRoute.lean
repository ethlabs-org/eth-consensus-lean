import Lean
import Lake.Toml.Load

open Lean

/-! Check (i), F-24-ROUTE: each theorem with conclusion head FaultX must
reach count_rec through constants in its proof value. Exempt count_rec.

Run from the repository root on the built tree:
  lake env lean --run scripts/CheckFaultXRoute.lean [Module.Name ...] [--routes]
  lake env lean --run scripts/CheckFaultXRoute.lean --libraries

Use the roots/globs/source scan of CheckGenFirst for every AvailableChain*
lean_lib. Load private data and scan each repository module's own constants.
Include private and generated theorems. Strip forall/arrow binders and mdata
from the type, but do not unfold the conclusion. Traverse only proof/definition
values of constants owned by AvailableChain* modules; do not walk Mathlib.
Cache dependency lists, successful routes, and failed searches. A local seen
set handles cycles; cache failure only after the whole search has failed.

Extra modules are control roots. They must have an AvailableChain prefix.
--expect requires named theorems to be found (including the exempt anchor).
--routes prints one path for each accepted theorem and the exempt anchor.
Exit 0: accepted; 1: route violation; 2: input error.
-/

def tomlString (v : Lake.Toml.Value) : IO String :=
  match v with
  | .string _ s => pure s
  | _ => throw <| IO.userError "lakefile.toml: expected a string"

def tomlStrings (v? : Option Lake.Toml.Value) : IO (Option (Array String)) :=
  match v? with
  | none => pure none
  | some (.array _ vs) => some <$> vs.mapM tomlString
  | some _ => throw <| IO.userError "lakefile.toml: expected an array of strings"

def moduleDir (srcDir : System.FilePath) (m : Name) : System.FilePath :=
  m.components.foldl (fun d c => d / c.toString) srcDir

/-- A library is in scope by its name; its modules come from its `roots` (default: the
name) and the stems of its `globs`, never from the name. A Tests target such as
`AvailableChainFGSAClaimsTests` (roots `[]`, globs `AvailableChainFGSAClaims.Tests.+`)
adds module prefixes of its owner, not a prefix of its own name. -/
def scopedModules : IO (Array Name × Array Name) := do
  let path := "lakefile.toml"
  let input ← IO.FS.readFile path
  let table ← (Lake.Toml.loadToml (Parser.mkInputContext input path)).toIO fun errors =>
    IO.userError s!"cannot parse lakefile.toml: {errors.toList.length} errors"
  let some (.array _ libraries) := table.find? `lean_lib |
    throw <| IO.userError "lakefile.toml: no lean_lib tables"
  let mut libs := #[]
  let mut roots := #[]
  let unported := (← IO.FS.lines "scripts/unported-libraries.txt").filterMap fun line =>
    let name := (line.splitOn "#").head!.trimAscii.toString
    if name.isEmpty then none else some name
  for library in libraries do
    let .table _ library := library | continue
    let some n := library.find? `name | continue
    let name ← tomlString n
    unless name.startsWith "AvailableChain" do continue
    if unported.contains name then continue
    let srcDir ← match library.find? `srcDir with
      | some v => System.FilePath.mk <$> tomlString v
      | none => pure "."
    let rootNames := (← tomlStrings (library.find? `roots)).getD #[name]
    let globs := (← tomlStrings (library.find? `globs)).getD #[]
    -- Each root and each glob stem is a module prefix; scan every source file under it
    -- (also modules that the library's facade or globs do not build).
    let stems := rootNames ++ globs.map fun g =>
      if g.endsWith ".*" || g.endsWith ".+" then String.ofList (g.toList.take (g.length - 2)) else g
    -- A glob-only library (CheckSupport) can have no root source module.
    -- Import its source modules, not a nonexistent facade with the library name.
    for stem in stems do
      let p := stem.toName
      libs := libs.push p
      if ← (moduleDir srcDir p |>.addExtension "lean").pathExists then
        roots := roots.push p
      let dir := moduleDir srcDir p
      unless ← dir.isDir do continue
      for file in ← dir.walkDir do
        unless file.extension.map String.toLower == some "lean" do continue
        let parts := (file.withExtension "").components.drop srcDir.components.length
        roots := roots.push (parts.foldl Name.str .anonymous)
  if libs.isEmpty then throw <| IO.userError "lakefile.toml: no AvailableChain libraries"
  return ((Std.HashSet.ofList libs.toList).toArray.qsort Name.lt,
    (Std.HashSet.ofList roots.toList).toArray.qsort Name.lt)

def faultX : Name := `AvailableChain.Gen.Pure.FaultX
def countRec : Name := `AvailableChain.Gen.Pure.count_rec

def repositoryModule (m : Name) : Bool := m.toString.startsWith "AvailableChain"

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)

def conclusionHead : Expr → Option Name
  | .forallE _ _ body _ => conclusionHead body
  | .mdata _ body => conclusionHead body
  | .app fn _ => appHead fn
  | .const n _ => some n
  | _ => none
where
  appHead : Expr → Option Name
    | .app fn _ => appHead fn
    | .mdata _ body => appHead body
    | .const n _ => some n
    | _ => none

structure RouteCache where
  edges : Std.HashMap Name (Array Name) := {}
  routes : Std.HashMap Name (List Name) := {}
  dead : Std.HashSet Name := {}

def dependencies (env : Environment) (n : Name) : StateM RouteCache (Array Name) := do
  if let some deps := (← get).edges[n]? then return deps
  let deps := match env.find? n >>= (·.value? (allowOpaque := true)) with
    | none => #[]
    | some value => value.getUsedConstants.filter fun c =>
        (moduleOf env c).any repositoryModule
  let deps := deps.qsort Name.lt
  modify fun cache => { cache with edges := cache.edges.insert n deps }
  return deps

/-- Store each suffix of a successful path. -/
def cacheRoute : List Name → StateM RouteCache Unit
  | [] => pure ()
  | n :: rest => do
    modify fun cache => { cache with routes := cache.routes.insert n (n :: rest) }
    cacheRoute rest

def proofRoute (env : Environment) (start : Name) : StateM RouteCache (Option (List Name)) := do
  let mut pending := [(start, [])]
  let mut seen : Std.HashSet Name := {}
  repeat
    let (n, parents) :: rest := pending | break
    pending := rest
    if seen.contains n || (← get).dead.contains n then continue
    let cache ← get
    let known := if n == countRec then some [countRec] else cache.routes[n]?
    if let some tail := known then
      let path := parents.reverse ++ tail
      cacheRoute path
      return some path
    seen := seen.insert n
    for dep in ← dependencies env n do
      pending := (dep, n :: parents) :: pending
  -- Every reached node failed. No partial, cycle-dependent failure is cached.
  modify fun cache => { cache with dead := seen.fold (fun acc n => acc.insert n) cache.dead }
  return none

structure CheckOptions where
  roots : Array Name := #[]
  expected : Array Name := #[]
  routes : Bool := false

def parseArgs : List String → CheckOptions → Except String CheckOptions
  | [], options => .ok options
  | "--routes" :: rest, options => parseArgs rest { options with routes := true }
  | "--expect" :: names, options =>
    if names.isEmpty || names.any (·.startsWith "-") then
      .error "--expect needs declaration names and must be last"
    else .ok { options with expected := names.toArray.map String.toName }
  | arg :: rest, options =>
    if arg.startsWith "-" then .error s!"unknown option: {arg}"
    else if !repositoryModule arg.toName then .error s!"extra module is not in repository scope: {arg}"
    else parseArgs rest { options with roots := options.roots.push arg.toName }

def runCheck (options : CheckOptions) : IO UInt32 := do
  let (_, roots) ← scopedModules
  initSearchPath (← findSysroot)
  let env ← importModules ((roots ++ options.roots).map fun m => { module := m }) {}
    (level := .private)
  unless env.contains faultX && env.contains countRec do
    throw <| IO.userError "FaultX or count_rec anchor is missing"
  let mut candidates : Std.HashMap Name Name := {}
  let mut modules := 0
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless repositoryModule m do continue
    modules := modules + 1
    for n in env.header.moduleData[i]!.constNames do
      let some ci := env.find? n |
        throw <| IO.userError s!"compiled constant not found: {m} {n}"
      let .thmInfo _ := ci | continue
      unless conclusionHead ci.type == some faultX do continue
      candidates := candidates.insert n m
  let mut cache : RouteCache := {}
  let mut checked := 0
  let mut exempt := 0
  let mut bad := 0
  for (n, m) in candidates.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    if n == countRec then
      exempt := exempt + 1
      if options.routes then IO.println s!"F-24-ROUTE-OK {n} ({m}): exempt"
      continue
    checked := checked + 1
    let (route, next) := proofRoute env n |>.run cache
    cache := next
    match route with
    | none =>
      IO.println s!"F-24-ROUTE {n} ({m})"
      bad := bad + 1
    | some path =>
      if options.routes then
        IO.println s!"F-24-ROUTE-OK {n} ({m}): {String.intercalate " -> " (path.map toString)}"
  IO.println s!"CheckFaultXRoute: {modules} modules; {candidates.size} FaultX theorems found; {checked} checked; {exempt} exempt; {bad} violations"
  for n in options.expected do
    unless candidates.contains n do
      throw <| IO.userError s!"expected FaultX theorem was not checked: {n}"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  try
    if args == ["--libraries"] then
      let (_, roots) ← scopedModules
      IO.println (String.intercalate " " (roots.toList.map toString))
      return 0
    match parseArgs args {} with
    | .error error => throw <| IO.userError error
    | .ok options => runCheck options
  catch error =>
    IO.eprintln s!"CheckFaultXRoute: {error}"
    return 2
