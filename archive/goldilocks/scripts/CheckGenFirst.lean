import Lean
import Lake.Toml.Load

open Lean

/-! Check (i), F-31 (GEN-FIRST): cite Gen; do not add an alias of it.

Run from the repository root on the built tree:
  lake env lean --run scripts/CheckGenFirst.lean [Module.Name ...] [--expect Name ...]
  lake env lean --run scripts/CheckGenFirst.lean --libraries

The scope comes from the lean_lib tables in lakefile.toml: all FGSA*
libraries, Shared and Claims if present, and KitFG; each library gives its
modules through its roots and globs (not through its name). Import each source
module, including modules absent from its facade. Extra modules are roots
for controls; they must be in scope. Missing compiled modules are errors.
Load private module data too: an unexposed theorem still has a proof to check.
Scan each module's own constants, not re-exports from its import closure.

Strip only leading lambdas and mdata. Keep the stripped binders as bvars:
an argument is one of these binders exactly when its index is below the
number of stripped lambdas. Do not reduce, unfold, eta-expand or erase args.
Implicit and instance binders count. Constant universe levels are unrestricted.

Skip names with internal or numeric components, or a component eq_, match_,
proof_ or omega_ followed only by digits/underscores (Name.isInternalDetail).
Also skip the generated equation suffixes eq_def, eq_unfold, splitter,
congr_eq_<digits>, induct and fun_cases. Skip deriving instances and their
helpers: a registered instance whose compiled declaration range is identical
to its selection range is generated at the deriving class token; user
instance commands have a separate declaration range. Check all name prefixes
for that marker. A missing range does not exempt an instance.

Print one exact key per finding, then a scope/count trailer. Exit 0 means
the scan completed (findings are consumed by Python); 2 means input error.
-/

def inScope (library : String) : Bool :=
  library == "AvailableChainFGCompose" ||
  library.startsWith "AvailableChainFGSA" ||
    ["AvailableChainShared", "AvailableChainClaims", "Shared", "Claims",
      "AvailableChainKitFG"].contains library

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
  for library in libraries do
    let .table _ library := library | continue
    let some n := library.find? `name | continue
    let name ← tomlString n
    unless inScope name do continue
    let srcDir ← match library.find? `srcDir with
      | some v => System.FilePath.mk <$> tomlString v
      | none => pure "."
    let rootNames := (← tomlStrings (library.find? `roots)).getD #[name]
    let globs := (← tomlStrings (library.find? `globs)).getD #[]
    -- Each root and each glob stem is a module prefix; scan every source file under it
    -- (also modules that the library's facade or globs do not build).
    let stems := rootNames ++ globs.map fun g =>
      if g.endsWith ".*" || g.endsWith ".+" then String.ofList (g.toList.take (g.length - 2)) else g
    for r in rootNames do
      roots := roots.push r.toName
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
  if libs.isEmpty then throw <| IO.userError "lakefile.toml: no GEN-FIRST libraries"
  return ((Std.HashSet.ofList libs.toList).toArray.qsort Name.lt,
    (Std.HashSet.ofList roots.toList).toArray.qsort Name.lt)

def generatedInstance (env : Environment) (n : Name) : Bool :=
  if Meta.isInstanceCore env n then
    match declRangeExt.find? (level := .server) env n with
    | some ranges => ranges.range == ranges.selectionRange
    | none => false
  else false

def skip (env : Environment) : Name → Bool
  | .str pre s =>
    let numbered (preStr : String) :=
      s.startsWith preStr && !(s.drop preStr.length).isEmpty &&
        (s.drop preStr.length).all Char.isDigit
    (Name.str pre s).isInternalDetail ||
      ["eq_def", "eq_unfold", "splitter", "induct", "fun_cases"].contains s ||
      numbered "congr_eq_" || generatedInstance env (.str pre s) || skip env pre
  | .num _ _ => true
  | .anonymous => false

def genAlias (value : Expr) : Option Name :=
  peel value 0
where
  peel (e : Expr) (binders : Nat) : Option Name :=
    match e with
    | .mdata _ body => peel body binders
    | .lam _ _ body _ => peel body (binders + 1)
    | _ => head e binders
  head (e : Expr) (binders : Nat) : Option Name :=
    match e with
    | .mdata _ body => head body binders
    | .app fn arg => if bound arg binders then head fn binders else none
    | .const n _ =>
      if n != `AvailableChain.Gen && (`AvailableChain.Gen).isPrefixOf n then some n else none
    | _ => none
  bound (e : Expr) (binders : Nat) : Bool :=
    match e with
    | .mdata _ body => bound body binders
    | .bvar i => i < binders
    | _ => false

def runCheck (extra expected : List String) : IO UInt32 := do
  let (libs, roots) ← scopedModules
  for m in extra do
    unless libs.any (·.isPrefixOf m.toName) && !m.startsWith "-" do
      throw <| IO.userError s!"extra module is not in GEN-FIRST scope: {m}"
  initSearchPath (← findSysroot)
  let env ← importModules ((roots ++ extra.toArray.map String.toName).map
    fun m => { module := m }) {} (level := .private)
  let mut keys : Std.HashSet String := {}
  let mut checked := 0
  let mut skipped := 0
  let mut modules := 0
  let mut seen : Std.HashSet Name := {}
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    unless libs.any (·.isPrefixOf m) do continue
    modules := modules + 1
    for n in env.header.moduleData[i]!.constNames do
      -- A realized matcher copy can occur in more than one module.
      if skip env n then skipped := skipped + 1; continue
      let some ci := env.find? n |
        throw <| IO.userError s!"compiled constant not found: {m} {n}"
      let some value := ci.value? (allowOpaque := true) | continue
      checked := checked + 1
      seen := seen.insert n
      if let some gen := genAlias value then
        keys := keys.insert s!"GEN-FIRST {n} {m} -> {gen}"
  for key in keys.toArray.qsort (· < ·) do IO.println key
  IO.println s!"CheckGenFirst: scope {String.intercalate " " (libs.toList.map toString)}"
  IO.println s!"CheckGenFirst: {modules} modules; {checked} bodies; {skipped} skipped; {keys.size} findings"
  for n in expected do
    unless seen.contains n.toName do
      throw <| IO.userError s!"expected declaration body was not checked: {n}"
  return 0

def main (args : List String) : IO UInt32 := do
  try
    if args == ["--libraries"] then
      -- Every scanned module is a build target: a library without globs builds only its
      -- root closure, so a module such as `Tests/Axioms` may have no object file.
      let (_, roots) ← scopedModules
      IO.println (String.intercalate " " (roots.toList.map toString))
      return 0
    let roots := args.takeWhile (· != "--expect")
    let expected := (args.drop roots.length).drop 1
    if roots.length != args.length && expected.isEmpty then
      throw <| IO.userError "--expect needs at least one declaration name"
    runCheck roots expected
  catch error =>
    IO.eprintln s!"CheckGenFirst: {error}"
    return 2
