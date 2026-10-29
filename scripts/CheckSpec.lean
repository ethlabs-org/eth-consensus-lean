import Lean
open Lean Meta

/-!
# CheckSpec: compiled-environment checks of the trust boundary

Run with `lake env lean --run scripts/CheckSpec.lean <command> [options]`, after `lake build`.

Commands (every one takes `--lib <Root>` (repeatable), `--src <dir>` (default `.`) and `--no-root`):

* `sanity`      every metadata query used below answers correctly on known constants.
* `imports`     import closure rules (`--allowed P1,P2`, `--root-covers`, `--no-root-imports`).
* `content`     no Prop-typed constant (proof) except projections, allowlisted instances of a permitted
                Prop class (`--allowlist f`; `Countable` only) and generated auxiliaries: no declaration
                range of their own (every declaration written in the source has one), a known suffix
                one component below an owned parent of the kind that suffix is generated for, and, for
                elaborator auxiliaries, reachable from the parent's value; no axiom, opaque, unsafe,
                partial, implemented_by, extern, csimp; roots own nothing; dependencies.
* `axioms`      every owned constant uses only `propext`, `Classical.choice`, `Quot.sound`.
* `review`      review statements against theorems and source theorems (`--pairs f`) and the wiring
                `--wired Root:Module` (default `ConsensusTests:ConsensusTests.ReviewAxioms`, always checked).
* `snapshot`    readable snapshot (default) or canonical hash file (`--canonical`), `--out f`;
                `--show <name>` prints the canonical S-expressions of one constant.
* `canon-dump`  full canonical S-expressions of every owned constant, one file per module (`--out dir`).
* `spec-source` source ban on the inventory's files: banned words as tokens anywhere outside comments and
                strings (any indentation, behind `set_option … in`/`open … in`, multi-line), every
                `#command`, and attributes that register user code; fail-closed on raw/multi-line strings.

Diagnostics only: `--modules A,B` replaces the inventory by the listed modules (no files, no roots).

Inventory of `--lib R`: the module `R` (file `<src>/R.lean`, unless `--no-root`) plus every module under
`<src>/R/`. The environment is loaded with `loadExts := false`, no initializers are enabled, and metadata
is read only from imported module entries, so no code from the checked modules runs here.

Every failure prints a stable tag `FAIL[<rule>] ...`. Exit code: 0 pass, 1 check failed, 2 usage or
sanity failure.
-/

namespace CheckSpec

/-! ## Options and inventory -/

structure Opts where
  cmd : String := ""
  libs : Array Name := #[]
  src : System.FilePath := "."
  noRoot : Bool := false
  allowed : Array Name := #[]
  rootCovers : Bool := false
  noRootImports : Bool := false
  allowlist : Option System.FilePath := none
  pairs : Option System.FilePath := none
  stmtModule : Name := `ConsensusSpec.Statements
  thmModule : Name := `ConsensusProofs.Review
  /-- review wiring `Root:Module` (§4.4 item 4); defaults to the production pair. -/
  wired : Name × Name := (`ConsensusTests, `ConsensusTests.ReviewAxioms)
  canonical : Bool := false
  out : Option System.FilePath := none
  showName : Option Name := none
  /-- Diagnostic only: replace the inventory by these modules (`--modules A,B`). -/
  modules : Array Name := #[]

def splitComma (s : String) : Array Name :=
  (s.splitOn ",").toArray.filterMap fun p =>
    let p := p.trimAscii.toString
    if p.isEmpty then none else some p.toName

partial def parseArgs (o : Opts) : List String → Except String Opts
  | [] => .ok o
  | "--lib" :: v :: rest => parseArgs { o with libs := o.libs.push v.toName } rest
  | "--src" :: v :: rest => parseArgs { o with src := v } rest
  | "--no-root" :: rest => parseArgs { o with noRoot := true } rest
  | "--allowed" :: v :: rest => parseArgs { o with allowed := o.allowed ++ splitComma v } rest
  | "--root-covers" :: rest => parseArgs { o with rootCovers := true } rest
  | "--no-root-imports" :: rest => parseArgs { o with noRootImports := true } rest
  | "--allowlist" :: v :: rest => parseArgs { o with allowlist := some v } rest
  | "--pairs" :: v :: rest => parseArgs { o with pairs := some v } rest
  | "--stmt-module" :: v :: rest => parseArgs { o with stmtModule := v.toName } rest
  | "--thm-module" :: v :: rest => parseArgs { o with thmModule := v.toName } rest
  | "--wired" :: v :: rest =>
    match v.splitOn ":" with
    | [r, m] => parseArgs { o with wired := (r.toName, m.toName) } rest
    | _ => .error s!"--wired expects Root:Module, got {v}"
  | "--modules" :: v :: rest => parseArgs { o with modules := o.modules ++ splitComma v } rest
  | "--canonical" :: rest => parseArgs { o with canonical := true } rest
  | "--out" :: v :: rest => parseArgs { o with out := some v } rest
  | "--show" :: v :: rest => parseArgs { o with showName := some v.toName } rest
  | a :: _ => .error s!"unknown argument {a}"

def nameToPath (n : Name) : System.FilePath :=
  System.mkFilePath (n.components.map (·.toString))

/-- Inventory entry: module name, its file, and the library root it belongs to. -/
structure Mod where
  name : Name
  file : System.FilePath
  lib : Name

def inventory (o : Opts) : IO (Array Mod) := do
  let mut out : Array Mod := #[]
  for lib in o.libs do
    let rootFile := (o.src / nameToPath lib).addExtension "lean"
    unless o.noRoot do
      unless ← rootFile.pathExists do
        throw <| IO.userError s!"root file {rootFile} of library {lib} does not exist"
      out := out.push { name := lib, file := rootFile, lib }
    let dir := o.src / nameToPath lib
    if ← dir.isDir then
      let dirLen := dir.components.length
      for f in ← dir.walkDir do
        if f.extension == some "lean" then
          let rel := (f.withExtension "").components.drop dirLen
          let m := rel.foldl Name.str lib
          out := out.push { name := m, file := f, lib }
  return out.qsort fun a b => a.name.toString < b.name.toString

/-! ## Loading and helpers -/

def load (mods : Array Name) : IO Environment := do
  initSearchPath (← findSysroot)
  importModules (mods.map fun m => { module := m }) {} (trustLevel := 1024) (loadExts := false)

def coreCtx (opts : Options := {}) : Core.Context :=
  { fileName := "CheckSpec", fileMap := default, options := opts, maxHeartbeats := 0 }

def runCore (env : Environment) (x : CoreM α) (opts : Options := {}) : IO α :=
  x.toIO' (coreCtx opts) { env }

def runMeta (env : Environment) (x : MetaM α) (opts : Options := {}) : IO α :=
  runCore env (x.run' {} {}) opts

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def modIdx (env : Environment) (m : Name) : Option Nat :=
  env.header.moduleNames.idxOf? m

/-- The pinned base set of dependency packages (top-level module components). -/
def baseTops : List String :=
  ["Init", "Std", "Lean", "Lake", "Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets",
   "Plausible", "ImportGraph", "LeanSearchClient"]

/-- A base-set module: its top-level component is a pinned dependency package and it was not built by
this project (`projectMods`, see `projectBuilt`), so a project file named `Mathlib/….lean` is not base. -/
def isBase (projectMods : NameSet) (m : Name) : Bool :=
  !projectMods.contains m && match m.components.head? with
  | some (.str .anonymous s) => baseTops.contains s
  | _ => false

/-- Modules of the environment whose `.olean` lies in this project's own build directory
(`<cwd>/.lake/build/`; dependency packages build under `.lake/packages/`). -/
def projectBuilt (env : Environment) : IO NameSet := do
  let build ← IO.FS.realPath ((← IO.currentDir) / ".lake" / "build")
  let pfx := build.toString ++ "/"
  let mut s : NameSet := {}
  for m in env.header.moduleNames do
    let f ← try some <$> findOLean m catch _ => pure none
    if let some f := f then
      let f ← IO.FS.realPath f
      if f.toString.startsWith pfx then s := s.insert m
  return s

def kindStr : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec" | .quotInfo _ => "quot"

/-- Owned constants of the inventory, sorted by name. -/
def owned (env : Environment) (inv : Array Mod) : Array (Name × ConstantInfo) := Id.run do
  let invNames := inv.map (·.name)
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if let some m := modOf env n then
      if invNames.contains m then out := out.push (n, ci)
  out.qsort fun a b => a.1.toString < b.1.toString

def instanceNamesOf (env : Environment) (idx : Nat) : Array Name :=
  (Meta.instanceExtension.ext.getModuleEntries env idx).filterMap fun
    | .global e => e.globalName?
    | .scoped _ e => e.globalName?

def csimpNamesOf (env : Environment) (idx : Nat) : Array Name :=
  (Compiler.CSimp.ext.ext.getModuleEntries env idx).map fun
    | .global e => e.thmName
    | .scoped _ e => e.thmName

def allInstanceNames (env : Environment) (mods : Array Name) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in mods do
    if let some i := modIdx env m then
      for n in instanceNamesOf env i do s := s.insert n
  return s

/-- `n` is declared as a class (raw module entries of `classExtension`; `isClass` reads state). -/
def isClassEntry (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (classExtension.getModuleEntries env i).any (·.name == n)
  | none => false

/-- Is the type of this constant a proposition (i.e. is the constant a proof)? -/
def isPropTyped (ci : ConstantInfo) : MetaM Bool := do
  match ci with
  | .thmInfo _ => return true
  | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => isProp ci.type
  | _ => return false

/-! ## Sanity: metadata queries answer correctly (no silently empty extension state) -/

/-- Checks on constants of Lean core, present in every environment. -/
def coreSanity (env : Environment) : IO (Array String) := do
  let mut errs := #[]
  unless env.isProjectionFn ``Prod.fst do errs := errs.push "isProjectionFn Prod.fst"
  if env.isProjectionFn ``Nat.add then errs := errs.push "isProjectionFn Nat.add (should be false)"
  if (← runCore env (findDeclarationRanges? ``Nat.le_refl)).isNone then
    errs := errs.push "findDeclarationRanges? Nat.le_refl"
  unless (getReducibilityStatusCore env ``inferInstance) matches .reducible do
    errs := errs.push "reducibility inferInstance"
  if (getReducibilityStatusCore env ``Nat.lt_irrefl) matches .reducible then
    errs := errs.push "reducibility Nat.lt_irrefl (should not be reducible)"
  unless ← runMeta env (isProp (env.find? ``Nat.le_refl).get!.type) do
    errs := errs.push "isProp type of Nat.le_refl"
  if ← runMeta env (isProp (env.find? ``Nat.add).get!.type) then
    errs := errs.push "isProp type of Nat.add (should be false)"
  unless (Compiler.implementedByAttr.getParam? env ``Array.foldlM).isSome do
    errs := errs.push "implemented_by Array.foldlM"
  unless isExtern env ``Nat.add do errs := errs.push "extern Nat.add"
  let mut csimp := 0
  let mut inst := 0
  for i in [:env.header.moduleNames.size] do
    csimp := csimp + (csimpNamesOf env i).size
    inst := inst + (instanceNamesOf env i).size
  if csimp == 0 then errs := errs.push "csimp module entries empty"
  if inst == 0 then errs := errs.push "instance module entries empty"
  unless (allInstanceNames env #[`Init.Prelude]).contains ``instInhabitedNat do
    errs := errs.push "instance entry instInhabitedNat"
  unless isStructure env ``Prod do errs := errs.push "isStructure Prod"
  unless isClassEntry env ``Inhabited do errs := errs.push "class entry Inhabited"
  if isClassEntry env ``Nat then errs := errs.push "class entry Nat (should be false)"
  return errs

def reportSanity (errs : Array String) : IO UInt32 := do
  if errs.isEmpty then return 0
  for e in errs do IO.eprintln s!"FAIL[sanity] {e}"
  return 2

/-- `sanity`: core checks plus project and fixture constants. -/
def cmdSanity (o : Opts) : IO UInt32 := do
  let fixtures := #[`CheckFixtures.BadImplBy, `CheckFixtures.BadExtern, `CheckFixtures.BadCSimp,
    `CheckFixtures.GoodSpec]
  let env ← load (o.libs ++ fixtures)
  let mut errs ← coreSanity env
  let some ci := env.find? `Consensus.Good.behaviour | return ← reportSanity #["Consensus.Good.behaviour missing"]
  unless env.isProjectionFn ci.name do errs := errs.push "isProjectionFn Consensus.Good.behaviour"
  if (← runCore env (findDeclarationRanges? `Consensus.Good)).isNone then
    errs := errs.push "findDeclarationRanges? Consensus.Good"
  unless (getReducibilityStatusCore env `Consensus.Shape.Sys) matches .reducible do
    errs := errs.push "reducibility Consensus.Shape.Sys (abbrev)"
  if ← runMeta env (isProp (env.find? `Consensus.Good).get!.type) then
    errs := errs.push "isProp: Consensus.Good is a Prop-valued definition, not a proof"
  unless (Compiler.implementedByAttr.getParam? env `CheckFixtures.BadImplBy.f).isSome do
    errs := errs.push "implemented_by CheckFixtures.BadImplBy.f"
  unless isExtern env `CheckFixtures.BadExtern.f do errs := errs.push "extern CheckFixtures.BadExtern.f"
  let csimpMod := `CheckFixtures.BadCSimp.A
  unless ((modIdx env csimpMod).map (csimpNamesOf env ·) |>.getD #[]).contains
      `CheckFixtures.BadCSimp.f_eq do
    errs := errs.push "csimp entry CheckFixtures.BadCSimp.f_eq"
  unless (allInstanceNames env #[`CheckFixtures.GoodSpec.A]).contains
      `CheckFixtures.GoodSpec.instCountableColor do
    errs := errs.push "instance entry CheckFixtures.GoodSpec.instCountableColor"
  -- own declaration ranges: present on declarations written in the source, absent on generated ones
  unless (← runCore env (findDeclarationRangesCore? `CheckFixtures.GoodSpec.instCountableColor)).isSome do
    errs := errs.push "own range CheckFixtures.GoodSpec.instCountableColor"
  for g in [`CheckFixtures.GoodSpec.Color.rec, `CheckFixtures.GoodSpec.Bounded.h._default,
      `CheckFixtures.GoodSpec.Color.red.sizeOf_spec] do
    unless env.contains g do errs := errs.push s!"generated constant {g} missing"
    if (← runCore env (findDeclarationRangesCore? g)).isSome then
      errs := errs.push s!"own range on generated {g} (should be none)"
  -- project-built modules
  let proj ← projectBuilt env
  unless proj.contains `CheckFixtures.GoodSpec.A do errs := errs.push "projectBuilt CheckFixtures.GoodSpec.A"
  if proj.contains `Mathlib.Logic.Equiv.Defs then errs := errs.push "projectBuilt Mathlib.Logic.Equiv.Defs (should be false)"
  if errs.isEmpty then IO.println "PASS sanity"
  reportSanity errs

/-! ## imports -/

def cmdImports (o : Opts) (inv : Array Mod) (env : Environment) (proj : NameSet) : IO UInt32 := do
  let names := env.header.moduleNames
  let data := env.header.moduleData
  let invNames := inv.map (·.name)
  let roots := if o.noRoot then #[] else o.libs
  let idxOf (m : Name) : Option Nat := modIdx env m
  -- parent pointers for "reached from" (BFS from the inventory)
  let mut parent : Std.HashMap Nat Nat := {}
  let mut queue : Array Nat := #[]
  let mut seen : Std.HashSet Nat := {}
  for m in invNames do
    if let some i := idxOf m then
      queue := queue.push i; seen := seen.insert i
  let mut qi := 0
  while qi < queue.size do
    let i := queue[qi]!
    qi := qi + 1
    for imp in data[i]!.imports do
      if let some j := idxOf imp.module then
        unless seen.contains j do
          seen := seen.insert j; parent := parent.insert j i; queue := queue.push j
  let chain (j : Nat) : String := Id.run do
    let mut path := #[names[j]!]
    let mut k := j
    for _ in [:names.size] do
      match parent.get? k with
      | some p => path := path.push names[p]!; k := p
      | none => break
    return " <- ".intercalate (path.toList.map toString)
  let mut bad := false
  for j in queue do
    let m := names[j]!
    let ok := o.allowed.any (·.isPrefixOf m) || isBase proj m
    unless ok do
      IO.println s!"FAIL[import] {m} (reached: {chain j})"
      bad := true
  if o.rootCovers then
    for r in roots do
      let some ri := idxOf r | continue
      let mut cl : Std.HashSet Nat := {}
      let mut st := #[ri]
      while h : st.size > 0 do
        let i := st.back
        st := st.pop
        unless cl.contains i do
          cl := cl.insert i
          for imp in data[i]!.imports do
            if let some j := idxOf imp.module then st := st.push j
      for md in inv do
        if md.lib == r then
          if let some i := idxOf md.name then
            unless cl.contains i do
              IO.println s!"FAIL[root] {md.name} is not in the import closure of root {r}"
              bad := true
  if o.noRootImports then
    let pkgRoots : Array Name := o.libs ++ #[`ConsensusSpec, `ConsensusProofs, `ConsensusInstances,
      `ConsensusTests, `ConsensusProblem, `ConsensusModel, `ConsensusModelProofs, `ConsensusBlocks,
      `ConsensusShape, `ConsensusShapeTests]
    for md in inv do
      if roots.contains md.name then continue
      if let some i := idxOf md.name then
        for imp in data[i]!.imports do
          if pkgRoots.contains imp.module then
            IO.println s!"FAIL[root-import] {md.name} imports package root {imp.module}"
            bad := true
  if bad then return 1
  IO.println s!"PASS imports: {queue.size} modules in the closure of {inv.size} inventory modules"
  return 0

/-! ## content -/

/-- Allowlist line: `name  class=C  # reason`. -/
def parseAllowlist (f : System.FilePath) : IO (Array (Name × Name)) := do
  let mut out := #[]
  for line in ← IO.FS.lines f do
    let line := ((line.splitOn "#").headD "").trimAscii.toString
    if line.isEmpty then continue
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws with
    | [n, c] =>
      if c.startsWith "class=" then out := out.push (n.toName, (c.drop 6).toString.toName)
      else throw <| IO.userError s!"bad allowlist line: {line}"
    | _ => throw <| IO.userError s!"bad allowlist line: {line}"
  return out

def isDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- `_proof_3`, `_proof_1_2`, `_simp_1_4` style: prefix followed by `_`-separated numbers. -/
def numbered (pfx s : String) : Bool :=
  s.startsWith pfx && (let rest := (s.drop pfx.length).toString
    !rest.isEmpty && (rest.splitOn "_").all isDigits)

/-- What a generated suffix requires of its parent constant `p = n.getPrefix`. -/
inductive GenKind where
  /-- kernel lemma of a constructor (`injEq`, `inj`, `sizeOf_spec`, `_flat_ctor`, `congr_simp`) -/
  | ofCtor
  /-- kernel lemma of an inductive type (`ofNat_ctorIdx`, `_sizeOf_<n>_eq`) -/
  | ofInduct
  /-- equational lemma of a non-Prop definition (`eq_<n>`, `eq_def`, `eq_unfold`, `splitter`,
  `congr_simp`, `else_eq`; `brecOn.eq`) -/
  | ofDefn
  /-- elaborator auxiliary proof (`_proof_<n>`, `_simp_<n>`, `proof_<n>`): must also be reachable from
  the parent's value -/
  | aux
  /-- default value of a structure field: the parent is the field's projection -/
  | dflt
  deriving BEq, Repr

/-- Classify the last component `s` of a generated name. A suffix that is generated for several parent
kinds (`congr_simp`) is classified by the parent constant `pci`; `pIsBrecOn`: the parent is a
`brecOn`/`brecOn_<n>` definition. -/
def genKind (s : String) (pci : ConstantInfo) (pIsBrecOn : Bool) : Option GenKind :=
  let isCtor := pci matches .ctorInfo _
  let isDefn := pci matches .defnInfo _
  if ["sizeOf_spec", "injEq", "inj", "_flat_ctor"].contains s then some .ofCtor
  else if s == "congr_simp" then (if isCtor then some .ofCtor else if isDefn then some .ofDefn else none)
  else if s == "ofNat_ctorIdx" ||
      (s.startsWith "_sizeOf_" && s.endsWith "_eq" && isDigits ((s.drop 8).dropEnd 3).toString) then
    some .ofInduct
  else if ["eq_def", "eq_unfold", "splitter", "else_eq"].contains s || numbered "eq_" s then some .ofDefn
  else if s == "eq" && pIsBrecOn then some .ofDefn
  else if numbered "_proof_" s || numbered "_simp_" s || numbered "proof_" s then some .aux
  else if s == "_default" then some .dflt
  else none

/-- The constant has its own declaration range (the elaborator records one for every declaration a user
writes: `def`, `theorem`, `instance`, `where`/`let rec` functions, structure fields, constructors). The
compiler and the kernel do not record ranges for the auxiliaries they generate. -/
def hasOwnRange (env : Environment) (n : Name) : IO Bool := do
  return (← runCore env (findDeclarationRangesCore? n)).isSome

/-- Constants reachable from `p` through used-constant edges among `p`'s generated auxiliaries
(names with prefix `p`). The walk starts at `p` and at its compiler/structural-recursion companions
(`p._sunfold`, `p._unsafe_rec`, ...): non-Prop definitions without a declaration range, so a companion
written by hand is never a starting point. -/
def reachableAux (env : Environment) (rangeless : Name → Bool) (p : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let companions := ["_sunfold", "_unsafe_rec", "_f", "_unary", "_binary", "_mutual"].map (Name.str p ·)
    |>.filter fun c => rangeless c && (env.find? c matches some (.defnInfo _))
  let mut st : Array Name := #[p] ++ companions.toArray
  while h : st.size > 0 do
    let q := st.back
    st := st.pop
    let some ci := env.find? q | continue
    for d in ci.getUsedConstantsAsSet.toList do
      -- (an auxiliary of a public `p` may be private: `_private.M.0.p._proof_1`)
      if (p.isPrefixOf d || p.isPrefixOf (privateToUserName d)) && d != p && !seen.contains d then
        seen := seen.insert d; st := st.push d
  return seen

/-- The parent of a generated name: its prefix with exactly one component removed. A generated auxiliary
of a public declaration may itself be private (`_private.M.0.f.match_1.eq_1` of `f.match_1`), so for a
private name the prefix of its user name is the parent when the private prefix is not a constant. -/
def genParent (env : Environment) (n : Name) : Option Name :=
  if env.contains n.getPrefix then some n.getPrefix
  else match privateToUserName? n with
    | some u => if env.contains u.getPrefix then some u.getPrefix else none
    | none => none

/-- Rule (b): `n` (Prop-typed, no declaration range of its own) is a generated auxiliary: its last
component is a known generated suffix, its parent (exactly one component up) is an owned constant of the
kind that suffix is generated for, the parent is not itself a proof (except inductives, constructors and,
for field defaults, projections), the type of a kernel/equational lemma mentions the parent, and an
elaborator auxiliary is reachable from the parent's value. Returns the reason on failure. -/
def genCheck (env : Environment) (ownedSet propSet : NameSet) (rangeless : Name → Bool)
    (n : Name) (ci : ConstantInfo) : Option String := Id.run do
  let .str _ s := n | return some "not a generated name"
  let some p := genParent env n | return some "no parent constant one component up"
  let some pci := env.find? p | return some "no parent constant"
  unless ownedSet.contains p do return some s!"parent {p} is not owned by the checked library"
  let pIsBrecOn := match p with
    | .str _ b => b == "brecOn" || numbered "brecOn_" b
    | _ => false
  let some k := genKind s pci pIsBrecOn | return some s!"suffix {s} is not generated for a {kindStr pci} parent"
  let parentIsProof := propSet.contains p && !env.isProjectionFn p
  let isCtor := match pci with | .ctorInfo _ => true | _ => false
  let isInduct := match pci with | .inductInfo _ => true | _ => false
  let isDefn := match pci with | .defnInfo _ => true | _ => false
  let kindOk : Bool := match k with
    | .ofCtor => isCtor
    | .ofInduct => isInduct
    | .ofDefn | .aux => isDefn && !parentIsProof && !env.isProjectionFn p
    | .dflt => env.isProjectionFn p
  unless kindOk do return some s!"suffix {s} is not generated for parent {p} ({kindStr pci})"
  let structural := k == .ofCtor || k == .ofInduct || k == .ofDefn
  if structural && s != "_flat_ctor" && !ci.type.getUsedConstants.contains p then
    return some s!"type does not mention its parent {p}"
  if k == .aux && !(reachableAux env rangeless p).contains n then
    return some s!"not reachable from the value of {p}"
  return none

/-- Prop classes whose instances may be allowlisted (rule (c)). -/
def allowedPropClasses : List Name := [`Countable]

def cmdContent (o : Opts) (inv : Array Mod) (env : Environment) (proj : NameSet) : IO UInt32 := do
  let invNames := inv.map (·.name)
  let roots := if o.noRoot then #[] else o.libs
  let allow ← match o.allowlist with
    | some f => parseAllowlist f
    | none => pure #[]
  let cs := owned env inv
  let ownedSet : NameSet := cs.foldl (fun s (n, _) => s.insert n) {}
  let mut fails : Array String := #[]
  -- csimp entries of the inventory modules
  for m in invNames do
    if let some i := modIdx env m then
      for t in csimpNamesOf env i do fails := fails.push s!"FAIL[csimp] {t}"
  -- allowlist hygiene
  for (n, _) in allow do
    unless ownedSet.contains n do fails := fails.push s!"FAIL[allowlist-stale] {n}"
  let propSet ← runMeta env do
    let mut s : NameSet := {}
    for (n, ci) in cs do
      if ← isPropTyped ci then s := s.insert n
    return s
  let rangeSet : NameSet ← cs.foldlM (init := {}) fun s (n, _) => do
    return if ← hasOwnRange env n then s.insert n else s
  for (n, ci) in cs do
    let m := (modOf env n).get!
    if roots.contains m then fails := fails.push s!"FAIL[root-decl] {n} (owned by root {m})"
    match ci with
    | .axiomInfo _ => fails := fails.push s!"FAIL[axiom] {n}"
    | .opaqueInfo _ => fails := fails.push s!"FAIL[opaque] {n}"
    | _ => pure ()
    if ci.isUnsafe then fails := fails.push s!"FAIL[unsafe] {n}"
    -- `X._unsafe_rec` (partial safety) is the compiler's implementation of an ordinary recursive
    -- definition `X`; for a `partial def X`, `X` is an opaque and this fails.
    if ci.isPartial || n.components.any (· == `_unsafe_rec) then
      let compilerAux : Bool := match n with
        | .str p "_unsafe_rec" => ownedSet.contains p &&
            (match env.find? p with | some (.defnInfo d) => d.safety == .safe | _ => false)
        | _ => false
      unless compilerAux do fails := fails.push s!"FAIL[partial] {n}"
    if (Compiler.implementedByAttr.getParam? env n).isSome then
      fails := fails.push s!"FAIL[implemented-by] {n}"
    if isExtern env n then fails := fails.push s!"FAIL[extern] {n}"
    -- dependencies
    for d in ci.getUsedConstantsAsSet.toList do
      let ok := match modOf env d with
        | some dm => invNames.contains dm || isBase proj dm
        | none => false
      unless ok do
        fails := fails.push s!"FAIL[dep] {n} uses {d} ({(modOf env d).getD `unknown})"
    -- Prop-typed constants
    if propSet.contains n then
      match ci with
      | .defnInfo _ | .thmInfo _ => pure ()
      | _ => continue
      if env.isProjectionFn n then continue
      -- (c) allowlisted Prop-class instance
      if let some (_, cls) := allow.find? (·.1 == n) then
        let ok : Bool := match ci.type.getForallBody.getAppFn with
          | .const c _ => c == cls && allowedPropClasses.contains cls && isClassEntry env cls &&
              (match env.find? cls with
              | some cc => cc.type.getForallBody == .sort .zero
              | none => false)
          | _ => false
        if ok then continue
        fails := fails.push s!"FAIL[theorem] {n} (allowlisted as class={cls}, but {cls} is not a permitted Prop class ({allowedPropClasses}) or its type is not an instance of it)"
        continue
      -- a declaration written by hand (it has a declaration range) is never a generated auxiliary
      if rangeSet.contains n then
        fails := fails.push s!"FAIL[theorem] {n} (a proof declared in the source)"
        continue
      -- (b) generated auxiliary of a permitted parent
      if let some why := genCheck env ownedSet propSet (fun c => !rangeSet.contains c) n ci then
        fails := fails.push s!"FAIL[theorem] {n} ({why})"
  if fails.isEmpty then
    IO.println s!"PASS content: {cs.size} constants in {inv.size} modules"
    return 0
  for f in fails do IO.println f
  return 1

/-! ## axioms -/

def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

def cmdAxioms (_o : Opts) (inv : Array Mod) (env : Environment) : IO UInt32 := do
  let cs := owned env inv
  let mut bad := false
  for (n, _) in cs do
    let axs ← runCore env (collectAxioms n)
    for ax in axs do
      unless allowedAxioms.contains ax do
        IO.println s!"FAIL[axiom-use] {n} uses {ax}"
        bad := true
  if cs.isEmpty then
    IO.eprintln "no declarations found"
    return 2
  if bad then return 1
  IO.println s!"PASS axioms: {cs.size} declarations in {inv.size} modules use only propext, Classical.choice, Quot.sound"
  return 0

/-! ## Canonical serialization -/

/-- Universe levels; a universe parameter is printed as its index in the constant's parameter list (its
name may be hygienic and contain the module name). -/
def lvl (ps : List Name) : Level → String
  | .zero => "0"
  | .succ l => s!"(s {lvl ps l})"
  | .max a b => s!"(max {lvl ps a} {lvl ps b})"
  | .imax a b => s!"(imax {lvl ps a} {lvl ps b})"
  | .param n => match ps.idxOf? n with
    | some i => s!"(u {i})"
    | none => s!"(p {n})"
  | .mvar _ => "(lmvar)"

def bi : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

/-- Deterministic S-expression of an elaborated term: binder names and `mdata` dropped, binder kinds,
universe levels, literals and projections kept. -/
partial def ser (ps : List Name) (e : Expr) (acc : String) : String :=
  let ser := ser ps
  let lvl := lvl ps
  match e with
  | .bvar i => acc ++ s!"#{i}"
  | .fvar _ => acc ++ "(fvar)"
  | .mvar _ => acc ++ "(mvar)"
  | .sort l => acc ++ s!"(sort {lvl l})"
  | .const n ls => acc ++ s!"(c {n}" ++ String.join (ls.map (" " ++ lvl ·)) ++ ")"
  | .app .. =>
    let args := e.getAppArgs
    let acc := ser e.getAppFn (acc ++ "(a ")
    (args.foldl (fun acc a => ser a (acc ++ " ")) acc) ++ ")"
  | .lam _ t b k => ser b (ser t (acc ++ s!"(lam {bi k} ") ++ " ") ++ ")"
  | .forallE _ t b k => ser b (ser t (acc ++ s!"(pi {bi k} ") ++ " ") ++ ")"
  | .letE _ t v b _ => ser b (ser v (ser t (acc ++ "(let ") ++ " ") ++ " ") ++ ")"
  | .lit (.natVal n) => acc ++ s!"(nat {n})"
  | .lit (.strVal s) => acc ++ s!"(str {s.quote})"
  | .mdata _ b => ser b acc
  | .proj s i b => ser b (acc ++ s!"(proj {s} {i} ") ++ ")"

def sexpr (ps : List Name) (e : Expr) : String := ser ps e ""

def names (ns : List Name) : String := "(" ++ " ".intercalate (ns.map toString) ++ ")"

/-- Canonical type and value of a constant; the value of a Prop-typed constant is erased (`-`). -/
def canonOf (ci : ConstantInfo) (isPropT : Bool) : String × String :=
  let sexpr := sexpr ci.levelParams
  let t := sexpr ci.type
  let v := match ci with
    | .defnInfo d =>
      -- `unsafe` is part of the meaning; written only when present, so other definitions hash as before
      -- (`partial` safety only occurs on the compiler's `X._unsafe_rec`; a `partial def X` is an opaque)
      let sf := if d.safety == .unsafe then "(safety unsafe) " else ""
      if isPropT then sf ++ "-" else sf ++ sexpr d.value
    | .thmInfo _ => "-"
    | .opaqueInfo d => if isPropT then "-" else sexpr d.value
    | .axiomInfo _ => "-"
    | .quotInfo _ => "-"
    | .inductInfo d =>
      s!"(ind {d.numParams} {d.numIndices} {names d.all} {names d.ctors} {d.isRec} {d.isReflexive} {d.isUnsafe})"
    | .ctorInfo d => s!"(ctor {d.induct} {d.cidx} {d.numParams} {d.numFields})"
    | .recInfo d =>
      let rules := d.rules.map fun r => s!"(rule {r.ctor} {r.nfields} {sexpr r.rhs})"
      s!"(rec {names d.all} {d.numParams} {d.numIndices} {d.numMotives} {d.numMinors} {d.k} " ++
        " ".intercalate rules ++ ")"
  (t, v)

/-! ## SHA-256 (for the canonical hash file) -/

def shaK : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def hex32 (x : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (8 - s.length) ++ s

def sha256 (msg : ByteArray) : String := Id.run do
  let len := msg.size
  let mut m := msg.push 0x80
  while m.size % 64 != 56 do m := m.push 0
  let bits := (len * 8 : Nat)
  for i in [:8] do m := m.push ((bits >>> ((7 - i) * 8)) % 256).toUInt8
  let mut h : Array UInt32 := #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
  for blk in [:m.size / 64] do
    let mut w : Array UInt32 := Array.mkEmpty 64
    for t in [:16] do
      let b := blk * 64 + t * 4
      w := w.push ((m[b]!.toUInt32 <<< 24) ||| (m[b+1]!.toUInt32 <<< 16) |||
        (m[b+2]!.toUInt32 <<< 8) ||| m[b+3]!.toUInt32)
    for t in [16:64] do
      let s0 := rotr w[t-15]! 7 ^^^ rotr w[t-15]! 18 ^^^ (w[t-15]! >>> 3)
      let s1 := rotr w[t-2]! 17 ^^^ rotr w[t-2]! 19 ^^^ (w[t-2]! >>> 10)
      w := w.push (w[t-16]! + s0 + w[t-7]! + s1)
    let mut a := h[0]!; let mut b := h[1]!; let mut c := h[2]!; let mut d := h[3]!
    let mut e := h[4]!; let mut f := h[5]!; let mut g := h[6]!; let mut hh := h[7]!
    for t in [:64] do
      let S1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
      let ch := (e &&& f) ^^^ ((~~~ e) &&& g)
      let t1 := hh + S1 + ch + shaK[t]! + w[t]!
      let S0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
      let mj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := S0 + mj
      hh := g; g := f; f := e; e := d + t1; d := c; c := b; b := a; a := t1 + t2
    h := #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]
  return String.join (h.toList.map hex32)

/-! ## snapshot / canon-dump -/

def relModule (inv : Array Mod) (m : Name) : String :=
  match inv.find? (·.name == m) with
  | some md =>
    let r := m.replacePrefix md.lib .anonymous
    if r.isAnonymous then "(root)" else r.toString
  | none => m.toString

def ppOpts : Options :=
  ({} : Options)
    |>.setBool `pp.fullNames true
    |>.setBool `pp.proofs false
    |>.setBool `pp.unicode.fun true
    |>.setBool `pp.fieldNotation false
    |>.set `format.width (120 : Nat)

def indent (s : String) : String :=
  "\n".intercalate ((s.splitOn "\n").map ("    " ++ ·))

def readableKind (env : Environment) (insts : NameSet) (n : Name) (ci : ConstantInfo) : String :=
  if insts.contains n then "instance"
  else if env.isProjectionFn n then "proj"
  else match ci with
    | .defnInfo _ =>
      match getReducibilityStatusCore env n with
      | .reducible => "abbrev"
      | .irreducible => "def[irreducible]"
      | _ => "def"
    | .inductInfo _ => if isStructure env n then "structure" else "inductive"
    | _ => kindStr ci

/-- Kernel/structural auxiliaries of an inductive (or of a constructor), left out of the readable
snapshot (they are all in the canonical file): the component right below the nearest inductive or
constructor ancestor is one of these names, possibly with a `_<n>` suffix (nested inductives). -/
def kernelAuxNames : List String :=
  ["casesOn", "recOn", "rec", "noConfusion", "noConfusionType", "ctorElim", "ctorElimType", "ctorIdx",
   "elim", "below", "brecOn", "binductionOn", "ibelow", "sizeOf_spec", "injEq", "inj", "ofNat_ctorIdx",
   "toCtorIdx", "ofNat"]

def stripNumSuffix (s : String) : String :=
  match s.splitOn "_" |>.reverse with
  | last :: rest@(_ :: _) => if isDigits last then "_".intercalate rest.reverse else s
  | _ => s

def kernelAux (env : Environment) (n : Name) : Bool := Id.run do
  if n.isInternalDetail then return true
  let mut child := n
  let mut p := n.getPrefix
  while !p.isAnonymous do
    match env.find? p with
    | some (.inductInfo _) | some (.ctorInfo _) =>
      return match child with
        | .str _ s => kernelAuxNames.contains (stripNumSuffix s) || s.startsWith "_sizeOf"
        | _ => false
    | _ => pure ()
    child := p
    p := p.getPrefix
  return false

def cmdSnapshot (o : Opts) (inv : Array Mod) (env : Environment) : IO UInt32 := do
  let cs := owned env inv
  let propSet ← runMeta env do
    let mut s : NameSet := {}
    for (n, ci) in cs do
      if ← isPropTyped ci then s := s.insert n
    return s
  if let some n := o.showName then
    let some ci := env.find? n | IO.eprintln s!"unknown constant {n}"; return 2
    let (t, v) := canonOf ci (propSet.contains n)
    IO.println s!"T: {t}\nV: {v}"
    return 0
  let sorted := cs.qsort fun a b =>
    let ma := relModule inv (modOf env a.1).get!
    let mb := relModule inv (modOf env b.1).get!
    ma < mb || (ma == mb && a.1.toString < b.1.toString)
  let mut out := ""
  if o.canonical then
    for (n, ci) in sorted do
      let (t, v) := canonOf ci (propSet.contains n)
      let vh := if v == "-" then "-" else sha256 v.toUTF8
      out := out ++ s!"{kindStr ci} {n} u:{ci.levelParams.length} T:{sha256 t.toUTF8} V:{vh}\n"
  else
    let insts := allInstanceNames env (inv.map (·.name))
    let lines ← runMeta env (opts := ppOpts) do
      let mut acc : Array String := #[]
      let mut cur := ""
      for (n, ci) in sorted do
        let isCtor := ci matches .ctorInfo _
        -- own range only (`findDeclarationRanges?` lends recursors and `casesOn` their type's range)
        let hasRange := (← findDeclarationRangesCore? n).isSome
        unless hasRange || isCtor || (← getEnv).isProjectionFn n do continue
        -- the kernel-auxiliary name filter never hides a declaration written in the source
        if !hasRange && kernelAux (← getEnv) n then continue
        let m := relModule inv (modOf (← getEnv) n).get!
        if m != cur then
          acc := acc.push s!"\n## {m}"
          cur := m
        let k := readableKind (← getEnv) insts n ci
        let ty ← try pure (toString (← ppExpr ci.type)) catch _ => pure "<pp error>"
        let mut entry := s!"{k} {n} u:{ci.levelParams.length}\n  : {indent ty |>.drop 4}"
        if (k == "def" || k == "abbrev" || k == "def[irreducible]") && !propSet.contains n then
          if let .defnInfo d := ci then
            let v ← try pure (toString (← ppExpr d.value)) catch _ => pure "<pp error>"
            entry := entry ++ s!"\n  := {indent v |>.drop 4}"
        acc := acc.push entry
      return acc
    out := "# readable snapshot (printing level; the canonical file is the meaning check)\n" ++
      "\n".intercalate lines.toList ++ "\n"
  match o.out with
  | some f => IO.FS.writeFile f out
  | none => IO.print out
  return 0

def cmdCanonDump (o : Opts) (inv : Array Mod) (env : Environment) : IO UInt32 := do
  let some dir := o.out | IO.eprintln "canon-dump needs --out <dir>"; return 2
  IO.FS.createDirAll dir
  let cs := owned env inv
  let propSet ← runMeta env do
    let mut s : NameSet := {}
    for (n, ci) in cs do
      if ← isPropTyped ci then s := s.insert n
    return s
  let mut byMod : Std.HashMap Name (Array String) := {}
  for (n, ci) in cs do
    let m := (modOf env n).get!
    let (t, v) := canonOf ci (propSet.contains n)
    let line := s!"{n}\t{m}\t{kindStr ci}\tu:{ci.levelParams.length}\t{t}\t{v}"
    byMod := byMod.insert m ((byMod.getD m #[]).push line)
  for md in inv do
    let ls := byMod.getD md.name #[]
    IO.FS.writeFile (dir / s!"{md.name}.tsv") (String.join (ls.toList.map (· ++ "\n")))
  IO.println s!"canon-dump: {cs.size} constants in {inv.size} modules -> {dir}"
  return 0

/-! ## review -/

def cmdReview (o : Opts) (env : Environment) : IO UInt32 := do
  let some pf := o.pairs | IO.eprintln "review needs --pairs <file>"; return 2
  let mut fails : Array String := #[]
  let mut count := 0
  for line in ← IO.FS.lines pf do
    let line := ((line.splitOn "#").headD "").trimAscii.toString
    if line.isEmpty then continue
    let ws := (line.splitOn " ").filter (· ≠ "")
    let [s, t, src] := ws | IO.eprintln s!"bad pairs line: {line}"; return 2
    let (s, t, src) := (s.toName, t.toName, src.toName)
    count := count + 1
    -- 1. the theorem
    match env.find? t with
    | some (.thmInfo d) =>
      unless modOf env t == some o.thmModule do
        fails := fails.push s!"FAIL[review-type] {t} is not owned by {o.thmModule}"
      unless d.type == .const s [] do
        fails := fails.push s!"FAIL[review-type] {t} : {d.type} is not syntactically {s}"
    | _ => fails := fails.push s!"FAIL[review-type] {t} is not a theorem"
    -- 2. the statement
    match env.find? s with
    | some (.defnInfo d) =>
      unless modOf env s == some o.stmtModule do
        fails := fails.push s!"FAIL[review-type] {s} is not owned by {o.stmtModule}"
      unless d.type == .sort .zero do fails := fails.push s!"FAIL[review-type] {s} is not of type Prop"
      -- 3. statement body = source theorem type (binder names dropped by `sexpr`)
      match env.find? src with
      | some sci =>
        unless sexpr [] d.value == sexpr sci.levelParams sci.type do
          fails := fails.push s!"FAIL[review-source] {s} is not the type of {src}"
      | none => fails := fails.push s!"FAIL[review-source] source theorem {src} not found"
    | _ => fails := fails.push s!"FAIL[review-type] {s} is not a definition"
  -- 4. wiring
  let (r, m) := o.wired
  let ok := match modIdx env r with
    | some i => env.header.moduleData[i]!.imports.any (·.module == m)
    | none => false
  unless ok do fails := fails.push s!"FAIL[review-wired] {r} does not import {m} (or {r} is not loaded)"
  if count == 0 then IO.eprintln "no review pairs"; return 2
  if fails.isEmpty then
    IO.println s!"PASS review: {count} statements"
    return 0
  for f in fails do IO.println f
  return 1

/-! ## spec-source: source ban on the inventory files -/

/-- Remove comments (nested block comments, docstrings, line comments), string literals and character
literals, keeping line breaks. Fail-closed: the stripper must never remove code, so constructs it does
not model are reported (raw string literals, string literals spanning lines). -/
def stripComments (s : String) : String × Array String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut errs : Array String := #[]
  let mut i := 0
  let mut depth := 0
  let mut inStr := false
  let mut line := 1
  let mut strLine := 0
  let identLike (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'
  while i < cs.size do
    let c := cs[i]!
    let n := cs[i+1]?.getD ' '
    let prev := if i == 0 then ' ' else cs[i-1]!
    if c == '\n' then line := line + 1
    if depth > 0 then
      if c == '/' && n == '-' then depth := depth + 1; i := i + 2
      else if c == '-' && n == '/' then depth := depth - 1; i := i + 2
      else
        if c == '\n' then out := out.push '\n'
        i := i + 1
    else if inStr then
      if c == '\\' then
        if n == '\n' then line := line + 1; out := out.push '\n'
        i := i + 2
      else
        if c == '"' then inStr := false
        if c == '\n' then
          out := out.push '\n'
          errs := errs.push s!"{strLine}: string literal spans lines"
        i := i + 1
    else if c == '/' && n == '-' then depth := 1; i := i + 2
    else if c == '-' && n == '-' then
      while i < cs.size && cs[i]! != '\n' do i := i + 1
    else if c == '"' then
      if prev == 'r' || prev == '#' then errs := errs.push s!"{line}: raw string literal"
      inStr := true; strLine := line; out := out.push ' '; i := i + 1
    else if c == '\'' && !identLike prev then
      -- character literal: 'x' or an escape '\..'
      if n == '\\' then
        let mut j := i + 2
        while j < cs.size && cs[j]! != '\'' && cs[j]! != '\n' do j := j + 1
        out := out.push ' '; i := if cs[j]? == some '\'' then j + 1 else j
      else if cs[i+2]? == some '\'' then out := out.push ' '; i := i + 3
      else out := out.push c; i := i + 1
    else out := out.push c; i := i + 1
  if inStr then errs := errs.push s!"{strLine}: unterminated string literal"
  if depth > 0 then errs := errs.push "unterminated block comment"
  return (String.ofList out.toList, errs)

/-- Words that may not occur anywhere in a Spec file outside comments and strings: commands that state
or discard a proof (`example`, `theorem`, `lemma`), add an axiom or an unchecked constant, or run a user
metaprogram. Matched as whole tokens anywhere, whatever the indentation or wrapper (`set_option … in`,
`open … in`, multi-line commands); in addition every `#command` is banned. -/
def bannedWords : List String :=
  ["example", "theorem", "lemma", "axiom", "opaque", "unsafe", "partial", "run_cmd", "run_elab",
   "run_meta", "elab", "elab_rules", "macro", "macro_rules", "syntax", "declare_syntax_cat",
   "initialize", "builtin_initialize", "meta", "implemented_by", "extern", "csimp",
   "simproc", "dsimproc", "simproc_decl", "dsimproc_decl"]

/-- Attribute names banned inside attribute brackets (`@[…]`, `attribute […]`): they register user code
to run at elaboration time (elaborators, macros, delaborators, simprocs, initializers) or replace compiled
code. Only inside brackets, since some are ordinary identifiers elsewhere (a field `init`). -/
def bannedAttrs : List String :=
  ["init", "builtin_init", "tactic", "builtin_tactic", "command_elab", "builtin_command_elab",
   "term_elab", "builtin_term_elab", "macro", "builtin_macro", "delab", "builtin_delab", "app_unexpander",
   "env_extension", "implemented_by", "extern", "csimp", "simproc", "dsimproc", "builtin_simproc",
   "builtin_dsimproc", "command_parser", "term_parser", "tactic_parser", "code_action",
   "command_code_action", "builtin_doc", "widget_module"]

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '#' || c == '.' || c == '\''

def tokens (s : String) : List String :=
  (s.split (fun c => !isIdentChar c)).toList.map (·.toString) |>.filter (· ≠ "")

/-- A `#`-command token (`#eval`, `#exit`, `#guard`, `#print`, ...); `#[` array literals give `#`. -/
def isHashCommand (t : String) : Bool :=
  t.startsWith "#" && ((t.drop 1).toString.toList.head?.map Char.isAlpha).getD false

/-- Contents of every attribute bracket (`@[…]`, `attribute […]`) of a stripped text, bracket-balanced,
with the line it starts on. -/
def attrBlocks (text : String) : Array (Nat × String) := Id.run do
  let cs := text.toList.toArray
  let mut out := #[]
  let mut line := 1
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    if c == '\n' then line := line + 1
    -- an attribute bracket opens at `@[`, or at the first `[` after the token `attribute`
    let mut opens : Option Nat := none
    if c == '@' && cs[i+1]? == some '[' then opens := some (i + 1)
    else if c == 'a' && (i == 0 || !isIdentChar cs[i-1]!) &&
        String.ofList (cs.extract i (i + 9)).toList == "attribute" &&
        !((cs[i+9]?.map isIdentChar).getD false) then
      let mut j := i + 9
      while j < cs.size && cs[j]!.isWhitespace do j := j + 1
      if cs[j]? == some '[' then opens := some j
    if let some j0 := opens then
      let mut depth := 0
      let mut j := j0
      let mut acc : Array Char := #[]
      while j < cs.size do
        let d := cs[j]!
        if d == '[' then depth := depth + 1
        if d == ']' then depth := depth - 1
        acc := acc.push d
        j := j + 1
        if depth == 0 then break
      out := out.push (line, String.ofList acc.toList)
    i := i + 1
  return out

def cmdSpecSource (inv : Array Mod) : IO UInt32 := do
  let mut bad := false
  for md in inv do
    let (text, errs) := stripComments (← IO.FS.readFile md.file)
    for e in errs do
      IO.println s!"FAIL[spec-source] {md.file}:{e} (not supported in Spec sources)"
      bad := true
    let mut ln := 0
    for line in text.splitOn "\n" do
      ln := ln + 1
      for t in tokens line do
        if bannedWords.contains t || isHashCommand t then
          IO.println s!"FAIL[spec-source] {md.file}:{ln}: {t}"
          bad := true
    for (l, blk) in attrBlocks text do
      for t in tokens blk do
        if bannedAttrs.contains t then
          IO.println s!"FAIL[spec-source] {md.file}:{l}: attribute {t}"
          bad := true
  if bad then return 1
  IO.println s!"PASS spec-source: {inv.size} files"
  return 0

/-! ## main -/

def run (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    IO.eprintln "usage: CheckSpec <sanity|imports|content|axioms|review|snapshot|canon-dump|spec-source> --lib R ..."
    return 2
  | cmd :: rest =>
  let o ← match parseArgs { cmd } rest with
    | .ok o => pure o
    | .error e => IO.eprintln e; return 2
  if o.libs.isEmpty then IO.eprintln "no --lib given"; return 2
  if cmd == "sanity" then return ← cmdSanity o
  let inv ← if o.modules.isEmpty then inventory o else
    pure (o.modules.map fun m => { name := m, file := "", lib := .anonymous })
  if inv.isEmpty then IO.eprintln "empty inventory"; return 2
  if cmd == "spec-source" then return ← cmdSpecSource inv
  let env ← load (inv.map (·.name))
  -- every loaded module of the inventory is present
  for md in inv do
    if (modIdx env md.name).isNone then
      IO.eprintln s!"FAIL[sanity] inventory module {md.name} not loaded"
      return 2
  let rc ← reportSanity (← coreSanity env)
  if rc != 0 then return rc
  match cmd with
  | "imports" => cmdImports o inv env (← projectBuilt env)
  | "content" => cmdContent o inv env (← projectBuilt env)
  | "axioms" => cmdAxioms o inv env
  | "review" => cmdReview o env
  | "snapshot" => cmdSnapshot o inv env
  | "canon-dump" => cmdCanonDump o inv env
  | c => IO.eprintln s!"unknown command {c}"; return 2

end CheckSpec

def main (args : List String) : IO UInt32 := do
  try CheckSpec.run args
  catch e =>
    IO.eprintln s!"error: {e}"
    return 2
