import AvailableChainFramework
import AvailableChainEngineV2
import AvailableChainKitV2
open Lean

/-! Current API snapshots. Run --write after a source change and review the diff.
--check compares the complete compiled scope with the committed snapshot.
Theorem proof values are excluded. Other attributes, such as simp membership
and instance priority, are not fully covered. V2 retains engine anchor coverage.
Deep mode uses full kernel dependency digests and readable review evidence.
No snapshot update grants approval for a changed claim. -/

inductive Scope where
  | v2 | gen | fgsa | pcsa
  deriving BEq

def anchorName : Name := `AvailableChain.Framework.V2.anchor
def anchorModule : Name := `AvailableChainFramework.V2.Anchor
/-- The modules of the anchor defs. -/
def anchorPrefix : Name := `AvailableChainFramework.V2
/-- A declaration that has a declaration range when the `.olean.server` data
is present (the guard of `scripts/CatalogLock.lean`). -/
def rangeProbe : Name := `AvailableChain.V2.ProtocolSpec

/-- The engine modules (locked through the anchors). -/
def engineScope : List Name :=
  [`AvailableChainEngineV2.Engine, `AvailableChainEngineV2.Conditions,
   `AvailableChainEngineV2.Laws]

def kitLibrary : Name := `AvailableChainKitV2
def kitTests : Name := `AvailableChainKitV2.Tests

def fgsaLibraries : Array Name :=
  #[`AvailableChainFGSA, `AvailableChainFGSARun, `AvailableChainFGSAClaims]

/-- Module prefixes of the fgsa scope: the three Statements trees and the claim modules
`Claims/*` (the safety claims live there). -/
def fgsaPrefixes : Array Name :=
  #[`AvailableChainFGSA.Statements, `AvailableChainFGSARun.Statements,
    `AvailableChainFGSAClaims.Statements, `AvailableChainFGSAClaims.Claims]

/-- Exact modules of the fgsa scope: the claim facade that assembles `FGSASafetyClaims`. -/
def fgsaModules : Array Name := #[`AvailableChainFGSAClaims.FGSAClaims]

def pcsaLibraries : Array Name :=
  #[`AvailableChainPCSA, `AvailableChainPCSARun, `AvailableChainPCSAClaims]

/-- Module prefixes of the pcsa scope: the `fgsaPrefixes` shape with the PC-SA names. -/
def pcsaPrefixes : Array Name :=
  #[`AvailableChainPCSA.Statements, `AvailableChainPCSARun.Statements,
    `AvailableChainPCSAClaims.Statements, `AvailableChainPCSAClaims.Claims]

/-- Exact modules of the pcsa scope: the facade with `PCSAClaims` and `PCSAStageTwoClaims`. -/
def pcsaModules : Array Name := #[`AvailableChainPCSAClaims.PCSAClaims]

/-- The scopes that include public fields and explicit equations. -/
def isFamily (scope : Scope) : Bool := scope == .fgsa || scope == .pcsa

def familyLibraries : Scope → Array Name
  | .fgsa => fgsaLibraries | .pcsa => pcsaLibraries | _ => #[]

def familyPrefixes : Scope → Array Name
  | .fgsa => fgsaPrefixes | .pcsa => pcsaPrefixes | _ => #[]

def familyModules : Scope → Array Name
  | .fgsa => fgsaModules | .pcsa => pcsaModules | _ => #[]

def isEngineModule (m : Name) : Bool := engineScope.any (·.isPrefixOf m)

def isKitModule (m : Name) : Bool :=
  kitLibrary.isPrefixOf m && m != kitLibrary && !kitTests.isPrefixOf m

def inScope (scope : Scope) (m : Name) : Bool :=
  match scope with
  | .v2 => isEngineModule m || isKitModule m
  | .gen => (`AvailableChainGeneric.Statements).isPrefixOf m &&
      m != `AvailableChainGeneric.Statements
  | .fgsa | .pcsa =>
      (familyPrefixes scope).any (·.isPrefixOf m) || (familyModules scope).contains m

/-- A module of the v2 libraries (tests included). -/
def isV2Module (m : Name) : Bool :=
  (`AvailableChainEngineV2).isPrefixOf m || kitLibrary.isPrefixOf m

def isScopeLibraryModule (scope : Scope) (m : Name) : Bool :=
  match scope with
  | .v2 => isV2Module m
  | .gen => (`AvailableChainGeneric).isPrefixOf m
  | .fgsa | .pcsa => (familyLibraries scope).any (·.isPrefixOf m)

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)

/-- Copy of `generated` in `scripts/CatalogLock.lean`. -/
def generated (n : Name) : CoreM Bool := do
  let env ← getEnv
  if n.isInternal || isAuxRecursor env n || isNoConfusion env n ||
      Meta.isMatcherCore env n || (env.find? n matches some (.recInfo _)) then
    return true
  if (← Meta.isEqnThm? n).isSome then return true
  return (← findDeclarationRangesCore? n).isNone

/-- Copy of `deps` in `scripts/CatalogLock.lean`. -/
def deps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo _ => ci.type.getUsedConstants
  | _ => ci.getUsedConstantsAsSet.toArray

/-- Every declaration that `n` reaches by `deps`, and `n` (the traversal of
`closure` in `scripts/CatalogLock.lean`). -/
def closure (env : Environment) (n : Name) : Except String (Array Name) := do
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert n
  let mut stack := #[n]
  let mut out := #[]
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    stack := stack.pop
    out := out.push m
    let some ci := env.find? m | throw s!"missing declaration: {m}"
    for d in deps ci do
      unless seen.contains d do
        seen := seen.insert d
        stack := stack.push d
  return out

/-- Copy of `kindTag` in `scripts/CatalogLock.lean`. -/
def kindTag : ConstantInfo → UInt64
  | .axiomInfo _ => 1 | .defnInfo _ => 2 | .thmInfo _ => 3 | .opaqueInfo _ => 4
  | .quotInfo _ => 5 | .inductInfo _ => 6 | .ctorInfo _ => 7 | .recInfo _ => 8

/-- `ownHash` of `scripts/CatalogLock.lean`, after the universe parameters
are renamed `u0`, `u1`, …. -/
def ownHash (ci : ConstantInfo) : UInt64 :=
  let us := (List.range ci.levelParams.length).map fun i => Level.param (.mkSimple s!"u{i}")
  let norm (e : Expr) := e.instantiateLevelParams ci.levelParams us
  let base := mixHash (mixHash (kindTag ci) (hash ci.name)) (hash (norm ci.type))
  match ci with
  | .defnInfo d => mixHash base (hash (norm d.value))
  | .opaqueInfo d => mixHash base (hash (norm d.value))
  | .inductInfo d => d.ctors.foldl (fun h c => mixHash h (hash c)) base
  | _ => base

def binderInfoTag : BinderInfo → UInt64
  | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

/-- The binder names and binder infos of `e`, in tree order (`Expr` hashes
ignore them). A hygienic name counts without its macro scopes: the scopes
depend on earlier declarations of the module with the same written name,
and a hygienic name cannot be a named argument. -/
partial def binderHash : Expr → UInt64
  | .forallE n t b bi | .lam n t b bi =>
      mixHash (mixHash (hash n.eraseMacroScopes) (binderInfoTag bi))
        (mixHash (binderHash t) (binderHash b))
  | .letE n t v b _ =>
      mixHash (hash n.eraseMacroScopes)
        (mixHash (binderHash t) (mixHash (binderHash v) (binderHash b)))
  | .app f a => mixHash (binderHash f) (binderHash a)
  | .mdata _ e | .proj _ _ e => binderHash e
  | _ => 11

def reducibilityTag : ReducibilityStatus → UInt64
  | .reducible => 1 | .semireducible => 2 | .irreducible => 3 | .implicitReducible => 4
  | .instanceReducible => 5

def hex (u : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 u.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The entry hash of `n` (module docstring). -/
def entryHex (scope : Scope) (n : Name) : CoreM String := do
  let env ← getEnv
  let some ci := env.find? n | throwError "missing declaration: {n}"
  let own ← match closure env n with
    | .ok xs => pure xs
    | .error e => throwError e
  let mn := moduleOf? env n
  let mut parts := #[n]
  for c in own do
    if c == n then continue
    let some m := moduleOf? env c | continue
    if (isScopeLibraryModule scope m || some m == mn) && (← generated c) then
      parts := parts.push c
  let mut h : UInt64 := 0
  for c in parts.qsort Name.lt do
    if let some cc := env.find? c then h := mixHash h (ownHash cc)
  h := mixHash h (binderHash ci.type)
  h := mixHash h (reducibilityTag (getReducibilityStatusCore env n))
  h := mixHash h (if Meta.isInstanceCore env n then 1 else 0)
  return hex h

def kindOf (env : Environment) : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
  | .inductInfo d => if isStructure env d.name then "structure" else "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- True projections and auxiliary parent projections, including Prop fields. -/
def fgsaField (env : Environment) (n : Name) : Bool :=
  env.isProjectionFn n || (env.getAuxParentProjectionInfo? n).isSome

/-- The FGSA entry exceptions do not change `generated` or `entryHex`. -/
def fgsaExplicit (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  !n.isInternal && !isPrivateName n &&
    (fgsaField env n || (ci matches .thmInfo _) && (toString n).endsWith "_def")

def scopeKind (scope : Scope) (env : Environment) (ci : ConstantInfo) : String :=
  if isFamily scope && fgsaField env ci.name then "field" else kindOf env ci

/-- The public declarations of the scope modules, per module, in source order
(line, column, then name). -/
def scan (scope : Scope) : CoreM (Std.HashMap Name (Array (Name × String))) := do
  let env ← getEnv
  let mut found : Std.HashMap Name (Array (Position × Name × String)) := {}
  if isFamily scope then
    for m in env.header.moduleNames do
      if inScope scope m then found := found.insert m #[]
  for (n, ci) in env.constants.toList do
    let some m := moduleOf? env n | continue
    unless inScope scope m do continue
    if ← generated n then
      unless isFamily scope && fgsaExplicit env n ci do continue
    let pos := (← findDeclarationRangesCore? n).map (·.range.pos) |>.getD ⟨0, 0⟩
    found := found.insert m ((found.getD m #[]).push (pos, n, scopeKind scope env ci))
  let lt (a b : Position × Name × String) : Bool :=
    a.1.line < b.1.line || (a.1.line == b.1.line &&
      (a.1.column < b.1.column || (a.1.column == b.1.column && Name.lt a.2.1 b.2.1)))
  return found.fold (init := {}) fun acc m xs =>
    acc.insert m ((xs.qsort lt).map fun (_, n, k) => (n, k))

/-- The union of the closures of the non-generated declarations of the
modules under `anchorPrefix`. -/
def anchored : CoreM (Std.HashSet Name) := do
  let env ← getEnv
  let mut out : Std.HashSet Name := {}
  for (n, _) in env.constants.toList do
    let some m := moduleOf? env n | continue
    unless anchorPrefix.isPrefixOf m do continue
    if ← generated n then continue
    match closure env n with
    | .ok xs => out := out.insertMany xs
    | .error e => throwError e
  return out

/-- The v2 engine modules first (`Engine`, `Conditions`, `Laws`), then the
Kit modules; by name within a group. Gen modules are sorted by name. -/
def sortedModules (s : Std.HashMap Name (Array (Name × String))) : Array Name :=
  let group (m : Name) : Nat := (engineScope.findIdx? (·.isPrefixOf m)).getD engineScope.length
  (s.toArray.map (·.1)).qsort fun a b =>
    group a < group b || (group a == group b && toString a < toString b)

/-- One manifest line: kind, name and hash (if any). -/
structure Line where
  kind : String
  name : Name
  hash? : Option String

/-- The manifest: per heading module, the lines in order. -/
def parseManifest (text : String) : Except String (Array (Name × Array Line)) := do
  let mut out : Array (Name × Array Line) := #[]
  let mut cur : Option Name := none
  let mut inBlock := false
  for line in text.splitOn "\n" do
    let l := line.trimAscii.toString
    if l.startsWith "```" then
      inBlock := !inBlock
      continue
    if inBlock then
      if l.isEmpty then continue
      if cur.isNone then continue
      let w := (l.splitOn " ").filter (!·.isEmpty)
      let n := (w.getD 1 "").toName
      unless (w.length == 2 || w.length == 3) && !n.isAnonymous do
        throw s!"malformed manifest line: {line}"
      out := out.modify (out.size - 1) fun (m, ls) => (m, ls.push ⟨w[0]!, n, w[2]?⟩)
    else if l.startsWith "### `" then
      let m := ((l.drop 5).takeWhile (· != '`')).toString.toName
      if (out.map (·.1)).contains m then throw s!"duplicate heading: {m}"
      out := out.push (m, #[])
      cur := some m
    else if l.startsWith "#" then
      cur := none
  return out

def runCore (env : Environment) (x : CoreM α) : IO α :=
  Core.CoreM.toIO' x { fileName := "V2Manifest", fileMap := .ofString "" } { env := env }

/-- `runCore`, with an error as a value. -/
def tryCore (env : Environment) (x : CoreM α) : IO (Except String α) :=
  try return .ok (← runCore env x) catch e => return .error (toString e)

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

/-- Load existing roots and all source modules of the scope, including facade orphans. -/
def familyImports (scope : Scope) : IO (Array Import) := do
  let mut roots : Std.HashSet Name := {}
  let libraries := (familyLibraries scope).map Name.toString
  let modules ← layoutOutput (#["modules"] ++ libraries)
  for text in modules do
    let m := text.toName
    if (familyLibraries scope).contains m || (familyModules scope).contains m ||
        (familyPrefixes scope).any (·.isPrefixOf m) then
      roots := roots.insert m
  return (roots.toArray.qsort Name.lt).map fun m => { module := m }

/-- The header of the PC-SA doc (not frozen; D15 only until a freeze). -/
def pcsaHeader : String :=
  "# PC-SA API manifest\n\n\
    _Statement manifest of the PC-SA claim surface (roadmap item 7). Not frozen._\n\n\
    This file lists every public declaration under the Statements prefixes of\n\
    `AvailableChainPCSA`, `AvailableChainPCSARun` and `AvailableChainPCSAClaims`,\n\
    under `AvailableChainPCSAClaims.Claims`, and in the claim facade\n\
    `AvailableChainPCSAClaims.PCSAClaims` (`PCSAClaims`, `PCSAStageTwoClaims`),\n\
    by fully qualified name and grouped by library and module. It uses the\n\
    FG-SA manifest rules (`docs/FGSA-API.md`). PC-SA has no anchor rule.\n\n\
    ## Update rule\n\n\
    The PC-SA claim surface is not frozen. A commit that adds, changes or removes\n\
    a declaration in this scope must write this doc again in the same commit, so\n\
    that the diff of this doc shows each statement change. The check fails when\n\
    this doc and the code differ. A freeze copies this doc to\n\
    `docs/PCSA-API-frozen.md` and records its SHA-256 in\n\
    `scripts/pcsa-manifest-frozen.sha256`. Then the FG-SA append-only rule\n\
    applies, with allow lines in `scripts/pcsa-manifest-allow.txt`.\n\n\
    ## How to check\n\n\
    `scripts/V2Manifest.lean` generates and checks this list.\n\n\
    - `lake env lean --run scripts/V2Manifest.lean --scope pcsa --list` prints\n\
      the module blocks from the environment, in source order, with hashes.\n\
    - `lake env lean --run scripts/V2Manifest.lean --scope pcsa --write` writes this doc.\n\
    - `lake env lean --run scripts/V2Manifest.lean --scope pcsa --check` checks\n\
      the names, modules, kinds, hashes and completeness (D15). A failed check\n\
      exits 1. A missing doc exits 2.\n\
    - `bash scripts/check-pcsa-manifest.sh` runs the check, then (when `NEG` is\n\
      not 0) checks that `--write` gives the same entry sections and runs negative\n\
      controls.\n\n\
    Each entry hash uses the shared hash rules in `scripts/V2Manifest.lean`:\n\
    types and definition values, generated or private helpers in the closure,\n\
    type binder names and infos, reducibility, and instance status. Theorem\n\
    proofs do not affect the hash. Public `_def` theorems are entries. Each public\n\
    structure projection is a separate `field` entry beside the structure entry.\n\n"

/-- A complete FGSA (or PC-SA) doc; each hash still belongs to one declaration. -/
def familyManifest (scope : Scope) (env : Environment)
    (decls : Std.HashMap Name (Array (Name × String))) : IO String := do
  let label := match scope with
    | .v2 => "V2" | .gen => "Generic" | .fgsa => "FG-SA" | .pcsa => "PC-SA"
  let total := decls.toArray.foldl (fun n (_, xs) => n + xs.size) 0
  let header := s!"# {label} API manifest\n\n" ++
    "_Current compiled snapshot. Policy: 2026-10-09._\n\n" ++
    "Run the writer after a source change and review the complete diff.\n" ++
    "The check requires all current names, modules, kinds and hashes.\n" ++
    "Theorem proof values are excluded. Snapshot updates do not approve claims.\n\n" ++
    s!"Entries: {total}; modules: {decls.size}.\n\n" ++
    "`lake env lean --run scripts/V2Manifest.lean --scope " ++
    (match scope with | .v2 => "v2" | .gen => "gen" | .fgsa => "fgsa" | .pcsa => "pcsa") ++
    " --write` updates this file; `--check` checks it.\n\n" ++
    (if scope == .v2 then
      "Engine entries require anchor coverage. Existing anchors can be updated.\n\n"
     else "")
  -- Preserve the existing PC-SA document and its writer header on this branch.
  let mut out := if scope == .pcsa then pcsaHeader else header
  let mods := sortedModules decls
  let libraries := if isFamily scope then familyLibraries scope else #[Name.anonymous]
  for lib in libraries do
    let ms := mods.filter (lib.isPrefixOf ·)
    if ms.isEmpty then continue
    if !lib.isAnonymous then out := out ++ s!"## `{lib}`\n\n"
    else out := out ++ "## Entries\n\n"
    for m in ms do
      out := out ++ s!"### `{m}`\n\n```text\n"
      for (n, k) in decls.getD m #[] do
        let h ← runCore env (entryHex scope n)
        out := out ++ s!"{k} {n} {h}\n"
      out := out ++ "```\n\n"
  return (out.dropEndWhile (· == '\n')).toString ++ "\n"

def familyLabel (scope : Scope) : String := if scope == .pcsa then "PC-SA" else "FGSA"

/-! FG-SA deep format v1. These rules are separate from the shallow manifest.
Names and kernel expressions use tagged, UTF-8 byte-length-prefixed fields.
Theorem values and expression metadata are excluded. No library/name filter is used.
SHA-256 node digests cover these bytes; root digests cover sorted name/digest pairs. -/
def deepPack (tag : String) (fields : Array String) : String :=
  s!"{tag}:{fields.size}:" ++ String.join (fields.toList.map fun s =>
    s!"{s.utf8ByteSize}:{s}")

partial def deepName : Name → String
  | .anonymous => deepPack "anonymous" #[]
  | .str p s => deepPack "str" #[deepName p, s]
  | .num p n => deepPack "num" #[deepName p, toString n]

partial def deepLevel : Level → String
  | .zero => deepPack "zero" #[]
  | .succ l => deepPack "succ" #[deepLevel l]
  | .max a b => deepPack "max" #[deepLevel a, deepLevel b]
  | .imax a b => deepPack "imax" #[deepLevel a, deepLevel b]
  | .param n => deepPack "param" #[deepName n]
  | .mvar n => deepPack "mvar" #[deepName n.name]

partial def deepExpr : Expr → String
  | .bvar i => deepPack "bvar" #[toString i]
  | .fvar n => deepPack "fvar" #[deepName n.name]
  | .mvar n => deepPack "mvar" #[deepName n.name]
  | .sort l => deepPack "sort" #[deepLevel l]
  | .const n ls => deepPack "const" #[deepName n, deepPack "levels" (ls.toArray.map deepLevel)]
  | .app f a => deepPack "app" #[deepExpr f, deepExpr a]
  | .lam n t b bi => deepPack "lam"
      #[deepName n.eraseMacroScopes, toString (binderInfoTag bi), deepExpr t, deepExpr b]
  | .forallE n t b bi => deepPack "forall"
      #[deepName n.eraseMacroScopes, toString (binderInfoTag bi), deepExpr t, deepExpr b]
  | .letE n t v b nd => deepPack "let"
      #[deepName n.eraseMacroScopes, deepExpr t, deepExpr v, deepExpr b, toString nd]
  | .lit (.natVal n) => deepPack "nat" #[toString n]
  | .lit (.strVal s) => deepPack "string" #[s]
  | .mdata _ e => deepExpr e
  | .proj n i e => deepPack "proj" #[deepName n, toString i, deepExpr e]

/-- Extend `deps` with all constructor and recursor data. Never traverse theorem values. -/
def deepDeps (ci : ConstantInfo) : Array Name :=
  let extra := match ci with
    | .inductInfo d => (d.all ++ d.ctors).toArray
    | .ctorInfo d => #[d.induct]
    | .recInfo d => d.all.toArray ++ d.rules.toArray.flatMap fun r =>
        #[r.ctor] ++ r.rhs.getUsedConstants
    | _ => #[]
  (({} : Std.HashSet Name).insertMany (deps ci ++ extra)).toArray.qsort Name.lt

def deepClosure (env : Environment) (n : Name)
    (edges : Std.HashMap Name (Array Name) := {}) : Except String (Array Name) := do
  let mut seen : Std.HashSet Name := {}
  let mut stack := #[n]
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    stack := stack.pop
    if seen.contains m then continue
    seen := seen.insert m
    let some ci := env.find? m | throw s!"missing deep dependency: {m}"
    stack := stack ++ (match edges[m]? with | some ds => ds | none => deepDeps ci)
  return seen.toArray.qsort Name.lt

/-- Full node bytes, not a rendering or a 64-bit Expr hash. -/
def deepNodeBytes (env : Environment) (ci : ConstantInfo) : String := Id.run do
  let us := (List.range ci.levelParams.length).map fun i => Level.param (.mkSimple s!"u{i}")
  let expr (e : Expr) := deepExpr (e.instantiateLevelParams ci.levelParams us)
  let names (ns : List Name) := deepPack "names" (ns.toArray.map deepName)
  let data := match ci with
    | .defnInfo d =>
      let hints := match d.hints with
        | .opaque => deepPack "opaque" #[] | .abbrev => deepPack "abbrev" #[]
        | .regular h => deepPack "regular" #[toString h]
      deepPack "definition" #[expr d.value, hints, (match d.safety with
          | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial")]
    | .opaqueInfo d => deepPack "opaque" #[expr d.value, toString d.isUnsafe]
    | .inductInfo d => deepPack "inductive" #[names d.all, names d.ctors,
        toString d.numParams, toString d.numIndices, toString d.numNested,
        toString d.isRec, toString d.isUnsafe, toString d.isReflexive]
    | .ctorInfo d => deepPack "constructor" #[deepName d.induct, toString d.cidx,
        toString d.numParams, toString d.numFields, toString d.isUnsafe]
    | .recInfo d => deepPack "recursor" #[names d.all, toString d.numParams,
        toString d.numIndices, toString d.numMotives, toString d.numMinors,
        toString d.k, toString d.isUnsafe, deepPack "rules" (d.rules.toArray.map fun r =>
          deepPack "rule" #[deepName r.ctor, toString r.nfields, expr r.rhs])]
    | .axiomInfo d => deepPack "axiom" #[toString d.isUnsafe]
    | .quotInfo d => deepPack "quotient" #[match d.kind with
        | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"]
    | .thmInfo _ => deepPack "theorem" #[]
  return deepPack "fgsa-deep-node-v1" #[deepName ci.name, toString (kindTag ci),
    toString ci.levelParams.length, expr ci.type, data,
    toString (reducibilityTag (getReducibilityStatusCore env ci.name)),
    toString (Meta.isInstanceCore env ci.name),
    deepPack "dependencies" ((deepDeps ci).map deepName)]

/-- SHA-256 of the full statement closure, in Name.lt order. Node SHA-256 values
cover the versioned kernel bytes above, including public/private/library data. -/
def deepEntryDigest (env : Environment) (n : Name) (nodes : Std.HashMap Name String)
    (hashBytes : String → IO String)
    (edges : Std.HashMap Name (Array Name) := {}) : IO String := do
  let ns ← IO.ofExcept (deepClosure env n edges)
  let parts ← ns.mapM fun d => do
    let some digest := nodes[d]? | throw (IO.userError s!"missing deep node digest: {d}")
    pure (deepPack "dependency" #[deepName d, digest])
  hashBytes (deepPack "fgsa-deep-entry-v1" parts)

/-- One Python SHA-256 worker avoids starting a process for each dependency. -/
def withDeepHasher (f : (String → IO String) → IO α) : IO α := do
  let child ← IO.Process.spawn {
    cmd := "python3"
    args := #["-u", "-c",
      "import hashlib,json,sys\n" ++
      "for line in sys.stdin:\n" ++
      " if line == 'STOP\\n': break\n" ++
      " print(hashlib.sha256(json.loads(line).encode('utf-8')).hexdigest(), flush=True)"]
    stdin := .piped
    stdout := .piped }
  let reaped ← IO.mkRef false
  try
    let result ← f fun bytes => do
      child.stdin.putStrLn (toJson bytes).compress
      child.stdin.flush
      let digest := (← child.stdout.getLine).trimAscii.toString
      unless digest.length == 64 && digest.toList.all (fun c =>
          c.isDigit || ('a' ≤ c && c ≤ 'f')) do
        throw (IO.userError "deep SHA-256 worker returned an invalid digest")
      return digest
    child.stdin.putStrLn "STOP"
    child.stdin.flush
    let code ← child.wait
    reaped.set true
    unless code == 0 do throw (IO.userError "deep SHA-256 worker failed")
    return result
  finally
    unless ← reaped.get do
      try child.kill catch _ => pure ()
      try discard child.wait catch _ => pure ()

/-- The shared node table and per-root node IDs retain dependency digests without
repeating long names. Both tables use Name.lt order. -/
def deepSnapshot (env : Environment) (roots : Array Name) : IO Json := withDeepHasher fun hashBytes => do
  let roots := roots.qsort Name.lt
  let mut edges : Std.HashMap Name (Array Name) := {}
  let mut stack := roots
  while h : stack.size > 0 do
    let n := stack[stack.size - 1]
    stack := stack.pop
    if edges.contains n then continue
    let some ci := env.find? n | throw (IO.userError s!"missing deep dependency: {n}")
    let ds := deepDeps ci
    edges := edges.insert n ds
    stack := stack ++ ds
  let names := (edges.toArray.map (·.1)).qsort Name.lt
  IO.eprintln s!"DEEP snapshot: {roots.size} roots; {names.size} dependency nodes"
  let mut digests : Std.HashMap Name String := {}
  let mut nodes : Array (String × Json) := #[]
  for n in names do
    let some ci := env.find? n | throw (IO.userError s!"missing deep dependency: {n}")
    let digest ← hashBytes (deepNodeBytes env ci)
    digests := digests.insert n digest
    let m := (moduleOf? env n).map Name.toString |>.getD "<kernel>"
    let project := m.startsWith "AvailableChain"
    let readable ← if project then runCore env (withOptions
        (fun o => o.setBool `pp.deepTerms true |>.set `pp.maxSteps (1000000 : Nat)) do
        let type ← Meta.MetaM.run' do return (← Meta.ppExpr ci.type).pretty 88
        let body ← match ci with
          | .defnInfo d => Meta.MetaM.run' do return (← Meta.ppExpr d.value).pretty 88
          | .opaqueInfo d => Meta.MetaM.run' do return (← Meta.ppExpr d.value).pretty 88
          | _ => pure ""
        pure (type, body))
      else pure ("", "")
    nodes := nodes.push (n.toString, Json.mkObj [("digest", toJson digest),
      ("kernel_name", toJson (deepName n)),
      ("module", toJson m), ("kind", toJson (scopeKind .fgsa env ci)),
      ("type", toJson (readable.1.splitOn "\n")),
      ("body", toJson (readable.2.splitOn "\n")),
      ("dependencies", toJson ((deepDeps ci).map Name.toString))])
  let mut entries : Array (String × Json) := #[]
  for n in roots do
    let digest ← deepEntryDigest env n digests hashBytes edges
    let some ci := env.find? n | throw (IO.userError s!"missing root: {n}")
    entries := entries.push (n.toString, Json.mkObj [("digest", toJson digest),
      ("module", toJson ((moduleOf? env n).map Name.toString |>.getD "<kernel>")),
      ("kind", toJson (scopeKind .fgsa env ci))])
  return Json.mkObj [("format_version", toJson (2 : Nat)), ("entries", Json.mkObj entries.toList),
    ("node_order", toJson (names.map Name.toString)), ("nodes", Json.mkObj nodes.toList)]

/-- The Python side validates and stores the current compiled snapshot. -/
def runDeep (scope : Scope) (mode : String) (manifest snapshotPath : System.FilePath)
    (rootsPath? reportPath? : Option System.FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (← familyImports scope) {}
  let decls ← runCore env (scan scope)
  let roots := decls.toArray.flatMap fun (_, xs) => xs.map (·.1)
  if roots.isEmpty then throw (IO.userError "no deep roots: missing declaration ranges/build")
  let snapshot ← deepSnapshot env roots
  IO.FS.withTempFile fun handle path => do
    handle.putStrLn snapshot.compress
    handle.flush
    let extra := (rootsPath?.map (fun p => #["--roots", p.toString])).getD #[] ++
      (reportPath?.map (fun p => #["--output", p.toString])).getD #[]
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/fgsa-deep.py", mode,
      "--snapshot", path.toString, "--manifest", manifest.toString,
      "--baseline", snapshotPath.toString] ++ extra }
    child.wait

structure Opts where
  mode : String := ""
  scope : Scope := .v2
  scopeGiven : Bool := false
  deep : Bool := false
  manifest? : Option System.FilePath := none
  snapshot? : Option System.FilePath := none
  roots? : Option System.FilePath := none
  report? : Option System.FilePath := none

def parseArgs : List String → Opts → Option Opts
  | [], o => if o.mode.isEmpty then none else some o
  | "--deep" :: r, o =>
      if o.deep then none else parseArgs r { o with deep := true }
  | "--scope" :: s :: r, o =>
      if o.scopeGiven then none else
      match s with
      | "v2" => parseArgs r { o with scope := .v2, scopeGiven := true }
      | "gen" => parseArgs r { o with scope := .gen, scopeGiven := true }
      | "fgsa" => parseArgs r { o with scope := .fgsa, scopeGiven := true }
      | "pcsa" => parseArgs r { o with scope := .pcsa, scopeGiven := true }
      | _ => none
  | "--manifest" :: p :: r, o =>
      if o.manifest?.isSome then none else parseArgs r { o with manifest? := some p }
  | "--roots" :: p :: r, o =>
      if o.roots?.isSome then none else parseArgs r { o with roots? := some p }
  | "--report" :: p :: r, o =>
      if o.report?.isSome then none else parseArgs r { o with report? := some p }
  | "--snapshot" :: p :: r, o =>
      if o.snapshot?.isSome then none else parseArgs r { o with snapshot? := some p }
  | m :: r, o =>
      if o.mode.isEmpty &&
          ["--list", "--anchor", "--check", "--write"].contains m then
        parseArgs r { o with mode := m }
      else none

def main (args : List String) : IO UInt32 := do
  let some o := parseArgs args {} | do
    IO.eprintln "usage: V2Manifest [--scope (v2 | gen | fgsa | pcsa)] \
      (--list | --anchor | --check | --write) [--deep] [--manifest <path>] [--snapshot <path>]"
    return 2
  if o.scope != .v2 && o.mode == "--anchor" then
    IO.eprintln "usage error: --anchor requires --scope v2"
    return 2
  if (o.roots?.isSome || o.report?.isSome) && (!o.deep || o.mode != "--check") then
    IO.eprintln "usage error: --roots and --report require --deep --check"
    return 2
  let unported := (← IO.FS.lines "scripts/unported-libraries.txt").filterMap fun line =>
    let name := (line.splitOn "#").head!.trimAscii.toString
    if name.isEmpty then none else some name
  if o.scope == .pcsa && unported.contains "AvailableChainPCSA" then
    IO.println "SKIP UNPORTED: PC-SA manifest and deep snapshot"
    return 0
  if o.deep then
    unless isFamily o.scope && ["--write", "--check"].contains o.mode do
      IO.eprintln "usage error: --deep requires --scope fgsa or pcsa and --write or --check"
      return 2
    try
      return ← runDeep o.scope o.mode
        (o.manifest?.getD (if o.scope == .pcsa then "docs/internal/PCSA-API.md"
          else "docs/internal/FGSA-API.md"))
        (o.snapshot?.getD (if o.scope == .pcsa then "docs/internal/api/pcsa-deep.json"
          else "docs/internal/api/fgsa-deep.json")) o.roots? o.report?
    catch e => IO.eprintln s!"DEEP FAIL: {e}"; return 1
  let mode := o.mode
  let manifest := o.manifest?.getD (match o.scope with
    | .v2 => "docs/internal/V2-API.md" | .gen => "docs/internal/GEN-API.md"
    | .fgsa => "docs/internal/FGSA-API.md"
    | .pcsa => "docs/internal/PCSA-API.md")
  if mode == "--check" && !(← manifest.pathExists) then
    IO.eprintln s!"cannot read {manifest}: it does not exist"
    return 2
  initSearchPath (← findSysroot)
  let imports ← match o.scope with
    | .v2 => pure #[{ module := `AvailableChainFramework },
        { module := `AvailableChainEngineV2 }, { module := `AvailableChainKitV2 }]
    | .gen => pure #[{ module := `AvailableChainGeneric }]
    | .fgsa | .pcsa => familyImports o.scope
  let env ← importModules imports {}
  if isFamily o.scope then
    let hasRanges ← runCore env do
      for (n, _) in env.constants.toList do
        if let some m := moduleOf? env n then
          if inScope o.scope m && (← findDeclarationRangesCore? n).isSome then return true
      return false
    unless hasRanges do
      IO.eprintln s!"no {familyLabel o.scope} declaration ranges: \
        the .olean.server data is missing or the scope is empty"
      return 2
  else
    let probe := if o.scope == .v2 then rangeProbe else `AvailableChain.Gen.Pure.qF
    if (← runCore env (findDeclarationRangesCore? probe)).isNone then
      IO.eprintln s!"no declaration range for {probe}: the .olean.server data is missing"
      return 2
  let decls ← runCore env (scan o.scope)
  let mods := sortedModules decls
  if mode == "--write" then
    try
      IO.FS.writeFile manifest (← familyManifest o.scope env decls)
    catch e => IO.eprintln s!"cannot write {manifest}: {e}"; return 2
    IO.println s!"{manifest}: written; {mods.size} modules"
    return 0
  if mode == "--list" then
    for m in mods do
      IO.println s!"### `{m}`\n"
      IO.println "```text"
      for (n, k) in decls.getD m #[] do
        match ← tryCore env (entryHex o.scope n) with
        | .ok h => IO.println s!"{k} {n} {h}"
        | .error e => IO.eprintln e; return 2
      IO.println "```\n"
    return 0
  let covered : Std.HashSet Name ← if o.scope == .v2 then
      match ← tryCore env anchored with
      | .ok s => pure s
      | .error e => IO.eprintln e; return 2
    else pure {}
  if mode == "--anchor" then
    let mut any := false
    for m in mods.filter isEngineModule do
      let todo := (decls.getD m #[]).filter (!covered.contains ·.1)
      unless todo.isEmpty do
        IO.println s!"  -- {m}"
        for (n, _) in todo do IO.println s!"  let _ := @{n}"
        any := true
    if any then IO.println "  ()" else IO.println "-- every engine declaration is anchored"
    return 0
  let text ← match ← (IO.FS.readFile manifest).toBaseIO with
    | .ok s => pure s
    | .error e => IO.eprintln s!"cannot read {manifest}: {e}"; return 2
  let entries ← match parseManifest text with
    | .ok x => pure x
    | .error e => IO.eprintln e; return 2
  let mut fails : Array String := #[]
  if o.scope == .v2 then
    match env.find? anchorName, moduleOf? env anchorName with
    | some _, some m =>
        if m != anchorModule then fails := fails.push s!"ANCHOR IN WRONG MODULE {m}"
    | _, _ => fails := fails.push s!"MISSING ANCHOR {anchorName}"
  let headings := entries.map (·.1)
  let mut listed : Std.HashSet Name := {}
  let mut count := 0
  for (m, ls) in entries do
    for l in ls do
      let n := l.name
      count := count + 1
      if listed.contains n then fails := fails.push s!"DUPLICATE ENTRY {n}"
      listed := listed.insert n
      if !(decls.getD m #[]).any (·.1 == n) then
        fails := fails.push s!"EXTRA ENTRY {n} (heading {m})"
      match env.find? n, moduleOf? env n with
      | some ci, some m' =>
          if m' != m then fails := fails.push s!"WRONG MODULE {n}: {m'}, heading {m}"
          if l.kind != scopeKind o.scope env ci then
            fails := fails.push s!"WRONG KIND {n}: {l.kind}, is {scopeKind o.scope env ci}"
          if o.scope == .v2 && isEngineModule m' && !covered.contains n then
            fails := fails.push s!"NOT ANCHORED {n}"
          match l.hash?, ← tryCore env (entryHex o.scope n) with
          | _, .error e => IO.eprintln e; return 2
          | none, _ => fails := fails.push s!"NO HASH {n}"
          | some h, .ok h' => if h != h' then fails := fails.push s!"CHANGED {n} {h} -> {h'}"
      | _, _ => fails := fails.push s!"UNKNOWN {n} (heading {m})"
  for m in mods do
    unless headings.contains m do fails := fails.push s!"NO HEADING {m}"
  for m in headings do
    unless inScope o.scope m do fails := fails.push s!"OUT OF SCOPE HEADING {m}"
    for (n, _) in decls.getD m #[] do
      unless listed.contains n do fails := fails.push s!"NOT LISTED {n}"
  for f in fails do IO.println f
  unless fails.isEmpty do return 1
  if o.scope == .v2 then
    IO.println s!"{manifest}: {count} entries in {headings.size} modules; \
      complete; engine entries anchored; hashes match"
  else
    IO.println s!"{manifest}: {count} entries in {headings.size} modules; complete; hashes match"
  return 0
