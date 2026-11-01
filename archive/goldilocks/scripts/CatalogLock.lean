import AvailableChainFramework
import Lean.Util.CollectAxioms
import Lean.Meta.Eqns
import Lean.Meta.Match.MatcherInfo
open Lean

/-! Catalog lock. Each locked declaration gets a hash of its own statement
(and body, for a definition) and of every declaration that it uses,
transitively. `docs/catalog.lock` has one line `<name> <16 hex digits>` per
locked declaration, sorted by name.

The hash of a line depends only on the set of declarations that its root
reaches (the closure), not on the traversal order or on the other roots. Thus
a new declaration does not change the line of an old declaration that does
not reach it.

The lock is a tripwire, not a commitment. `Expr` hashes have 32 bits per node
and ignore binder names, binder info and metadata, so two different
declarations can have one hash. A kernel check, not the lock, makes a proof
valid.

A declaration is locked if its module is locked and Lean did not generate it,
or if its type (after `whnfR`, so that an `abbrev` alias counts) is a claim, a
profile, a profile entry, a claim domain or a domain map and its module is in
`AvailableChainFramework`. "Generated" comes from
environment metadata, never from a name suffix. A generated declaration has no
line, but its hash enters every closure that reaches it.

Separately from the hash, the script checks the axioms of every locked
declaration, proofs included, that no two claims have the same `id`, and that
no two profiles have the same `id`. A pulled claim (`ClaimSpec.pull …`) keeps the id of its base claim and is
exempt. Thus two pulls of one base claim along one map are not found by this
check (by design).

Run: `lake env lean --run scripts/CatalogLock.lean
  (--check | --write) [--local] [--lock <path>]`.
The lock file is `docs/catalog.lock` if `--lock` is not given.
`--local` makes the local-closure lock: the closure stops at a constant of
a module outside the project (core, Std, Mathlib, …), and such a constant
is hashed by its name only. The local lock does not change when a
toolchain or Mathlib bump changes a foreign definition, so it shows that
no project declaration changed. `--local` needs `--lock`; it never uses
`docs/catalog.lock`. Bump procedure: on the old toolchain, `--write
--local --lock <file>`; on the new one, `--check --local --lock <file>`
(it must be clean); then `--write` of the full lock, with
a lock-log entry (design §8; example: `docs/lock-log/v4.34.1/`).
`--check` compares by name. It prints `REMOVED <name>` for an old name that is
not locked now, `CHANGED <name> <old> -> <new>` for a different hash, and
`ADDED <name>` for a new name.
`--write` replaces the current lock after all semantic checks. Review its diff.
Exit codes: 0 same, or an explicit write; 1 any snapshot difference; 2 a usage error, a
malformed lock line, a missing declaration in a closure, a bad axiom, two
claims with one id, two profiles with one id, a claim or profile id that
cannot be read, or no declaration ranges. -/

/-- The library that the lock scans. -/
def frameworkLibrary : Name := `AvailableChainFramework

/-- Every declaration of these modules is locked (L1–L3). The LM/L0
definitions that they use are reached through the closure. `Kit` (L5) is
not locked. A module in the list that does not exist is ignored. -/
def lockedModules : List Name :=
  [`AvailableChainFramework.Hooks, `AvailableChainFramework.Instance,
   `AvailableChainFramework.Claim, `AvailableChainFramework.Cert,
   `AvailableChainFramework.Profile, `AvailableChainFramework.Pareto,
   `AvailableChainFramework.ClaimDomain, `AvailableChainFramework.DomainMap]

/-- Every declaration of the modules under these prefixes is locked (L2, L3,
and the engine v2 anchor, whose closure holds the frozen v2 engine API). -/
def lockedModulePrefixes : List Name :=
  [`AvailableChainFramework.Catalog, `AvailableChainFramework.Facets,
   `AvailableChainFramework.V2]

/-- A declaration whose type is an application of one of these is always
locked. Names that do not exist yet are ignored. -/
def claimTypes : List Name :=
  [`AvailableChain.Framework.ClaimSpec, `AvailableChain.Framework.Profile,
   `AvailableChain.Framework.Profile.Entry, `AvailableChain.Framework.ClaimDomain,
   `AvailableChain.Framework.DomainMap]

def claimSpecName : Name := `AvailableChain.Framework.ClaimSpec
def claimIdName : Name := `AvailableChain.Framework.ClaimSpec.id
def profileName : Name := `AvailableChain.Framework.Profile
def profileIdName : Name := `AvailableChain.Framework.Profile.id
/-- A pulled claim keeps the id of its base claim. -/
def pullName : Name := `AvailableChain.Framework.ClaimSpec.pull

/-- Axioms that a locked declaration can use. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)

def lockedModule (m : Name) : Bool :=
  lockedModules.contains m || lockedModulePrefixes.any (·.isPrefixOf m)

/-- The head constant of the type of `ci`, after `whnfR`. -/
def typeHead? (ci : ConstantInfo) : MetaM (Option Name) :=
  return (← Meta.whnfR ci.type).getAppFn.constName?

/-- The type of `ci` is `C …` for a `C` in `claimTypes`. -/
def claimLike (ci : ConstantInfo) : MetaM Bool :=
  return (← typeHead? ci).any claimTypes.contains

/-- Lean generated `n`: an internal name, an auxiliary recursor, a
`noConfusion`, a matcher, a recursor, an equation lemma, or no declaration
range. `isEqnThm?` knows only the equation lemmas of the current file; for an
imported declaration, the missing declaration range finds them. -/
def generated (n : Name) : CoreM Bool := do
  let env ← getEnv
  if n.isInternal || isAuxRecursor env n || isNoConfusion env n ||
      Meta.isMatcherCore env n || (env.find? n matches some (.recInfo _)) then
    return true
  if (← Meta.isEqnThm? n).isSome then return true
  return (← findDeclarationRangesCore? n).isNone

def locked (n : Name) (ci : ConstantInfo) : MetaM Bool := do
  let some m := moduleOf? (← getEnv) n | return false
  unless frameworkLibrary.isPrefixOf m do return false
  if ← claimLike ci then return true
  return lockedModule m && !(← generated n)

/-- A tag for each kind of constant, so that (for example) a definition and an
opaque with the same type and value have different hashes. -/
def kindTag : ConstantInfo → UInt64
  | .axiomInfo _ => 1 | .defnInfo _ => 2 | .thmInfo _ => 3 | .opaqueInfo _ => 4
  | .quotInfo _ => 5 | .inductInfo _ => 6 | .ctorInfo _ => 7 | .recInfo _ => 8

def ownHash (ci : ConstantInfo) : UInt64 :=
  let base := mixHash (mixHash (kindTag ci) (hash ci.name)) (hash ci.type)
  match ci with
  | .defnInfo d => mixHash base (hash d.value)
  | .opaqueInfo d => mixHash base (hash d.value)
  | .inductInfo d => d.ctors.foldl (fun h c => mixHash h (hash c)) base
  | _ => base  -- theorems: the statement only; a new proof keeps the hash

/-- The declarations that `ci` uses. A theorem uses only the constants of its
statement, so that a new proof keeps the hash. For an inductive,
`getUsedConstantsAsSet` also gives its constructors. -/
def deps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo _ => ci.type.getUsedConstants
  | _ => ci.getUsedConstantsAsSet.toArray

/-- A constant of a module outside the project (core, Std, Mathlib, …). -/
def foreign (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => !(m.getRoot.toString.startsWith "AvailableChain")
  | none => false

/-- The cached own hash and dependencies of a declaration. -/
structure Node where
  own : UInt64
  deps : Array Name

/-- The cache holds only per-declaration data, never a closure hash. -/
abbrev HashM := StateT (Std.HashMap Name Node) (Except String)

/-- With `loc` (`--local`), a foreign constant is a leaf hashed by name. -/
def node (env : Environment) (n : Name) (loc : Bool := false) : HashM Node := do
  if let some x := (← get)[n]? then return x
  let some ci := env.find? n | throw s!"missing declaration: {n}"
  let x : Node := if loc && foreign env n then { own := mixHash 99 (hash n), deps := #[] }
    else { own := ownHash ci, deps := deps ci }
  modify (·.insert n x)
  return x

/-- Every declaration that `n` reaches by `deps`, and `n`. -/
def closure (env : Environment) (n : Name) (loc : Bool := false) : HashM (Array Name) := do
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert n
  let mut stack := #[n]
  let mut out := #[]
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    stack := stack.pop
    out := out.push m
    for d in (← node env m loc).deps do
      unless seen.contains d do
        seen := seen.insert d
        stack := stack.push d
  return out

/-- The fold of `mixHash` over the own hashes of the closure, in `Name.lt`
order. -/
def lockHash (env : Environment) (n : Name) (loc : Bool := false) : HashM UInt64 := do
  let mut h : UInt64 := 0
  for m in (← closure env n loc).qsort Name.lt do
    h := mixHash h (← node env m loc).own
  return h

def hex (u : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 u.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- The `Name` that a closed, reduced expression of type `Name` denotes. -/
partial def nameOfExpr? (e : Expr) : Option Name :=
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Name.anonymous, #[] => some .anonymous
  | some ``Name.str, #[p, .lit (.strVal s)] => (nameOfExpr? p).map (·.str s)
  | some ``Name.num, #[p, .lit (.natVal k)] => (nameOfExpr? p).map (·.num k)
  | _, _ => none

/-- The value of the `id` projection `idProj` at `n`, as a literal name. -/
def readId (idProj n : Name) (ci : ConstantInfo) : MetaM Name := do
  let e ← Meta.mkAppM idProj #[mkConst n (ci.levelParams.map mkLevelParam)]
  let r ← instantiateMVars (← Meta.reduce e)
  match nameOfExpr? r with
  | some id => return id
  | none => throwError "the id does not reduce to a literal name: {r}"

/-- The `id` of a claim `n`, or `none` for a pulled claim. -/
def claimId? (n : Name) (ci : ConstantInfo) : MetaM (Option Name) := do
  if let some v := ci.value? then
    if v.getAppFn.constName? == some pullName then return none
  return some (← readId claimIdName n ci)

/-- The locked names (sorted), and the problems that force exit 2. -/
def scan : MetaM (Array Name × Array String) := do
  let env ← getEnv
  if (← findDeclarationRangesCore? claimSpecName).isNone then
    return (#[], #[s!"no declaration range for {claimSpecName}: the .olean.server data is missing"])
  let mut found := #[]
  for (n, ci) in env.constants.toList do
    if ← locked n ci then found := found.push n
  let names := found.qsort Name.lt
  let mut problems := #[]
  let mut ids : Std.HashMap Name Name := {}
  let mut profileIds : Std.HashMap Name Name := {}
  for n in names do
    let axs ← collectAxioms n
    let bad := (axs.filter (!allowedAxioms.contains ·)).qsort Name.lt
    unless bad.isEmpty do
      problems := problems.push s!"BAD AXIOMS {n}: {bad.toList}"
    let some ci := env.find? n | continue
    if (← typeHead? ci) == some claimSpecName then
      -- An error here (for example an id that does not reduce) is a problem
      -- with exit 2, not an uncaught exception with exit 1.
      let r : Except String (Option Name) ← try Except.ok <$> claimId? n ci
        catch e => pure (Except.error s!"UNREADABLE ID {n}: {← e.toMessageData.toString}")
      match r with
      | .error msg => problems := problems.push msg
      | .ok (some id) =>
          if let some other := ids[id]? then
            problems := problems.push s!"DUPLICATE ID {id}: {other} and {n}"
          else
            ids := ids.insert id n
      | .ok none => pure ()
    if (← typeHead? ci) == some profileName then
      let r : Except String Name ← try Except.ok <$> readId profileIdName n ci
        catch e => pure (Except.error s!"UNREADABLE PROFILE ID {n}: {← e.toMessageData.toString}")
      match r with
      | .error msg => problems := problems.push msg
      | .ok id =>
          if let some other := profileIds[id]? then
            problems := problems.push s!"DUPLICATE PROFILE ID {id}: {other} and {n}"
          else
            profileIds := profileIds.insert id n
  return (names, problems)

/-- The lines `(name, hash)` of a lock file. Blank lines are ignored. -/
def parseLock (text : String) : Except String (Array (String × String)) := do
  let mut out := #[]
  let mut seen : Std.HashSet String := {}
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    let parts := line.splitOn " "
    let h := parts.getLast!
    let n := String.intercalate " " parts.dropLast
    unless parts.length ≥ 2 && !n.isEmpty && h.length == 16 &&
        h.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      throw s!"malformed lock line: {line}"
    if seen.contains n then throw s!"duplicate lock line: {n}"
    seen := seen.insert n
    out := out.push (n, h)
  return out

/-- The `REMOVED`, `CHANGED` and `ADDED` lines, sorted by name, and whether
there is a `REMOVED` or `CHANGED` line. -/
def diff (old new : Array (String × String)) : Array String × Bool := Id.run do
  let oldMap : Std.HashMap String String := Std.HashMap.ofList old.toList
  let newMap : Std.HashMap String String := Std.HashMap.ofList new.toList
  let mut out : Array (String × String) := #[]
  let mut breaking := false
  for (n, h) in old do
    match newMap[n]? with
    | none => out := out.push (n, s!"REMOVED {n}"); breaking := true
    | some h' =>
        if h != h' then
          out := out.push (n, s!"CHANGED {n} {h} -> {h'}"); breaking := true
  for (n, _) in new do
    unless oldMap.contains n do out := out.push (n, s!"ADDED {n}")
  return ((out.qsort (fun a b => a.1 < b.1)).map (·.2), breaking)

structure Opts where
  mode : String := ""
  loc : Bool := false
  lockGiven : Bool := false
  lock : System.FilePath := "docs/internal/catalog.lock"

def parseArgs : List String → Opts → Option Opts
  | [], o => if o.mode.isEmpty || (o.loc && !o.lockGiven) then none else some o
  | "--check" :: r, o => if o.mode.isEmpty then parseArgs r { o with mode := "check" } else none
  | "--write" :: r, o => if o.mode.isEmpty then parseArgs r { o with mode := "write" } else none
  | "--local" :: r, o => parseArgs r { o with loc := true }
  | "--lock" :: p :: r, o => parseArgs r { o with lock := p, lockGiven := true }
  | _, _ => none

def main (args : List String) : IO UInt32 := do
  let some o := parseArgs args {} | do
    IO.eprintln "usage: lake env lean --run scripts/CatalogLock.lean \
      (--check | --write) [--local] [--lock <path>]"
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := frameworkLibrary }] {}
  let (names, problems) ← Core.CoreM.toIO' (scan.run' {} {})
    { fileName := "CatalogLock", fileMap := .ofString "" } { env := env }
  unless problems.isEmpty do
    for p in problems do IO.eprintln p
    return 2
  let hashes := names.mapM (fun n => return (toString n, hex (← lockHash env n o.loc)))
  let new ← match hashes.run' {} with
    | .ok x => pure x
    | .error e => IO.eprintln e; return 2
  let text := String.intercalate "\n" (new.toList.map fun (n, h) => s!"{n} {h}") ++ "\n"
  if o.mode == "write" then
    IO.FS.writeFile o.lock text
    IO.println s!"wrote {o.lock}: {new.size} lines"
    return 0
  let old? ← match ← (IO.FS.readFile o.lock).toBaseIO with
    | .ok s => pure (some s)
    | .error e =>
        if o.mode == "check" then
          IO.eprintln s!"cannot read {o.lock}: {e}"
          return (2 : UInt32)
        pure none
  let old ← match (old?.map parseLock).getD (.ok #[]) with
    | .ok x => pure x
    | .error e => IO.eprintln e; return 2
  let (report, _) := diff old new
  for l in report do IO.println l
  unless report.isEmpty do
    IO.eprintln s!"{o.lock} differs: run --write and review the diff"
    return 1
  IO.println s!"{o.lock}: current snapshot matches"
  return 0
