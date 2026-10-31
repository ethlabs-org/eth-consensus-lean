/- Persisted Spec surface only; imports never execute checked-module initializers.
   Snapshot headers (pins/options) are supplied by check.sh. -/
import Lean
open Lean Meta
namespace SpecSurface

def runMeta {α : Type} (env : Environment) (x : MetaM α) : IO α := do
  let opts := (((({} : Options).setBool `pp.fullNames true).setBool `pp.universes true).setBool `pp.proofs false).set `pp.width (120 : Nat)
  (x.run' {} {}).toIO' { fileName := "SpecSurface", fileMap := default, options := opts } { env }

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "recursor"

def flat (s : String) : String :=
  " ".intercalate (s.splitOn "\n" |>.flatMap (·.splitOn " ") |>.filter (· != ""))

def pretty (e : Expr) : MetaM String := do
  try return flat (toString (← PrettyPrinter.ppExpr e))
  catch _ => return flat (toString e)

def allow (path : String) : IO (List String) := do
  return (← IO.FS.readFile path).splitOn "\n" |>.map (fun s =>
    (s.splitOn "#").head!.trimAscii.toString) |>.filter (· != "")

def run (args : List String) : IO UInt32 := do
  let cmd :: rest := args | throw (IO.userError "missing subcommand")
  unless ["extensions", "snapshot", "theorems", "noconst", "statements", "reach", "dependencies"].contains cmd do
    throw (IO.userError s!"unknown subcommand: {cmd}")
  let mut rest := rest
  let mut allowPath : Option String := none
  let mut out : Option String := none
  let mut report := false
  let mut seeds : List Name := []
  while rest.head? != some "--modules" do
    match rest with
    | "--allow" :: p :: xs =>
      unless cmd == "extensions" || cmd == "theorems" do throw (IO.userError "unexpected --allow")
      if p.startsWith "--" then throw (IO.userError "missing --allow argument")
      allowPath := some p; rest := xs
    | "--out" :: p :: xs =>
      unless cmd == "snapshot" do throw (IO.userError "unexpected --out")
      if p.startsWith "--" then throw (IO.userError "missing --out argument")
      out := some p; rest := xs
    | "--from" :: xs =>
      unless cmd == "reach" || cmd == "dependencies" do throw (IO.userError "unexpected --from")
      let names := xs.takeWhile (· != "--modules")
      if names.isEmpty then throw (IO.userError "empty --from")
      seeds := names.map String.toName; rest := xs.drop names.length
    | "--report" :: xs =>
      unless cmd == "theorems" do throw (IO.userError "unexpected --report")
      report := true; rest := xs
    | _ => throw (IO.userError "invalid options or missing --modules")
  let mods := rest.tail!.toArray.map String.toName
  if mods.isEmpty || mods.any (fun m => m.toString.startsWith "--") then
    throw (IO.userError "--modules requires module names")
  let allowed ← if cmd == "extensions" || cmd == "theorems" then do
    let some p := allowPath | throw (IO.userError "missing --allow")
    allow p
    else pure []
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map ({module := ·})) {} (loadExts := false) (level := .private)
  if cmd == "dependencies" then
    if seeds.isEmpty then throw (IO.userError "missing --from")
    let mut visited : NameSet := {}
    let mut todo := seeds
    while let n :: ns := todo do
      todo := ns
      if visited.contains n then continue
      visited := visited.insert n
      let some ci := env.find? n | do
        IO.println (Json.mkObj [("missing", toJson n.toString)]).compress
        continue
      let deps := ci.getUsedConstantsAsSet.toList
      todo := deps ++ todo
      let owner := (env.getModuleIdxFor? n).map (env.header.moduleNames[·]!.toString)
      IO.println (Json.mkObj [
        ("declaration", toJson n.toString), ("module", toJson owner),
        ("dependencies", toJson (deps.map Name.toString |>.mergeSort (· < ·))) ]).compress
    return 0
  let mut failed := false
  let mut lines : Array String := #[]
  let mut seen : List String := []
  -- The constants a module owns (`getModuleIdxFor?`), in name order: read from the module's own
  -- `constNames` instead of filtering and sorting the whole environment once per call.
  let ownedBy (idxs : Array Nat) : Array (Name × ConstantInfo) :=
    (idxs.foldl (init := #[]) fun acc i => env.header.moduleData[i]!.constNames.foldl (init := acc) fun acc n =>
      if env.getModuleIdxFor? n == some i then
        match env.constants.find?' n with | some ci => acc.push (n, ci) | none => acc
      else acc).qsort (fun a b => a.1.toString < b.1.toString)
  if cmd == "reach" then
    if seeds.isEmpty then throw (IO.userError "missing --from")
    for n in seeds do
      unless env.contains n do throw (IO.userError s!"unknown declaration: {n}")
    let mut reached : NameSet := {}
    let mut todo := seeds
    while let n :: ns := todo do
      todo := ns
      if reached.contains n then continue
      reached := reached.insert n
      if let some ci := env.find? n then todo := ci.getUsedConstantsAsSet.toList ++ todo
    let idxs := (List.range env.header.moduleNames.size).toArray.filter (mods.contains env.header.moduleNames[·]!)
    let result ← runMeta env do
      let mut result : Array String := #[]
      for (n, ci) in ownedBy idxs do
        if reached.contains n then result := result.push n.toString
        else if ci matches .defnInfo _ then
          if (← findDeclarationRanges? n).isSome then result := result.push s!"UNREACHED {n}"
      return result
    for line in result do IO.println line
    return 0
  for m in mods do
    let some idx := env.header.moduleNames.idxOf? m | throw (IO.userError s!"module not loaded: {m}")
    if cmd == "extensions" then
      for (ext, entries) in env.header.moduleData[idx]!.entries do
        unless entries.isEmpty do
          seen := ext.toString :: seen
          unless allowed.contains ext.toString do
            lines := lines.push s!"FAIL[ext] {m} {ext}"; failed := true
      continue
    let owned := ownedBy #[idx]
    if cmd == "noconst" then
      unless owned.isEmpty do
        lines := lines.push s!"FAIL[noconst] {m} {owned.size} {String.intercalate " " (owned.toList.take 5 |>.map (·.1.toString))}"
        failed := true
      continue
    if cmd == "snapshot" then lines := lines.push s!"## {m}"
    let more ← runMeta env do
      let mut result := #[]
      for (n, ci) in owned do
        let ranged := (← findDeclarationRanges? n).isSome
        if cmd == "theorems" then
          if ci matches .thmInfo _ then
            if ranged && !env.isProjectionFn n && !allowed.contains n.toString then
              result := result.push s!"{if report then "REPORT" else "FAIL"}[theorem] {m} {n}"
          continue
        if cmd == "statements" then
          if ci matches .defnInfo _ then
            if ci.type == .sort .zero then result := result.push n.toString
          continue
        let prop ← isProp ci.type
        let value := if prop then none else ci.value? (allowOpaque := true)
        let hashes := s!"{ci.type.hash}/{value.map (fun v => toString v.hash) |>.getD "-"}"
        if ranged || (ci matches .ctorInfo _) || env.isProjectionFn n then
          let mut line := s!"{kind ci} {n} : {← pretty ci.type}"
          if let .defnInfo d := ci then
            unless prop do line := line ++ s!" := {← pretty d.value}"
          result := result.push line |>.push s!"  #{hashes}"
        else result := result.push s!"{kind ci} {n} #{hashes}"
      return result
    if cmd == "theorems" && !report && !more.isEmpty then failed := true
    lines := lines ++ more
  if cmd == "extensions" then
    for ext in allowed do
      unless seen.contains ext do lines := lines.push s!"WARN[ext] unused {ext}"
  if cmd == "statements" then lines := lines.qsort (· < ·)
  let text := if lines.isEmpty then "" else "\n".intercalate lines.toList ++ "\n"
  if let some path := out then IO.FS.writeFile path text else IO.print text
  return if failed then 1 else 0
end SpecSurface

def main (args : List String) : IO UInt32 := do
  try SpecSurface.run args
  catch e => IO.eprintln s!"error: {e}"; return 2
