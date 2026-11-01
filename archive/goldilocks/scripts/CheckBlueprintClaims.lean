import Lean.Util.CollectAxioms
import Lean.Meta.InferType
open Lean

/-! D10 blueprint oracle. It reads compiled constants for
`scripts/check-fgsa-blueprint.py`, which compares them with
`docs/FGSA-BLUEPRINT-LEAN.json`.

Run from the repository root after the build:
  lake env lean --run scripts/CheckBlueprintClaims.lean <request>

The request file has one item per line: `import <module>` or `const <name>`.
The oracle imports the listed modules. For each `const` it prints one line:

  CONST <name> kind=<kind> module=<module> fingerprint=<16 hex> binders=<n> props=<n> axioms=<a,b,…>

or `MISSING <name>`. `kind` is the constant kind (`theorem`, `definition`, …).
`binders` counts the leading `∀` binders of the type, without unfolding;
`props` counts the binders among them whose type is a proposition. `axioms` is
the transitive axiom set, sorted (`-` when empty).

`fingerprint` is the closure hash of `scripts/CatalogLock.lean` in its
`--local` form, applied to the constant: a fold of the own hashes of every
project constant that the statement reaches, in `Name.lt` order. A constant
outside the project is a leaf hashed by its name. A theorem contributes its
statement only, so a new proof keeps the fingerprint. A changed statement, or a
changed definition, structure or field type that the statement reaches,
changes it. As in the catalog lock, the hash is a tripwire, not a proof of
equality. `kindTag`, `ownHash`, `deps`, `foreign` and the closure traversal
are copies of `scripts/CatalogLock.lean`; a change to one needs the same
change in the other.

Exit codes: 0 after all lines are printed; 2 for a usage error, an empty or
malformed request, or a module that cannot be imported (`INPUT ERROR: …`). -/

namespace CheckBlueprintClaims

def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!)

def kindTag : ConstantInfo → UInt64
  | .axiomInfo _ => 1 | .defnInfo _ => 2 | .thmInfo _ => 3 | .opaqueInfo _ => 4
  | .quotInfo _ => 5 | .inductInfo _ => 6 | .ctorInfo _ => 7 | .recInfo _ => 8

def kindName : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def ownHash (ci : ConstantInfo) : UInt64 :=
  let base := mixHash (mixHash (kindTag ci) (hash ci.name)) (hash ci.type)
  match ci with
  | .defnInfo d => mixHash base (hash d.value)
  | .opaqueInfo d => mixHash base (hash d.value)
  | .inductInfo d => d.ctors.foldl (fun h c => mixHash h (hash c)) base
  | _ => base

def deps (ci : ConstantInfo) : Array Name :=
  match ci with
  | .thmInfo _ => ci.type.getUsedConstants
  | _ => ci.getUsedConstantsAsSet.toArray

def foreign (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => !(m.getRoot.toString.startsWith "AvailableChain")
  | none => false

/-- The own hash and dependencies of `n`; a foreign constant is a leaf. -/
def node (env : Environment) (n : Name) : Except String (UInt64 × Array Name) := do
  let some ci := env.find? n | throw s!"missing declaration: {n}"
  return if foreign env n then (mixHash 99 (hash n), #[]) else (ownHash ci, deps ci)

def fingerprint (env : Environment) (n : Name) : Except String UInt64 := do
  let mut seen : Std.HashSet Name := ({} : Std.HashSet Name).insert n
  let mut stack := #[n]
  let mut out := #[]
  while h : stack.size > 0 do
    let m := stack[stack.size - 1]
    stack := stack.pop
    out := out.push m
    for d in (← node env m).2 do
      unless seen.contains d do
        seen := seen.insert d
        stack := stack.push d
  let mut acc : UInt64 := 0
  for m in out.qsort Name.lt do
    acc := mixHash acc (← node env m).1
  return acc

def hex (u : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 u.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- Leading binders of the type, and how many of them are propositions. -/
def binderCounts (ty : Expr) : MetaM (Nat × Nat) :=
  Meta.forallTelescope ty fun xs _ => do
    let mut props := 0
    for x in xs do
      if ← Meta.isProp (← Meta.inferType x) then props := props + 1
    return (xs.size, props)

def report (env : Environment) (n : Name) : IO String := do
  let some ci := env.find? n | return s!"MISSING {n}"
  let ctx : Core.Context := { fileName := "CheckBlueprintClaims", fileMap := .ofString "" }
  let axs ← Core.CoreM.toIO' (collectAxioms n) ctx { env := env }
  let (binders, props) ← Core.CoreM.toIO' (Meta.MetaM.run' (binderCounts ci.type)) ctx { env := env }
  let fp ← match fingerprint env n with
    | .ok h => pure (hex h)
    | .error e => throw (IO.userError e)
  let axText := if axs.isEmpty then "-"
    else ",".intercalate ((axs.qsort Name.lt).toList.map toString)
  let m := (moduleOf? env n).map toString |>.getD "-"
  return s!"CONST {n} kind={kindName ci} module={m} fingerprint={fp} binders={binders} " ++
    s!"props={props} axioms={axText}"

end CheckBlueprintClaims

open CheckBlueprintClaims in
def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "USAGE: lake env lean --run scripts/CheckBlueprintClaims.lean <request>"; return 2
  let lines ← try IO.FS.lines path catch e => IO.eprintln s!"INPUT ERROR: {e}"; return 2
  let mut imports : Array Name := #[]
  let mut consts : Array Name := #[]
  for line in lines do
    match line.trimAscii.toString.splitOn " " with
    | ["import", m] => imports := imports.push m.toName
    | ["const", c] => consts := consts.push c.toName
    | [""] => pure ()
    | _ => IO.eprintln s!"INPUT ERROR: malformed request line: {line}"; return 2
  if imports.isEmpty || consts.isEmpty then
    IO.eprintln "INPUT ERROR: empty request"
    return 2
  initSearchPath (← findSysroot)
  let env ← try importModules (imports.map ({ module := · })) {} (loadExts := false)
    catch e => IO.eprintln s!"INPUT ERROR: {e}"; return 2
  for c in consts do
    IO.println (← report env c)
  return 0
