import Lean
open Lean

/-! Statement census: the gate for a toolchain or Mathlib bump.

For every constant of an `AvailableChain*` module that an importer can see,
one line: `user|gen <name> <kind> <module> <type hash> [<value hash>]`. The
value hash is given for a definition or opaque; a theorem contributes only
its statement, so a new proof keeps the line. An inductive lists its
constructors. `gen` marks names that Lean generates (equation lemmas,
matchers, auxiliary proofs); they depend on which tactics ran.

The hash is an FNV-1a fold over a structural walk of the `Expr`. It ignores
binder names and metadata, keeps binder info and universe levels, and does
not use Lean's own `Expr.hash`, so the output of two toolchains can be
compared. Unlike `CatalogLock`, it does not follow the closure: a changed
Mathlib definition does not change a line, but a changed elaboration of a
project statement (for example a new instance path or a renamed constant in
the statement) does.

Usage (bump procedure, one run per toolchain, in a built tree):
  `lake env lean --run scripts/StmtCensus.lean > census-<toolchain>.txt`
then `diff` the `user` lines of the two files. Every difference must have a
cause outside the project (record it in the lock log, design §8; example:
`docs/lock-log/v4.34.1/`); a declaration that the bump edited must not
differ. The module of a `gen` line is the first module that generated the
name, so it can move when the import set changes; compare `gen` lines without
it. Run it in the project root: it imports every built module found there. -/

def fnv (h : UInt64) (b : UInt8) : UInt64 := (h ^^^ b.toUInt64) * 1099511628211
def mixStr (h : UInt64) (s : String) : UInt64 := s.toUTF8.foldl fnv h
def mixNat (h : UInt64) (n : Nat) : UInt64 := mixStr h (toString n)
def seed : UInt64 := 14695981039346656037

partial def hLevel (h : UInt64) : Level → UInt64
  | .zero => mixStr h "z"
  | .succ l => hLevel (mixStr h "s") l
  | .max a b => hLevel (hLevel (mixStr h "m") a) b
  | .imax a b => hLevel (hLevel (mixStr h "i") a) b
  | .param n => mixStr (mixStr h "p") n.toString
  | .mvar _ => mixStr h "?"

def bi : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

/-- Memo key with strict equality: `Expr` `==` ignores binder info, the hash does not. -/
structure K where
  e : Expr
instance : BEq K := ⟨fun a b => a.e.equal b.e⟩
instance : Hashable K := ⟨fun a => a.e.hash⟩

abbrev M := StateM (Std.HashMap K UInt64)

partial def hE (e : Expr) : M UInt64 := do
  if let some v := (← get)[K.mk e]? then return v
  let v ← match e with
    | .bvar i => pure (mixNat (mixStr seed "b") i)
    | .fvar id => pure (mixStr (mixStr seed "f") id.name.toString)
    | .mvar _ => pure (mixStr seed "m")
    | .sort l => pure (hLevel (mixStr seed "S") l)
    | .const n ls => pure (ls.foldl hLevel (mixStr (mixStr seed "c") n.toString))
    | .app f a => do
        let x ← hE f; let y ← hE a
        pure (mixNat (mixNat (mixStr seed "a") x.toNat) y.toNat)
    | .lam _ t b i => do
        let x ← hE t; let y ← hE b
        pure (mixNat (mixNat (mixStr seed ("l" ++ bi i)) x.toNat) y.toNat)
    | .forallE _ t b i => do
        let x ← hE t; let y ← hE b
        pure (mixNat (mixNat (mixStr seed ("F" ++ bi i)) x.toNat) y.toNat)
    | .letE _ t v b _ => do
        let x ← hE t; let y ← hE v; let z ← hE b
        pure (mixNat (mixNat (mixNat (mixStr seed "L") x.toNat) y.toNat) z.toNat)
    | .lit (.natVal n) => pure (mixNat (mixStr seed "n") n)
    | .lit (.strVal s) => pure (mixStr (mixStr seed "t") s)
    | .mdata _ b => hE b
    | .proj s i b => do
        let x ← hE b
        pure (mixNat (mixNat (mixStr (mixStr seed "P") s.toString) i) x.toNat)
  modify (·.insert (K.mk e) v)
  return v

def hex (x : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (16 - s.length) ++ s

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

/-- Every built module of the project: each `.lean` file under an
`AvailableChain*` directory of the working directory, and the root files, that
has an `.olean` in `.lake/build`. Test modules that only a glob builds are
included, so the census does not depend on the root imports. Files that no
target builds (no `.olean`) are skipped and counted on stderr. -/
def projectModules : IO (Array Name) := do
  let modules ← layoutOutput #["--exclude-source-dir", "scripts", "modules"]
  let mut out := #[]
  let mut skipped := 0
  for text in modules do
    let rel := text.replace "." "/"
    let olean := (System.FilePath.mk ".lake/build/lib/lean" / rel).withExtension "olean"
    if ← olean.pathExists then out := out.push text.toName
    else skipped := skipped + 1
  IO.eprintln s!"census: {out.size} modules, {skipped} unbuilt files skipped"
  return out.qsort Name.lt

/-- Auto-generated names: their presence depends on which tactics ran. -/
def generated (n : Name) : Bool :=
  n.isInternal || n.components.any fun c =>
    let s := c.toString
    s.startsWith "eq_" || s == "eq_def" || s.startsWith "match_" || s.startsWith "proof_" ||
      s == "splitter" || s.startsWith "_" || s == "congr_simp" || s == "fun_cases" ||
      s == "induct" || s == "induct_unfolding" || s == "eq_iff"

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules ((← projectModules).map fun m => { module := m }) {}
  let mut rows : Array String := #[]
  let mut memo : Std.HashMap K UInt64 := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.toString.startsWith "AvailableChain" do continue
    let tag := if generated n then "gen" else "user"
    let (ht, m1) := (hE ci.type).run memo
    memo := m1
    let (kind, hv) ← match ci with
      | .thmInfo _ => pure ("thm", "")
      | .axiomInfo _ => pure ("axiom", "")
      | .defnInfo d => do
          let (x, m2) := (hE d.value).run memo; memo := m2; pure ("def", hex x)
      | .opaqueInfo d => do
          let (x, m2) := (hE d.value).run memo; memo := m2; pure ("opaque", hex x)
      | .inductInfo d => pure ("induct", ",".intercalate (d.ctors.map toString))
      | .ctorInfo _ => pure ("ctor", "")
      | .recInfo _ => pure ("rec", "")
      | .quotInfo _ => pure ("quot", "")
    rows := rows.push s!"{tag} {n} {kind} {mod} {hex ht} {hv}"
  for r in rows.qsort (· < ·) do
    IO.println r
  return 0
