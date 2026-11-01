import AvailableChainRegistry
import Lean.Util.CollectAxioms
import Lean.Meta.Basic
import Lean.Elab.Frontend
open Lean

/-! Type-scanning registry. Every constant in `AvailableChainRegistry` whose
type head is in `kinds` is a row of `docs/REGISTRY.md`: `Cert c I`,
`Refutation c I`, `RefutationFamily c I` (with the claim domain `K` of
`c : ClaimSpec K` as the first, implicit argument), `ProfileCert p I` (with
`K` of `p : Profile K` first), `Candidate I` and `Profile.holdsAt p I C`
(kind `profile-holds`, arguments `K p I C`).

A `profile-holds` row proves the profile's claim propositions at one
constant, without inhabitation; it can be vacuous. It is not a certificate.
A family row holds for every value of its data binders.

A type with leading binders (`∀ …, Cert c I`) is CONDITIONAL and is not a
certificate; it is still written as a row, with status `CONDITIONAL (not a
certificate)`. The one exception is a FAMILY row: a row of kind
`profile-holds` whose binder telescope (implicit and instance binders
included) has exactly one binder, whose type is not a `Prop` and is
syntactically a type of `familyBinders` (an `abbrev` alias is not unfolded,
so `SAPC.Params` has its own entry), and whose instance argument, below its
parent projections, is `f x` with `x` that binder (so the binder reaches the
instance). Each type of `familyBinders` has a witness, and the script checks
that the witness exists, is not `unsafe`, has exactly that type and uses only
the allowed axioms (exit 2 otherwise). So the domain is not empty, and the
`Prop` fields of the type (`deltaPos`, …) stay visible as the constraints of
the domain. A witness does not show that a run exists. Every other leading
binder (a `Prop`, a data type outside `familyBinders`, a function type, two
or more binders, a binder that the instance does not use) makes the row
CONDITIONAL.

A row that is not CONDITIONAL has status `LEAN` only if every axiom the
declaration transitively depends on (`Lean.collectAxioms`) is one of
`propext`, `Classical.choice`, `Quot.sound`. Any other axiom (including
`sorryAx`) gives status `UNSOUND(<axiom names>)`; a CONDITIONAL row is not
checked, since it is not a certificate. An `unsafe` declaration has status
`UNSOUND(unsafe)`, with or without binders, since an `unsafe` self-reference
proves any type without an axiom. A row's claim column keeps the claim's
name and appends `NON-CATALOG` if the `ClaimSpec` it certifies is not
declared in a module under `AvailableChainFramework.Catalog`.

A certificate of a pulled claim `ClaimSpec.pull m c` shows the base claim
`c` with the suffix `(pulled)`. A row of kind `profile-cert` (a `ProfileCert p
I`, or a `Candidate I`, which is `ProfileCert core I`) or `profile-holds`
shows the profile `id` in the claim column, for example `core.v1`, and then
its constant as ` at C = <term>` (`constSuffix`). The instance column names
the source instance: below a parent projection to an instance type
(`(sapcInst p).toInstance` gives `sapcInst`), the head constant if the
instance depends on a binder (`gridInst p` gives `gridInst`), and the full
term if it is closed (`gridInst smokeParams`), so that a row at one parameter
record does not read as a row for every record.

The libraries in `instanceLibraries` are imported, and only their modules
give rows. A row of a module under `AvailableChainRegistry.Gaps` has status
`KNOWN-GAP` in place of `LEAN`; `UNSOUND` and `CONDITIONAL` stay. A family
row gets the suffix ` (family)` after this rule: `LEAN (family)` or
`KNOWN-GAP (family)`.

The same run writes `docs/MATRIX.md` from the same rows: one line per
constant of `instanceLibraries` whose type (after its leading binders) is an
`instanceTypes` type, and one line per other instance column of a row (a
closed instance term); one column per catalog claim and one per catalog
profile. Its header gives the meaning of each cell.

Run: `lake env lean --run scripts/Registry.lean [--check | (--selftest |
--selftest-write) <file> [<module>]]`. Without an argument, write
`docs/REGISTRY.md` and `docs/MATRIX.md`. With `--check`, compare the texts
with the two files, name each file that is different, and write nothing.
With `--selftest`, elaborate the Lean file `<file>` as the module `<module>`
(default `RegistrySelfTest`), print one line per row of its own declarations
(the row and its MATRIX cell), and compare the lines with the file
`<file>.expected` (`<file>.<module>.expected` for another module).
`--selftest-write` writes that file in place of the comparison.
Exit codes: 0 written, or the same; 1 different; 2 a usage error, an
unreadable file, a missing witness, a witness of a wrong type, `unsafe` or
with a bad axiom, or a self-test file that does not elaborate. -/

/-- The libraries that hold certificates and refutations. The script imports
them and scans only their modules. -/
def instanceLibraries : List Name := [`AvailableChainRegistry]

/-- Rows of these modules are known gaps: a `LEAN` status becomes
`KNOWN-GAP`. -/
def gapsPrefix : Name := `AvailableChainRegistry.Gaps

/-- The allowed data binders of a family row, as pairs (type, witness). Any
other family shape needs its own domain and a checked proof over the whole
domain before it is added here. -/
def familyBinders : List (Name × Name) :=
  [(`AvailableChain.GridCO.Params, `AvailableChain.GridCO.Tests.smokeParams),
   (`AvailableChain.SA.Params, `AvailableChain.SA.Tests.p),
   (`AvailableChain.SAPC.Params, `AvailableChain.SAPC.Tests.p)]

/-- The modules of the witnesses in `familyBinders`. The script imports them;
they give no rows. -/
def witnessModules : List Name :=
  [`AvailableChainGridCO.Tests.Smoke, `AvailableChainSA.Tests.Smoke,
   `AvailableChainSAPC.Tests.Smoke]

/-- The head constant after all leading binders, and whether binders exist. -/
partial def headOf (e : Expr) (binders : Bool := false) : Option Name × Bool :=
  match e with
  | .forallE _ _ b _ => headOf b true
  | _ => (e.getAppFn.constName?, binders)

def kinds : List (Name × String) :=
  [(``AvailableChain.Framework.Cert, "cert"),
   (``AvailableChain.Framework.Refutation, "refutation"),
   (``AvailableChain.Framework.RefutationFamily, "refutation-family"),
   -- Arguments `K p I`.
   (``AvailableChain.Framework.ProfileCert, "profile-cert"),
   -- Argument `I`. `Candidate I` is a `def`, so its type head is `Candidate`.
   (``AvailableChain.Framework.Catalog.Candidate, "profile-cert"),
   -- Arguments `K p I C`.
   (``AvailableChain.Framework.Profile.holdsAt, "profile-holds")]

/-- The types of an instance: a MATRIX line, and the target of a projection
that the instance column looks through. -/
def instanceTypes : List Name :=
  [``AvailableChain.Framework.Instance, ``AvailableChain.Framework.StrongInstance]

/-- Axioms allowed in a sound LEAN row. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Run `x` in the environment `env`. -/
def runMeta (env : Environment) (x : MetaM α) : IO α :=
  Core.CoreM.toIO' (Meta.MetaM.run' x) { fileName := "Registry", fileMap := .ofString "" }
    { env := env }

/-- The axioms `n` transitively depends on. -/
def axiomsOf (env : Environment) (n : Name) : IO (Array Name) :=
  Core.CoreM.toIO' (collectAxioms n) { fileName := "Registry", fileMap := .ofString "" }
    { env := env }

/-- The axioms of `n` outside `allowedAxioms`, sorted. -/
def badAxioms (env : Environment) (n : Name) : IO (Array Name) := do
  return ((← axiomsOf env n).filter (fun a => !allowedAxioms.contains a)).qsort Name.lt

/-- `n`'s status column: `LEAN`, or `UNSOUND(ax1, ax2, …)` if it depends on
an axiom outside `allowedAxioms`. -/
def statusOf (env : Environment) (n : Name) : IO String := do
  let bad ← badAxioms env n
  if bad.isEmpty then
    return "LEAN"
  else
    return s!"UNSOUND({String.intercalate ", " (bad.toList.map toString)})"

/-- The problems with the witnesses of `familyBinders`: a missing witness, an
`unsafe` witness, a witness whose type is not exactly its binder type, or a bad
axiom. -/
def witnessProblems (env : Environment) : IO (List String) := do
  let mut out := []
  for (ty, w) in familyBinders do
    match env.find? w with
    | none => out := out ++ [s!"missing witness {w} for {ty}"]
    | some ci =>
        if ci.isUnsafe then
          out := out ++ [s!"witness {w} is unsafe"]
        if ci.type != mkConst ty then
          out := out ++ [s!"witness {w} does not have the type {ty}"]
        let bad ← badAxioms env w
        unless bad.isEmpty do
          out := out ++ [s!"witness {w} uses the axioms {bad.toList}"]
  return out

/-- The types of the leading binders of `t` (implicit and instance binders
included), each with whether it is a `Prop`. -/
def bindersOf (env : Environment) (t : Expr) : IO (Array (Expr × Bool)) :=
  runMeta env <| Meta.forallTelescope t fun xs _ => xs.mapM fun x => do
    let ty ← Meta.inferType x
    return (ty, ← Meta.isProp ty)

/-- The row is a family: kind `profile-holds`, exactly one binder, and that
binder's type is not a `Prop` and is a type of `familyBinders`. -/
def isFamily (kind : String) (bs : Array (Expr × Bool)) : Bool :=
  kind == "profile-holds" &&
    match bs with
    | #[(.const ty [], false)] => (familyBinders.lookup ty).isSome
    | _ => false

/-- Every catalog claim lives in a module under this prefix. -/
def catalogPrefix : Name := `AvailableChainFramework.Catalog

/-- `n` is declared in a module under `catalogPrefix`. -/
def inCatalog (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => catalogPrefix.isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => false

/-- `n`'s claim column: its name (or `shown`), with `NON-CATALOG` appended if
`n` is not declared in a module under `catalogPrefix`. -/
def claimOf (env : Environment) (n : Name) (shown : String := toString n) : String :=
  if inCatalog env n then shown else shown ++ " NON-CATALOG"

/-- An `id` as text, without `«»` (`ac-4.3`, not `«ac-4.3»`). -/
def idText (id : Name) : String := id.toString (escape := false)

/-- The base claim of `c` below all `ClaimSpec.pull` layers, and whether `c`
has one. In `@ClaimSpec.pull K K' m c'`, the base claim `c'` is the last
argument. -/
partial def pullBase (c : Expr) : Expr × Bool :=
  if c.isAppOfArity ``AvailableChain.Framework.ClaimSpec.pull 4 then
    ((pullBase c.getAppArgs.back!).1, true)
  else (c, false)

/-- The claim column of a claim expression `c`. For a pulled claim, the
innermost base claim with the suffix `(pulled)`. -/
def claimColumn (env : Environment) (c : Expr) : String :=
  let (b, pulled) := pullBase c
  (b.getAppFn.constName?.map (claimOf env)).getD "?" ++ (if pulled then " (pulled)" else "")

/-- The name that a closed `Name` expression in normal form denotes. -/
partial def nameOfExpr? (e : Expr) : Option Name :=
  if e.isConstOf ``Name.anonymous then some .anonymous
  else match e.getAppFn.constName?, e.getAppArgs with
    | some ``Name.str, #[p, .lit (.strVal s)] => (nameOfExpr? p).map (·.str s)
    | some ``Name.num, #[p, .lit (.natVal k)] => (nameOfExpr? p).map (·.num k)
    | _, _ => none

/-- The `id` of a claim or profile `x` over the claim domain `K`, by reduction
of `idFn K x` (`ClaimSpec.id` or `Profile.id`). -/
def idOf? (env : Environment) (idFn : Name) (K x : Expr) : IO (Option Name) := do
  try
    let r ← runMeta env (Meta.reduce (mkApp2 (mkConst idFn) K x))
    pure (nameOfExpr? r)
  catch _ => pure none

/-- The claim column of a profile certificate: the `id` of the profile `p`
over the claim domain `K`, by reduction of `Profile.id p`. If the reduction does not
give a name, the name of the constant `p`. `NON-CATALOG` as for a claim. -/
def profileColumn (env : Environment) (K p : Expr) : IO String := do
  let some n := p.getAppFn.constName? | return "?"
  let pid ← idOf? env ``AvailableChain.Framework.Profile.id K p
  return claimOf env n (idText (pid.getD n))

/-- The field `k` of the structure `s` is a parent (subobject) field whose
parent is an `instanceTypes` type. -/
def parentInstField (env : Environment) (s : Name) (k : Nat) : Bool :=
  isStructure env s &&
    match (getStructureFields env s)[k]? with
    | some f => (isSubobjectField? env s f).any instanceTypes.contains
    | none => false

/-- The instance argument `i` below its parent projections to an
`instanceTypes` type (`StrongInstance.toInstance x`, or the same `Expr.proj`,
gives `x`). Any other projection stays. -/
partial def instCore (env : Environment) (i : Expr) : Expr :=
  match i with
  | .proj s k x => if parentInstField env s k then instCore env x else i
  | _ =>
    match i.getAppFn.constName?.bind env.getProjectionFnInfo? with
    | some info =>
        if parentInstField env info.ctorName.getPrefix info.i &&
            i.getAppNumArgs == info.numParams + 1 then instCore env i.appArg!
        else i
    | none => i

/-- `e` pretty-printed on one line, with full names. -/
def ppLine (e : Expr) : MetaM String := do
  let f ← withOptions (fun o => o.setBool `pp.fullNames true) (Meta.ppExpr e)
  -- One space for each run of white space.
  let (out, _) := (toString f).foldl (init := ("", false)) fun (acc, sp) c =>
    if c.isWhitespace then (if sp then (acc, true) else (acc.push ' ', true))
    else (acc.push c, false)
  return out

/-- The instance column of the instance argument `i` of the type `t` (after the
binders of `t`), below its parent projections (`instCore`): its head constant
if it depends on a binder or has no arguments (`gridInst p` gives `gridInst`),
else the full closed term (`gridInst smokeParams`), so that a row at one
parameter record gets its own MATRIX line. `?` if the head is not a constant. -/
def instName (env : Environment) (t i : Expr) : IO String := do
  let c := instCore env i
  let some f := c.getAppFn.constName? | return "?"
  if c.hasLooseBVars || c.getAppNumArgs == 0 then return toString f
  runMeta env <| Meta.forallTelescope t fun _ _ => ppLine c

/-- The instance argument `i` (after one binder), below its parent
projections, is `f x` with `x` that binder: the binder reaches the instance. -/
def bindsInstance (env : Environment) (i : Expr) : Bool :=
  let c := instCore env i
  c.getAppFn.isConst && c.getAppNumArgs == 1 && c.appArg! == .bvar 0

/-- The constant of a row of kind `profile-holds` or `profile-cert`, as the
suffix ` at C = <term>` of its claim column. For `profile-holds`, the argument
`C` of `holdsAt p I C` (with the binder names of the type). For
`profile-cert`, the field `shared` of the value, if the value reduces to
`ProfileCert.mk`; else `?`. -/
def constSuffix (env : Environment) (h : Name) (ci : ConstantInfo) : IO String := do
  let c ← try
      runMeta env <| Meta.forallTelescope ci.type fun _ body => do
        if h == ``AvailableChain.Framework.Profile.holdsAt then
          ppLine body.getAppArgs[3]!
        else
          let some v := ci.value? | return "?"
          let v ← Meta.whnf v
          if v.isAppOfArity ``AvailableChain.Framework.ProfileCert.mk 6 then
            ppLine v.getAppArgs[3]!
          else return "?"
    catch _ => pure "?"
  return s!" at C = {c}"

/-- One row of `docs/REGISTRY.md`. `col` is the constant of the catalog claim
(the base claim of a pull) or catalog profile of the row, if there is one. -/
structure Row where
  decl : Name
  kind : String
  claim : String
  col : Option Name
  inst : String
  status : String

def Row.line (r : Row) : String :=
  s!"│ {r.decl} │ {r.kind} │ {r.claim} │ {r.inst} │ {r.status} │"

/-- The row of the constant `n` of the module `m`, if its type head is in
`kinds`. -/
def rowOf (env : Environment) (n : Name) (ci : ConstantInfo) (m : Name) :
    IO (Option Row) := do
  let (h, _) := headOf ci.type
  let some h := h | return none
  let some kind := kinds.lookup h | return none
  let args := ci.type.getForallBody.getAppArgs
  -- The claim (or profile) column, its catalog constant, and the instance argument.
  let (claim, col, i) ← match h with
    | ``AvailableChain.Framework.ProfileCert | ``AvailableChain.Framework.Profile.holdsAt =>
        -- `K p I` (and `C`): the claim domain, the profile, the instance.
        let p := args[1]!
        let col := p.getAppFn.constName?.filter (inCatalog env)
        pure ((← profileColumn env args[0]! p) ++ (← constSuffix env h ci), col, args[2]!)
    | ``AvailableChain.Framework.Catalog.Candidate =>
        -- `I`: `Candidate I` is `ProfileCert core I` over `v1`. The two
        -- constants are hard-coded here. A change to `Candidate` or `core`
        -- changes their lines in `docs/catalog.lock`, so `CatalogLock
        -- --check` fails until this path is checked again.
        pure ((← profileColumn env (mkConst ``AvailableChain.Framework.ClaimDomain.v1)
            (mkConst ``AvailableChain.Framework.Catalog.core)) ++ (← constSuffix env h ci),
          some ``AvailableChain.Framework.Catalog.core, args[0]!)
    | _ =>
        -- `K c I`: the claim domain, the claim, the instance.
        let col := (pullBase args[1]!).1.getAppFn.constName?.filter (inCatalog env)
        pure (claimColumn env args[1]!, col, args[2]!)
  let bs ← bindersOf env ci.type
  let family := isFamily kind bs && bindsInstance env i
  -- `collectAxioms` finds no axiom in an `unsafe` self-reference, which
  -- proves any type.
  let status ← if ci.isUnsafe then pure "UNSOUND(unsafe)"
    else if bs.isEmpty || family then statusOf env n
    else pure "CONDITIONAL (not a certificate)"
  let status := if status == "LEAN" && gapsPrefix.isPrefixOf m then "KNOWN-GAP" else status
  let status := if family then status ++ " (family)" else status
  return some { decl := n, kind, claim, col, inst := ← instName env ci.type i, status }

/-- The rows of the declarations of `instanceLibraries` modules, sorted by
line, and the instance constants of those modules. -/
def scan (env : Environment) : IO (Array Row × Array Name) := do
  let mut rows : Array Row := #[]
  let mut insts : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    -- Only declarations of `instanceLibraries` modules are rows.
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless instanceLibraries.any (·.isPrefixOf m) do continue
    if (headOf ci.type).1.any instanceTypes.contains then insts := insts.push n
    if let some r ← rowOf env n ci m then rows := rows.push r
  return (rows.qsort (·.line < ·.line), insts.qsort (toString · < toString ·))

/-- The text of `docs/REGISTRY.md`. -/
def registryText (rows : Array Row) : String :=
  let libs := String.intercalate ", " (instanceLibraries.map (s!"`{·}`"))
  "# Registry (generated by scripts/Registry.lean; do not edit)\n\n" ++
    s!"Scanned libraries: {libs}.\n\n```text\n" ++
    "│ Declaration │ Kind │ Claim │ Instance │ Status │\n" ++
    String.intercalate "\n" (rows.toList.map Row.line) ++ "\n```\n"

/-- The catalog constants whose type (with no binders) has the head `ty`, in
lock order (`Name.lt`), each with its `id`. The `id` of `idFn` is reduced; a
constant whose `id` does not reduce to a name is shown by its name. -/
def catalogColumns (env : Environment) (ty idFn : Name) : IO (Array (Name × Name)) := do
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal || !inCatalog env n then continue
    unless ci.type.isAppOfArity ty 1 do continue
    let id ← idOf? env idFn ci.type.appArg! (mkConst n)
    out := out.push (n, id.getD n)
  return out.qsort (fun a b => Name.lt a.1 b.1)

/-- The cell of one row: a result only for a `LEAN` or `LEAN (family)` row. -/
def cellOf (r : Row) : String :=
  if r.status == "LEAN" || r.status == "LEAN (family)" then
    match r.kind with
    | "cert" | "profile-cert" => "cert"
    | "refutation" => "refuted"
    | "refutation-family" => "refuted-all"
    | "profile-holds" => if r.status == "LEAN" then "holds" else "holds*"
    | _ => "unsound"
  else if r.status.startsWith "KNOWN-GAP" then "gap"
  else if r.status.startsWith "CONDITIONAL" then "cond"
  else "unsound"

/-- The order of the parts of a cell. -/
def cellOrder : List String :=
  ["cert", "refuted-all", "refuted", "holds", "holds*", "gap", "cond", "unsound"]

/-- A table with box-drawing borders and padded columns. -/
def boxTable (header : List String) (body : List (List String)) : String :=
  let all := header :: body
  let widths := (List.range header.length).map fun j =>
    all.foldl (fun w row => max w (row.getD j "").length) 0
  let rule (l m r : String) :=
    l ++ String.intercalate m (widths.map (fun w => "".pushn '─' (w + 2))) ++ r
  let line (row : List String) :=
    "│" ++ String.intercalate "│" ((row.zip widths).map fun (c, w) =>
      " " ++ c ++ "".pushn ' ' (w - c.length) ++ " ") ++ "│"
  String.intercalate "\n"
    ([rule "┌" "┬" "┐", line header, rule "├" "┼" "┤"] ++ body.map line ++
      [rule "└" "┴" "┘"])

/-- The MATRIX columns: the catalog claims, then the catalog profiles, each
with its `id`. -/
def matrixColumns (env : Environment) : IO (Array (Name × Name)) := do
  let claims ← catalogColumns env ``AvailableChain.Framework.ClaimSpec
    ``AvailableChain.Framework.ClaimSpec.id
  let profiles ← catalogColumns env ``AvailableChain.Framework.Profile
    ``AvailableChain.Framework.Profile.id
  return claims ++ profiles

/-- Why the row `r` has no MATRIX cell, if it has none. -/
def noCell (cols : Array (Name × Name)) (r : Row) : Option String :=
  let what := if r.kind.startsWith "profile" then "profile" else "claim"
  if r.inst == "?" then some "no instance"
  else if !r.col.any (fun c => cols.any (·.1 == c)) then some s!"{what} not in the catalog"
  else none

/-- The text of `docs/MATRIX.md`. -/
def matrixText (env : Environment) (rows : Array Row) (insts : Array Name) : IO String := do
  let cols ← matrixColumns env
  -- An instance of a row that is not an instance constant still gets a line.
  let extra := (rows.map (·.inst)).filter fun s =>
    s != "?" && !insts.any (toString · == s)
  let names := insts.toList.map toString ++ (extra.qsort (· < ·)).toList.eraseDups
  let body := names.map fun inst =>
    inst :: cols.toList.map fun (c, _) =>
      let parts := (rows.filter (fun r => r.inst == inst && r.col == some c)).map cellOf
      let parts := cellOrder.filter parts.contains
      if parts.isEmpty then "·" else String.intercalate "+" parts
  let header := "Instance" :: cols.toList.map (idText ·.2)
  -- The rows without a cell, each with the reason.
  let dropped := rows.toList.filterMap fun r =>
    (noCell cols r).map fun why => s!"- `{r.decl}` ({r.status}): {why}.\n"
  let dropped := if dropped.isEmpty then "Rows without a cell: none.\n"
    else "Rows without a cell:\n\n" ++ String.join dropped
  let libs := String.intercalate ", " (instanceLibraries.map (s!"`{·}`"))
  return "# Matrix (generated by scripts/Registry.lean; do not edit)\n\n" ++
    s!"Scanned libraries: {libs}. The cells come from the rows of `docs/REGISTRY.md`; " ++
    "rows without a cell are listed below the table.\n\n" ++
    "One line per instance: a constant whose type, after its leading binders, is " ++
    "`Instance` or `StrongInstance`. An instance with parameters (`gridInst p`) has " ++
    "one line, by its constant name. A row at a closed instance term " ++
    "(`gridInst smokeParams`, one parameter record) has its own line, by that term. " ++
    "One column per catalog claim, then one column " ++
    "per catalog profile, each by its `id`, in lock order. A row of a pulled claim " ++
    "goes in the column of its base claim. A row of a claim or profile that is not " ++
    "in the catalog has no column.\n\n" ++
    "A cell shows its rows. Only a row with status `LEAN` or `LEAN (family)` gives " ++
    "a result:\n\n" ++
    "- `cert`: a certificate (`cert` or `profile-cert` row).\n" ++
    "- `refuted`: a refutation. `refuted-all`: a refutation family.\n" ++
    "- `holds`: the claim propositions at one constant; no inhabitation; can be " ++
    "vacuous; not a certificate and not a `Candidate`.\n" ++
    "- `holds*`: `holds` from a family row, for every value of its data binder.\n" ++
    "- `gap`: a `KNOWN-GAP` row. `cond`: a `CONDITIONAL` row. `gap` and `cond` " ++
    "cells are records, not results; MATRIX consumers ignore them.\n" ++
    "- `unsound`: a row with any other status.\n" ++
    "- `+` joins the parts of one cell. `·`: no row.\n\n" ++
    "```text\n" ++ boxTable header body ++ "\n```\n\n" ++
    "`*`: a family row. `holds` means the claim propositions at one constant; no " ++
    "inhabitation; can be vacuous; not a certificate and not a `Candidate`.\n\n" ++
    dropped

def registryPath : System.FilePath := "docs/internal/REGISTRY.md"

/-- The default module name of a self-test file. -/
def selftestModule : Name := `RegistrySelfTest
def matrixPath : System.FilePath := "docs/internal/MATRIX.md"

/-- The environment of `instanceLibraries` and `witnessModules`. -/
def loadEnv : IO Environment :=
  importModules ((instanceLibraries ++ witnessModules).map ({ module := · })).toArray {}

/-- Fail (exit 2) on a problem with the witnesses. -/
def checkWitnesses (env : Environment) : IO Unit := do
  let ps ← witnessProblems env
  unless ps.isEmpty do throw (IO.userError (String.intercalate "\n" ps))

/-- The two files and their generated texts. -/
def generated : IO (List (System.FilePath × String)) := do
  let env ← loadEnv
  checkWitnesses env
  let (rows, insts) ← scan env
  return [(registryPath, registryText rows), (matrixPath, ← matrixText env rows insts)]

/-- The expected-output file of a self-test: `<file>.expected` for the default
module, `<file>.<module>.expected` for another module. -/
def expectedPath (file : System.FilePath) (m : Name) : System.FilePath :=
  let stem := file.withExtension ""
  if m == selftestModule then stem.addExtension "expected"
  else (stem.addExtension m.toString).addExtension "expected"

/-- Elaborate `file` as the module `m`, and give one line per row of its own
declarations: the row and its MATRIX cell (or `no cell: <reason>`). -/
def selftestText (file : System.FilePath) (m : Name) : IO String := do
  let input ← IO.FS.readFile file
  -- `runFrontend` imports with environment extensions.
  unsafe enableInitializersExecution
  let some env ← Elab.runFrontend input {} file.toString m
    | throw (IO.userError s!"{file} does not elaborate")
  checkWitnesses env
  let cols ← matrixColumns env
  let mut rows : Array Row := #[]
  for (n, ci) in env.constants.map₂.toList do
    if n.isInternal then continue
    if let some r ← rowOf env n ci m then rows := rows.push r
  let lines := (rows.qsort (·.line < ·.line)).toList.map fun r =>
    let cell := match noCell cols r with
      | some why => s!"no cell: {why}"
      | none => cellOf r
    s!"{r.line} {cell} │\n"
  return String.join lines

/-- Print the self-test lines of `file` as the module `m`, and compare them
with the expected-output file (exit 1 if different). With `write`, write the
expected-output file instead. -/
def selftest (file : System.FilePath) (m : Name) (write : Bool := false) : IO UInt32 := do
  let text ← selftestText file m
  IO.print text
  let path := expectedPath file m
  if write then
    IO.FS.writeFile path text
    return 0
  let old ← try IO.FS.readFile path
    catch e => throw (IO.userError s!"cannot read {path}: {e}")
  if old == text then return 0
  IO.eprintln s!"{path} differs from the self-test output"
  return 1

/-- Write both files. -/
def writeFiles : IO UInt32 := do
  for (path, text) in ← generated do IO.FS.writeFile path text
  return 0

/-- Compare both files with their generated texts; name each file that is
different. -/
def checkFiles : IO UInt32 := do
  let mut code : UInt32 := 0
  for (path, text) in ← generated do
    let old ← try IO.FS.readFile path
      catch e => throw (IO.userError s!"cannot read {path}: {e}")
    unless old == text do
      IO.eprintln s!"{path} differs: run scripts/Registry.lean to write it"
      code := 1
  return code

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let run : IO UInt32 := match args with
    | [] => writeFiles
    | ["--check"] => checkFiles
    | ["--selftest", file] => selftest file selftestModule
    | ["--selftest", file, m] => selftest file m.toName
    | ["--selftest-write", file] => selftest file selftestModule true
    | ["--selftest-write", file, m] => selftest file m.toName true
    | _ => do
        IO.eprintln <| "usage: lake env lean --run scripts/Registry.lean " ++
          "[--check | (--selftest | --selftest-write) <file> [<module>]]"
        return 2
  tryCatch run fun e => do
    IO.eprintln s!"{e}"
    return 2
