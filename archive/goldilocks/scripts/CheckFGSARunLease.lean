import AvailableChainFGSARun
import AvailableChainCheckSupport.GeneratedOwner
import Lean
open Lean Meta AvailableChainCheckSupport

/-! FGSA run-library lease-instance check (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` §3.1, T7.1). A copy of
`scripts/CheckFGSALease.lean` with other scanned roots: the modules of
`AvailableChainFGSARun` (not those of `AvailableChainFGSA`, which the store
check scans). The store definitions that the run library reaches are
inspected imported definitions here. The rules are the rules of the store
check. The SA base runs GridCO with `GridCO.slowLeasePolicy`. A parameter is a
policy parameter if its type, reduced by `whnf` with ALL transparency, is
`GridCO.LeasePolicy` (so an alias of the type is caught, also an
`@[irreducible]` one).

Scanned (the types and values of these constants; the value of a theorem is its
proof, so theorem proofs are scanned too, which is stricter than soundness
needs, on purpose):
- every compiled constant of the modules of `AvailableChainFGSARun` (and of each
  extra root module `M` on the command line), except the equation lemmas that
  Lean generates for a definition of another library (see "Skipped");
- inspected imported definitions: every definition in a namespace
  `AvailableChain.*` (tested on the name without its `private` prefix) of a
  module outside the scanned roots that a scanned constant reaches, directly or
  through the values of other inspected definitions.

Rules:
- A scanned constant must not have a policy parameter. The run library never
  needs a policy-generic declaration, so a wrapper with its own policy
  parameter in a run-library module fails, whatever its namespace or name
  (also a `private` one).
- In a scanned constant, every argument at a policy position of an applied
  constant must be the constant `GridCO.slowLeasePolicy`. The default instance
  `gridLeasePolicy`, any other term, a bound variable, a partial use and an
  unapplied use fail.
- In an inspected imported definition, a policy argument may also be one of the
  definition's OWN policy parameters (a leading binder of its type or value
  whose type is a policy type). A variable that a `let` or a `fun` inside the
  body binds fails. So an imported wrapper that fixes `gridLeasePolicy` inside
  (directly, through a `let`, through a beta-redex, or through a private
  helper) and that the run library reaches fails.
- Reachability backstop: in the closure of the scanned constants (types and
  values of every reached constant, all namespaces, private names included;
  the proofs of imported theorems excluded), no constant may mention
  `GridCO.gridLeasePolicy`, and only the value of `GridCO.slowLeasePolicy` may
  mention the constructor `GridCO.LeasePolicy.mk`.

Trusted, not inspected by the argument rules: the proofs of imported theorems
(their statements reach the scanned roots only through the arguments at each
use, which the rules check), and definitions outside the namespace `AvailableChain` (Lean
core, Batteries, Mathlib: they do not mention GridCO). The backstop covers
these definitions too.

Skipped: a generated constant (an equation `eq_<k>` or `eq_def`, a matcher
splitter or congruence equation, a sparse `casesOn` or its fallback equation,
also with a private name) whose owner is a definition declared in a module
outside the scanned roots (for example `GridCO.recordGenuine.eq_1`, which Lean
realizes in a run-library module when a proof there unfolds `recordGenuine`).
The owner comes from `AvailableChainCheckSupport.generatedOwner`
(`scripts/AvailableChainCheckSupport/GeneratedOwner.lean`): the private prefix
and the generated last components are stripped until the name is declared. Its
policy is a bound variable, and each use of it is checked at the use. Its owner
is inspected as an imported definition (the equation states the body of that
definition). Lean reserves these names: a user declaration cannot have one.

It checks BUILT data, as `scripts/CheckFGSARunAxioms.lean`: run
`lake build AvailableChainFGSARun` first, or use
`bash scripts/check-fgsa-run.sh`.

Run: `lake env lean --run scripts/CheckFGSARunLease.lean [M …]`. Each optional
`M` is one more root module to import and scan (the negative controls in
`check-fgsa-run.sh` use this).
Exit codes: 0 clean; 1 a bad use; 2 nothing found. -/

def policyName : Name := `AvailableChain.GridCO.LeasePolicy
def slowName : Name := `AvailableChain.GridCO.slowLeasePolicy
def gridName : Name := `AvailableChain.GridCO.gridLeasePolicy
def mkName : Name := `AvailableChain.GridCO.LeasePolicy.mk

def moduleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

def inRoots (roots : List Name) (env : Environment) (n : Name) : Bool :=
  match moduleOf env n with
  | some m => roots.any (·.isPrefixOf m)
  | none => false

/-- A generated constant of a definition of another library, with its owner
(`AvailableChainCheckSupport.generatedOwner`: the private prefix and the
generated last components stripped). -/
def generatedEqn (roots : List Name) (env : Environment) (n : Name) : Option Name :=
  generatedOfOther env (inRoots roots env) n

/-- A policy type: `GridCO.LeasePolicy` after `whnf` with all transparency. -/
def isPolicyType (t : Expr) : MetaM Bool :=
  withTransparency .all do return (← whnf t).isConstOf policyName

/-- The positions of the policy parameters of a constant (types reduced with
all transparency). -/
def leasePositions (ci : ConstantInfo) : MetaM (Array Nat) :=
  withTransparency .all <| forallTelescopeReducing ci.type fun xs _ => do
    let mut out := #[]
    for i in [0:xs.size] do
      if ← isPolicyType (← inferType xs[i]!) then out := out.push i
    return out

structure Scan where
  cache : Std.HashMap Name (Array Nat) := {}
  seen : Std.HashSet Expr := {}
  bad : Array String := #[]
  uses : Nat := 0
  reached : Std.HashSet Name := {}
  /-- The own policy parameters of the inspected imported definition. -/
  own : Array Expr := #[]

def posOf (c : Name) : StateT Scan MetaM (Array Nat) := do
  if let some ps := (← get).cache[c]? then return ps
  let ps ← match (← getEnv).find? c with
    | some ci => leasePositions ci
    | none => pure #[]
  modify fun s => { s with cache := s.cache.insert c ps }
  return ps

def report (msg : String) : StateT Scan MetaM Unit :=
  modify fun s => { s with bad := s.bad.push msg }

def note (c : Name) : StateT Scan MetaM Unit :=
  modify fun s => { s with reached := s.reached.insert c }

/-- Scan `e`, a part of a type or value of `owner`. A policy argument is valid
if it is `slowLeasePolicy` or one of the owner's own policy parameters
(`Scan.own`, empty for a scanned constant). -/
partial def scan (owner : Name) (e : Expr) : StateT Scan MetaM Unit := do
  if (← get).seen.contains e then return
  modify fun s => { s with seen := s.seen.insert e }
  match e with
  | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const c _ := f then
        note c
        for i in ← posOf c do
          modify fun s => { s with uses := s.uses + 1 }
          if h : i < args.size then
            let a := args[i]
            unless a.isConstOf slowName || (← get).own.contains a do
              report s!"{owner}: {c} at {a}"
          else
            report s!"{owner}: {c} (partial)"
      else scan owner f
      for a in args do scan owner a
  | .const c _ =>
      note c
      unless (← posOf c).isEmpty do report s!"{owner}: {c} (unapplied)"
  | .lam _ t b _ | .forallE _ t b _ => do scan owner t; scan owner b
  | .letE _ t v b _ => do scan owner t; scan owner v; scan owner b
  | .mdata _ b | .proj _ _ b => scan owner b
  | _ => pure ()

/-- The policy-typed variables among `xs`. -/
def policyVars (xs : Array Expr) : MetaM (Array Expr) :=
  xs.filterM fun x => do isPolicyType (← inferType x)

/-- Scan a type or value after opening its leading binders. With `generic`, the
policy-typed leading binders are the owner's own policy parameters. The binder
types are scanned too. -/
def scanOpen (owner : Name) (generic : Bool) (lam : Bool) (e : Expr) :
    StateT Scan MetaM Unit := do
  let go : Array Expr → Expr → StateT Scan MetaM Unit := fun xs body => do
    let own ← if generic then policyVars xs else pure #[]
    modify fun s => { s with own }
    for x in xs do scan owner (← inferType x)
    scan owner body
  let st ← get
  let ((), st') ← (if lam then lambdaTelescope e fun xs b => (go xs b).run st
    else forallTelescope e fun xs b => (go xs b).run st : MetaM _)
  set { st' with own := #[] }

def scanConst (owner : Name) (generic : Bool) (ci : ConstantInfo) :
    StateT Scan MetaM Unit := do
  modify fun s => { s with seen := {} }
  scanOpen owner generic false ci.type
  if let some v := ci.value? (allowOpaque := true) then
    modify fun s => { s with seen := {} }
    scanOpen owner generic true v

/-- The backstop: the closure of `start` through types and values (not the
proofs of imported theorems). Reports every reached constant that mentions
`gridLeasePolicy`, and every one other than `slowLeasePolicy` that mentions
`LeasePolicy.mk`. Returns the reports and the number of reached constants. -/
def backstop (env : Environment) (inRoot : Name → Bool) (start : List Name) :
    Array String × Nat := Id.run do
  let mut todo := start.toArray
  let mut seen : NameSet := {}
  let mut bad := #[]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    let some ci := env.find? c | continue
    let mut used := ci.type.getUsedConstants
    unless !inRoot c && ci matches .thmInfo _ do
      if let some v := ci.value? (allowOpaque := true) then used := used ++ v.getUsedConstants
    if used.contains gridName then bad := bad.push s!"{c}: mentions {gridName} (reach)"
    if c != slowName && used.contains mkName then bad := bad.push s!"{c}: mentions {mkName} (reach)"
    for u in used do
      unless seen.contains u do todo := todo.push u
  return (bad, seen.size)

def main (args : List String) : IO UInt32 := do
  let extra := args.map String.toName
  let roots := `AvailableChainFGSARun :: extra
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map ({ module := · })) {}
  let cs := env.constants.toList.filter (fun (n, _) => inRoots roots env n)
  if cs.isEmpty then
    IO.eprintln "NO CONSTANTS FOUND"
    return 2
  let run : MetaM (Scan × Nat × Nat) := do
    let mut st : Scan := {}
    let mut skipped := 0
    for (n, ci) in cs do
      if let some o := generatedEqn roots env n then
        -- The equation states the body of its definition: inspect that body.
        skipped := skipped + 1
        st := { st with reached := st.reached.insert o }
        continue
      let ((), st') ← (do
        unless (← posOf ci.name).isEmpty do
          report s!"{n}: has a policy parameter (a policy-generic declaration in the run library)"
        scanConst n false ci).run st
      st := st'
    -- Inspect the imported `AvailableChain.*` definitions that the scanned roots reach.
    let mut done : Std.HashSet Name := {}
    let mut inspected := 0
    let mut todo := st.reached.toList
    while !todo.isEmpty do
      let c := todo.head!
      todo := todo.tail!
      if done.contains c then continue
      done := done.insert c
      let user := (privateToUserName? c).getD c
      if !(`AvailableChain).isPrefixOf user || inRoots roots env c then continue
      match env.find? c with
      | some ci@(.defnInfo _) =>
          inspected := inspected + 1
          let ((), st') ← (scanConst c true ci).run { st with reached := {} }
          todo := todo ++ st'.reached.toList
          st := st'
      | _ => pure ()
    return (st, skipped, inspected)
  let (st, skipped, inspected) ← run.run' {} |>.toIO'
    { fileName := "CheckFGSARunLease", fileMap := .ofString "" } { env := env }
  let (reach, nReach) := backstop env (inRoots roots env) (cs.map (·.1))
  for b in st.bad ++ reach do IO.println s!"BAD LEASE INSTANCE {b}"
  IO.println s!"checked {cs.length - skipped} constants ({skipped} generated equation \
    lemmas skipped), {inspected} imported definitions inspected, {st.uses} lease arguments, \
    {nReach} constants reached (backstop)"
  return if st.bad.isEmpty && reach.isEmpty then 0 else 1
