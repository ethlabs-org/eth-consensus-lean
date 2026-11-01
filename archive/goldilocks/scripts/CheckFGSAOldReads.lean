import Lean
open Lean

/-! FG-SA old-read audit (fg5-rulings STOP 6 and ruling 7, lead 2026-10-02).

The stage-3 switch (J4) moves FG-SA from the old SimplexFG fold to the window
fold. After J4 no old `on_block`, `update_finality`, `acceptViable`,
`HeadFields.ofBlock` or `rowValidFor`, and no FINALITY read of the old
`SimplexFG.derive`, may stay in the ACTIVE FG-SA path. The window fold has
declarations with the same short names (`Window.on_block`, …), so a text search
cannot tell an old read from a new one. This audit reads the COMPILED constants
and matches full names.

Active path: every module of the source directories `AvailableChainFGSA`,
`AvailableChainFGSAClaims`, `AvailableChainFGSAProofs` and
`AvailableChainFGSARun` (and their root files), except modules under a `Tests`
directory.

Read classes of an active declaration (its type and value):
- OLD: it names an old constant (the five STOP-6 names below, plus every
  `old <name>` data line), or it names a constant outside the active path whose
  type, or whose value if it is a definition, names one.
- FINALITY: it contains a finality read of the old derive, or it names a
  constant outside the active path whose type or definition value contains
  one. A finality read of the old derive is a term `(SimplexFG.derive …).F`
  (also `.h_F`, `.finalize`, as a projection or a projection function), or an
  application of a FINALITY FUNCTION to an argument that names
  `SimplexFG.derive`. A finality function is a definition of the AvailableChain
  libraries whose value projects `F`, `h_F` or `finalize` of a `ChainState`, or
  applies another finality function (closed under that rule).
- HEIGHT: it names `SimplexFG.derive` (directly, or through a constant outside
  the active path whose type or definition value names it), and it is not OLD
  or FINALITY.
- HYPOTHESIS: a HEIGHT read confined to binder hypotheses `local = derive …`
  (either direction). The optional `hypothesis` section records these reads.
  Existing `height` entries remain valid for them. OLD and FINALITY take priority.
Also FINALITY (J5 Opus review N7): a finality projector passed as an argument
(`congrArg ChainState.F h`), a beta-redex `(fun σ => σ.F) (derive …)`, a
`ChainState` case split or compiled matcher on derive whose branch uses a finality
field, and a finality read of a local `ChainState` (`σ` with `σ = derive …`) in a
term that names derive. Limit: a matcher on a LOCAL `ChainState` is not matched
(the matcher extension is not loaded, so the discriminant type is unknown).
Auxiliary constants (`foo.proof_1`, `foo.match_1`, `foo.eq_1`, …) count for
their declaration `foo`; a private name counts under its user name.

Data file (default `scripts/baselines/fgsa-old-reads.txt`), one entry per line:
  `allow <declaration> # <reason>`   an OLD or FINALITY read that may stay for now;
  `height <declaration> # <reason>`  a HEIGHT-only read (ruling 7 named exceptions);
  `hypothesis <declaration> # <reason>` a HYPOTHESIS-only read (optional);
  `old <constant> # <reason>`        one more old constant (tightening only);
blank lines and lines that start with `#` are comments. Every entry needs a
reason after ` # `.

Result: every OLD or FINALITY reader needs an `allow` line, every HEIGHT reader
a `height` line. A HYPOTHESIS reader accepts `height` or `hypothesis`. A line
for a declaration with no read of its class (stale), a
duplicate line, or a line in the wrong section fails. So the data only shrinks
with the code (J4: allow lines; J6: height lines).

Run: `lake env lean --run scripts/CheckFGSAOldReads.lean [--data F] [--write]
[--controls]`. `--write` rewrites the data from current reads. It keeps each
reason and each valid optional `hypothesis` entry, and exits 0. `--controls`
also runs the negative controls in the same environment: planted reads (a
direct old constant, an old constant through a KitFG lemma, a
`(SimplexFG.derive …).F` projection, a height-only derive read, and the N7 forms:
congrArg, beta-redex, casesOn, matcher, local name) must each fail as unlisted.
A dropped and an extra data line must also be detected.
Exit codes: 0 pass; 1 an unlisted read, a stale, duplicate or misplaced line,
or a control that is not detected; 2 a usage, data or setup error. -/

def libs : List String :=
  ["AvailableChainFGSA", "AvailableChainFGSAClaims", "AvailableChainFGSAProofs",
    "AvailableChainFGSARun"]

/-- STOP 6 of fg5-rulings. -/
def floorOld : List Name :=
  [`AvailableChain.SimplexFG.on_block, `AvailableChain.SimplexFG.update_finality,
    `AvailableChain.SimplexFG.acceptViable, `AvailableChain.SimplexFG.HeadFields.ofBlock,
    `AvailableChain.FGSA.rowValidFor]

def deriveName : Name := `AvailableChain.SimplexFG.derive
def stateName : Name := `AvailableChain.SimplexFG.ChainState
def finalityFields : List String := ["F", "h_F", "finalize"]

/-- An external lemma about the old fold, for the indirect negative control. -/
def indirectFixture : Name := `AvailableChain.KitFG.on_block_F_mono

/-- Source lookup is owned by the caller's Lake configuration. -/
def layoutOutput (args : Array String) : IO (Array String) := do
  let result ← IO.Process.output { cmd := "python3", args :=
    #["-B", "scripts/source_layout.py", "--root", ".", "--lines"] ++ args }
  unless result.exitCode == 0 do
    throw <| IO.userError s!"source layout failed: {result.stderr}"
  let rows := (result.stdout.splitOn "\n").filter (!·.isEmpty)
  if rows.isEmpty then throw <| IO.userError "source layout returned no paths"
  return rows.toArray

def activeModules : IO (Array Name) := do
  let modules ← layoutOutput (#["modules"] ++ libs.toArray)
  return modules.filterMap fun text =>
    let m := text.toName
    if m.components.contains `Tests then none else some m

def isAuxComp (s : String) : Bool :=
  s.startsWith "_" ||
    ["eq_def", "eq_unfold", "induct", "mutual_induct", "fun_cases", "sizeOf_spec"].contains s ||
    ["proof_", "match_", "eq_", "eqn_", "spec_"].any fun p =>
      s.startsWith p && s.length > p.length && (s.drop p.length).all Char.isDigit

/-- A compiled `match` auxiliary (`foo.match_1`). The matcher extension is not loaded
here, so the name decides. -/
def isMatcherName (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "match_" && (s.drop 6).all Char.isDigit && s.length > 6
  | _ => false

partial def declKey (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  match n with
  | .str p s => if !p.isAnonymous && isAuxComp s then declKey p else n
  | .num p _ => if p.isAnonymous then n else declKey p
  | .anonymous => n

/-- The type, and the value when `withValue` (theorem values included). -/
def exprsOf (ci : ConstantInfo) (withValue : Bool) : Array Expr :=
  match (if withValue then ci.value? (allowOpaque := true) else none) with
  | some v => #[ci.type, v]
  | none => #[ci.type]

def mentionsDerive (e : Expr) : Bool := (e.find? (·.isConstOf deriveName)).isSome

/-- The finality context: the projection functions, the field indices, and the
finality functions. -/
structure FinCtx where
  idx : List Nat
  fns : NameSet
  /-- The number of `ChainState` fields (the binders of a `casesOn` minor premise). -/
  nf : Nat := 0
  /-- The finality functions with a `ChainState` argument (projectors as values). -/
  stateFns : NameSet := {}

/-- `e` projects a finality field of a `ChainState`, or applies a finality function. -/
def projectsFinality (fc : FinCtx) (e : Expr) : Bool :=
  (e.find? fun s =>
    match s with
    | .proj S i _ => S == stateName && fc.idx.contains i
    | .const c _ => fc.fns.contains c
    | _ => false).isSome

/-- A local: a bound or free variable (the `σ` of `σ = derive …`). -/
def isLocal (e : Expr) : Bool := e.consumeMData.isBVar || e.consumeMData.isFVar

def isStateTy (t : Expr) : Bool := t.consumeMData.getAppFn.isConstOf stateName

/-- A projection function of a finality field (`ChainState.F`, `.h_F`, `.finalize`). -/
def isFinalityProjFn (n : Name) : Bool :=
  finalityFields.any fun x => n == stateName ++ Name.mkSimple x

/-- `e` reads a finality field of a local `ChainState`: `σ.F` or `ChainState.F σ`. -/
def readsLocalFinality (fc : FinCtx) (e : Expr) : Bool :=
  (e.find? fun s =>
    match s with
    | .proj S i x => S == stateName && fc.idx.contains i && isLocal x
    | .app .. => s.getAppFn.isConst && isFinalityProjFn s.getAppFn.constName! &&
        s.getAppArgs.any isLocal
    | _ => false).isSome

/-- A lambda over a `ChainState` whose body reads a finality field of a local
(`fun σ => σ.F`). -/
def isStateLam (fc : FinCtx) (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ ty b _ => isStateTy ty && readsLocalFinality fc b
  | _ => false

/-- A finality projector used as a value: a finality projection function, a finality
function with a `ChainState` argument, or a lambda `fun σ => σ.F`. -/
def isFinalityProjector (fc : FinCtx) (e : Expr) : Bool :=
  match e.consumeMData with
  | .const c _ => isFinalityProjFn c || fc.stateFns.contains c
  | f => isStateLam fc f

def isDeriveApp (e : Expr) : Bool := e.consumeMData.getAppFn.isConstOf deriveName

def stripLams : Nat → Expr → Option Expr
  | 0, e => some e
  | k + 1, .lam _ _ b _ => stripLams k b
  | k + 1, .mdata _ b => stripLams (k + 1) b
  | _, _ => none

/-- A `ChainState` recursor (`casesOn`, `rec`, `recOn`) with a major premise that is a
derive application or a local, and a minor premise that uses a finality field binder. -/
def casesReadsFinality (fc : FinCtx) (f : Expr) (args : Array Expr) : Bool :=
  f.isConst && [`casesOn, `rec, `recOn].any (fun r => f.constName! == stateName ++ r) &&
    args.any (fun a => isDeriveApp a || isLocal a) &&
    args.any fun a => match stripLams fc.nf a with
      | some body => fc.idx.any fun i => body.hasLooseBVar (fc.nf - 1 - i)
      | none => false

/-- `e` has a finality read of the old derive. Besides `(derive …).F` and a finality
function applied to a derive argument, it catches (J5 Opus review N7): (a) a finality
projector in argument position of an application with a derive argument
(`congrArg ChainState.F h`); (b) a beta-redex `(fun σ => σ.F) (derive …)`; (c) a
`ChainState` case split on derive or on a local whose minor premise uses a finality
field, and a compiled matcher with a derive discriminant; (d) a finality read of a local
`ChainState` in a term that names derive (`∀ σ, σ = derive … → … σ.F`, also in the type
of an external theorem). A W-state local projects `Window.State`, not `ChainState`, so
(d) does not match it. -/
def finalityRule (fc : FinCtx) (s : Expr) : Option String :=
  match s with
  | .proj S i x =>
      if S == stateName && fc.idx.contains i then
        if mentionsDerive x then some "projection" else if isLocal x then some "local name"
        else none
      else none
  | .app .. =>
      let f := s.getAppFn
      let args := s.getAppArgs
      let derArg := args.any mentionsDerive
      if f.isConst && fc.fns.contains f.constName! && derArg then some "finality function"
      else if f.isConst && isFinalityProjFn f.constName! && args.any isLocal then
        some "local name"
      else if derArg && args.any (isFinalityProjector fc) then some "projector argument"
      else if derArg && isStateLam fc f then some "beta-redex"
      else if casesReadsFinality fc f args then some "case split"
      else if f.isConst && isMatcherName f.constName! && args.any isDeriveApp then some "matcher"
      else none
  | _ => none

/-- The rule of the first finality read of the old derive in `e`, if any. -/
def finalityOfDeriveWhy (fc : FinCtx) (e : Expr) : Option String :=
  if mentionsDerive e then (e.find? (finalityRule fc · |>.isSome)).bind (finalityRule fc)
  else none

def finalityOfDerive (fc : FinCtx) (e : Expr) : Bool := (finalityOfDeriveWhy fc e).isSome

inductive Cls where
  | major | height | hypothesis
  deriving BEq, Inhabited

/-- Only a direct equality to a local qualifies, and only in a binder domain. -/
def isDeriveHypothesis (e : Expr) : Bool :=
  let e := e.consumeMData
  let args := e.getAppArgs
  e.getAppFn.isConstOf ``Eq && args.size == 3 &&
    ((isLocal args[1]! && isDeriveApp args[2]!) ||
      (isDeriveApp args[1]! && isLocal args[2]!))

/-- Keep all other reads, including conclusions and executable terms. -/
partial def mentionsOutsideHypotheses (e : Expr) : Bool :=
  match e with
  | .forallE _ ty b _ | .lam _ ty b _ =>
      (!isDeriveHypothesis ty && mentionsOutsideHypotheses ty) || mentionsOutsideHypotheses b
  | .app f a => mentionsOutsideHypotheses f || mentionsOutsideHypotheses a
  | .letE _ t v b _ =>
      mentionsOutsideHypotheses t || mentionsOutsideHypotheses v || mentionsOutsideHypotheses b
  | .mdata _ b | .proj _ _ b => mentionsOutsideHypotheses b
  | .const n _ => n == deriveName
  | _ => false

structure Read where
  cls : Cls
  why : Array String

/-- The old reads of one active constant. -/
def readsOf (env : Environment) (active : NameSet) (old : NameSet) (fc : FinCtx)
    (ci : ConstantInfo) : Option Read := Id.run do
  let es := exprsOf ci true
  let mut major := #[]
  let mut height := #[]
  let mut hypothesisOnly := true
  if let some w := es.findSome? (finalityOfDeriveWhy fc) then
    major := major.push s!"finality of SimplexFG.derive ({w})"
  else if es.any mentionsDerive then
    height := height.push s!"{deriveName}"
    hypothesisOnly := !es.any mentionsOutsideHypotheses
  let mut seen : NameSet := {}
  for e in es do
    for c in e.getUsedConstants do
      if seen.contains c then continue
      seen := seen.insert c
      if old.contains c then
        major := major.push s!"{c}"
      else if !active.contains c && c != deriveName then
        if let some ce := env.find? c then
          let ces := exprsOf ce (ce matches .defnInfo _)
          let hits := ces.foldl (fun a e => a ++ e.getUsedConstants.filter old.contains) #[]
          if let some h := hits[0]? then
            major := major.push s!"{h} (via {c})"
          else if let some w := ces.findSome? (finalityOfDeriveWhy fc) then
            major := major.push s!"finality of SimplexFG.derive ({w}; via {c})"
          else if ces.any mentionsDerive then
            height := height.push s!"{deriveName} (via {c})"
            hypothesisOnly := hypothesisOnly && !ces.any mentionsOutsideHypotheses
  if !major.isEmpty then return some ⟨.major, major⟩
  if !height.isEmpty then
    return some ⟨if hypothesisOnly then .hypothesis else .height, height⟩
  return none

structure Data where
  allow : Array (Name × String) := #[]
  height : Array (Name × String) := #[]
  hypothesis : Array (Name × String) := #[]
  old : Array (Name × String) := #[]
  bad : Array String := #[]

def parseData (text : String) : Data := Id.run do
  let mut d : Data := {}
  for raw in text.splitOn "\n" do
    let line := raw.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    let (body, reason) := match line.splitOn " # " with
      | b :: r :: rs => (b.trimAscii.toString, (" # ".intercalate (r :: rs)).trimAscii.toString)
      | _ => (line, "")
    let ws := (body.splitOn " ").filter (· ≠ "")
    if reason.isEmpty then d := { d with bad := d.bad.push s!"no reason: {line}" }
    match ws with
    | ["allow", n] => d := { d with allow := d.allow.push (n.toName, reason) }
    | ["height", n] => d := { d with height := d.height.push (n.toName, reason) }
    | ["hypothesis", n] => d := { d with hypothesis := d.hypothesis.push (n.toName, reason) }
    | ["old", n] => d := { d with old := d.old.push (n.toName, reason) }
    | _ => d := { d with bad := d.bad.push s!"bad line: {line}" }
  return d

/-- Unlisted reads, and stale, duplicate or misplaced lines. -/
def compare (reads : Std.HashMap Name Read) (allow height : Array Name)
    (hypothesis : Array Name := #[]) :
    Array String × Array String := Id.run do
  let mut unlisted := #[]
  for (k, r) in reads.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    match r.cls with
    | .major =>
        unless allow.contains k do
          unlisted := unlisted.push s!"OLD READ NOT LISTED (allow): {k} reads {r.why.toList}"
    | .height =>
        unless height.contains k do
          unlisted := unlisted.push s!"OLD READ NOT LISTED (height): {k} reads {r.why.toList}"
    | .hypothesis =>
        unless height.contains k || hypothesis.contains k do
          unlisted := unlisted.push s!"OLD READ NOT LISTED (hypothesis): {k} reads {r.why.toList}"
  let mut stale := #[]
  let mut seen : NameSet := {}
  for (sect, ks, cls) in [("allow", allow, Cls.major), ("height", height, Cls.height),
      ("hypothesis", hypothesis, Cls.hypothesis)] do
    for k in ks do
      if seen.contains k then stale := stale.push s!"DUPLICATE LINE: {k}"
      seen := seen.insert k
      match reads[k]? with
      | none => stale := stale.push s!"STALE {sect} LINE (no old read now; remove it): {k}"
      | some r =>
          unless r.cls == cls || (cls == .height && r.cls == .hypothesis) do
            stale := stale.push s!"MISPLACED {sect} LINE (move it to the other section): \
              {k} reads {r.why.toList}"
  return (unlisted, stale)

def header : String :=
  "# FG-SA old-read audit data (scripts/CheckFGSAOldReads.lean; fg5-rulings STOP 6, ruling 7).\n\
   # allow <declaration> # <reason>: an old-constant or old-derive FINALITY read \
   that may stay for now (J4 removes).\n\
   # height <declaration> # <reason>: a height-only read of the old derive \
   (ruling 7 named exceptions; J6 removes).\n\
   # hypothesis <declaration> # <reason>: an optional hypothesis-only derive read.\n\
   # old <constant> # <reason>: one more old constant (tightening only).\n\
   # An unlisted read fails; a stale, duplicate or misplaced line fails.\n"

/-- The finality functions: a fixpoint over the definitions of the AvailableChain libraries.
A definition that BUILDS a `ChainState` (its type ends in `ChainState`: the fold steps,
`transition`, `derive`) is never a finality function: it writes the fields, it does not
read them out, and the fold is matched at its application sites instead. -/
def finalityFns (env : Environment) (idx : List Nat) : NameSet := Id.run do
  let mut fns : NameSet :=
    finalityFields.foldl (fun s f => s.insert (stateName ++ Name.mkSimple f)) {}
  let buildsState (t : Expr) : Bool := t.getForallBody.getAppFn.isConstOf stateName
  let defs := env.constants.toList.filterMap fun (n, ci) =>
    match ci with
    | .defnInfo d =>
        if (`AvailableChain).isPrefixOf n && !buildsState d.type then some (n, d.value) else none
    | _ => none
  let mut changed := true
  while changed do
    changed := false
    for (n, v) in defs do
      if fns.contains n then continue
      if projectsFinality { idx, fns } v then
        fns := fns.insert n
        changed := true
  return fns

def main (args : List String) : IO UInt32 := do
  let usage := "USAGE: lake env lean --run scripts/CheckFGSAOldReads.lean \
    [--data F] [--write] [--controls] [--list-fns]"
  let mut rest := args
  let mut path : System.FilePath := "scripts/baselines/fgsa-old-reads.txt"
  let mut write := false
  let mut controls := false
  let mut listFns := false
  while !rest.isEmpty do
    match rest with
    | "--data" :: f :: r => path := f; rest := r
    | "--write" :: r => write := true; rest := r
    | "--controls" :: r => controls := true; rest := r
    | "--list-fns" :: r => listFns := true; rest := r
    | _ => IO.eprintln usage; return 2
  let data := parseData (← IO.FS.readFile path)
  unless data.bad.isEmpty do
    for b in data.bad do IO.println s!"DATA ERROR: {b}"
    return 2
  let mods ← activeModules
  initSearchPath (← findSysroot)
  let env ← importModules (mods.map ({ module := · })) {}
  let modSet : NameSet := mods.foldl (·.insert ·) {}
  let isActive (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some idx => modSet.contains env.header.moduleNames[idx.toNat]!
    | none => false
  let mut old : NameSet := {}
  for n in floorOld do
    if env.contains n then old := old.insert n
    else IO.println s!"note: old constant {n} is absent (nothing can read it)"
  for (n, _) in data.old do
    unless env.contains n do
      IO.println s!"DATA ERROR: old constant {n} does not exist"
      return 2
    old := old.insert n
  unless env.contains deriveName do
    IO.println s!"SETUP ERROR: {deriveName} does not exist"
    return 2
  unless isStructure env stateName do
    IO.println s!"SETUP ERROR: {stateName} is not a structure"; return 2
  let fields := (getStructureFields env stateName).toList
  let idx := finalityFields.filterMap fun f => fields.findIdx? (· == Name.mkSimple f)
  unless idx.length == finalityFields.length do
    IO.println s!"SETUP ERROR: {stateName} lacks a finality field {finalityFields}"
    return 2
  let fns := finalityFns env idx
  let stateFns := fns.toList.foldl (fun acc c => match env.find? c with
    | some ci => if (ci.type.getForallBinderNames.length > 0) &&
        (Id.run do
          let mut t := ci.type
          let mut hit := false
          while t.isForall do
            if isStateTy t.bindingDomain! then hit := true
            t := t.bindingBody!
          return hit) then acc.insert c else acc
    | none => acc) {}
  let fc : FinCtx := ⟨idx, fns, fields.length, stateFns⟩
  if listFns then
    for n in fc.fns.toList.toArray.qsort (fun a b => a.toString < b.toString) do
      let m := match env.getModuleIdxFor? n with
        | some i => s!"{env.header.moduleNames[i.toNat]!}" | none => "?"
      IO.println s!"finality function {n} ({m})"
    return 0
  let cs := env.constants.toList.filter (fun (n, _) => isActive n)
  if cs.isEmpty then
    IO.eprintln "NO ACTIVE CONSTANTS FOUND"
    return 2
  let active : NameSet := cs.foldl (fun s (n, _) => s.insert n) {}
  let mut reads : Std.HashMap Name Read := {}
  let mut home : Std.HashMap Name Name := {}
  for (_, ci) in cs do
    if let some r := readsOf env active old fc ci then
      let k := declKey ci.name
      let r := match reads[k]? with
        | some r0 =>
            ⟨if r0.cls == .major || r.cls == .major then .major
              else if r0.cls == .height || r.cls == .height then .height else .hypothesis,
              r0.why ++ r.why⟩
        | none => r
      reads := reads.insert k r
      if let some i := env.getModuleIdxFor? ci.name then
        home := home.insert k env.header.moduleNames[i.toNat]!
  let allow := data.allow.map (·.1)
  let height := data.height.map (·.1)
  let hypothesis := data.hypothesis.map (·.1)
  let nMajor := (reads.toArray.filter (·.2.cls == .major)).size
  IO.println s!"scanned {cs.length} constants of {mods.size} active modules; {old.size} old \
    constants; {fc.fns.size} finality functions; {nMajor} old/finality readers, \
    {reads.size - nMajor} height-only readers; {allow.size} allow and {height.size} height lines"
  if write then
    let keep : Std.HashMap Name String :=
      (data.allow ++ data.height ++ data.hypothesis).foldl (fun m (n, r) => m.insert n r) {}
    let mut out := header
    for (n, r) in data.old do out := out ++ s!"old {n} # {r}\n"
    let ks := (reads.toArray.map (·.1)).qsort (fun a b => a.toString < b.toString)
    for sect in ["allow", "height", "hypothesis"] do
      for k in ks do
        let some r := reads[k]? | continue
        let targetSection := if r.cls == .major then "allow"
          else if r.cls == .hypothesis && hypothesis.contains k then "hypothesis" else "height"
        unless sect == targetSection do continue
        let rsn := keep.getD k s!"pre-J4 baseline 2026-10-02 ({home.getD k .anonymous})"
        out := out ++ s!"{sect} {k} # {rsn}\n"
    IO.FS.writeFile path out
    IO.println s!"wrote {path}"
    return 0
  let (unlisted, stale) := compare reads allow height hypothesis
  for s in unlisted ++ stale do IO.println s
  let mut failed := !(unlisted.isEmpty && stale.isEmpty)
  if controls then
    let some o := floorOld.find? env.contains | do
      IO.println "CONTROL SETUP FAIL: no old constant exists"; return 2
    unless env.contains indirectFixture do
      IO.println s!"CONTROL SETUP FAIL: {indirectFixture} does not exist"
      return 2
    let mk (n : Name) (v : Expr) : ConstantInfo :=
      ConstantInfo.defnInfo
        { name := n
          levelParams := []
          type := mkConst `Nat
          value := v
          hints := .opaque
          safety := .safe }
    let some mName := env.constants.toList.findSome? (fun (n, _) =>
        if isMatcherName n && (`AvailableChain).isPrefixOf n then some n else none) | do
      IO.println "CONTROL SETUP FAIL: no matcher exists"; return 2
    let der := mkApp (mkConst deriveName) (mkConst `Nat)
    let fIdx := idx.head!
    let hypothesisRead := mk `OldReadControl.hypothesisOnly
      (.forallE `σ (mkConst stateName)
        (.forallE `h (mkApp3 (mkConst ``Eq [1]) (mkConst stateName) (.bvar 0) der)
          (mkConst ``True) .default) .default)
    let planted : List (ConstantInfo × Cls) :=
      [(mk `OldReadControl.direct (mkConst o), .major),
        (mk `OldReadControl.indirect (mkConst indirectFixture), .major),
        (mk `OldReadControl.finalityProj (.proj stateName fIdx der), .major),
        (mk `OldReadControl.finalityFn
          (mkApp2 (mkConst (stateName ++ `F)) (mkConst `Nat) der), .major),
        (mk `OldReadControl.heightOnly der, .height),
        (hypothesisRead, .hypothesis),
        -- J5 Opus review N7 (a): a finality projector in argument position.
        (mk `OldReadControl.congrArgF
          (mkAppN (mkConst `congrArg [1, 1]) #[mkConst stateName, mkConst `Nat, der, der,
            mkConst (stateName ++ `F), mkConst `rfl]), .major),
        -- N7 (b): a beta-redex `(fun σ => σ.F) (derive …)`.
        (mk `OldReadControl.betaRedex
          (mkApp (.lam `σ (mkConst stateName) (.proj stateName fIdx (.bvar 0)) .default) der),
          .major),
        -- N7 (c): `ChainState.casesOn (derive …)` with a minor premise that uses `F`.
        (mk `OldReadControl.casesOnF
          (mkAppN (mkConst (stateName ++ `casesOn) [1]) #[mkConst `Nat, der,
            (List.range fields.length).foldl (fun b _ => .lam `x (mkConst `Nat) b .default)
              (.bvar (fields.length - 1 - fIdx))]), .major),
        -- N7 (c): a matcher with a `derive …` discriminant.
        (mk `OldReadControl.matcher
          (mkAppN (mkConst mName) #[mkConst `Nat, der]), .major),
        -- N7 (d): a local name, `∀ σ, σ = derive … → … σ.F`.
        (mk `OldReadControl.localName
          (.forallE `σ (mkConst stateName)
            (.forallE `h (mkApp3 (mkConst `Eq [1]) (mkConst stateName) (.bvar 0) der)
              (mkApp3 (mkConst `Eq [1]) (mkConst `Nat) (.proj stateName fIdx (.bvar 1))
                (.proj stateName fIdx (.bvar 1))) .default) .default), .major)]
    let mut withPlanted := reads
    for (ci, cls) in planted do
      match readsOf env active old fc ci with
      | some r =>
          withPlanted := withPlanted.insert ci.name r
          unless r.cls == cls do
            IO.println s!"NEGATIVE CONTROL WRONG CLASS: {ci.name}"
            failed := true
      | none =>
          IO.println s!"NEGATIVE CONTROL NOT DETECTED: {ci.name} is not an old read"
          failed := true
    let (u, _) := compare withPlanted allow height hypothesis
    for (ci, _) in planted do
      if u.any (fun s => (s.splitOn s!": {ci.name} reads").length > 1) then
        IO.println s!"control planted {ci.name}: detected"
      else
        IO.println s!"NEGATIVE CONTROL NOT DETECTED: planted {ci.name}"
        failed := true
    for (sect, ks) in [("allow", allow), ("height", height)] do
      if let some first := ks[0]? then
        let (u, _) := if sect == "allow" then compare reads (allow.erase first) height hypothesis
          else compare reads allow (height.erase first) hypothesis
        if u.any (fun s => (s.splitOn s!": {first} reads").length > 1) then
          IO.println s!"control dropped {sect} line {first}: detected"
        else
          IO.println s!"NEGATIVE CONTROL NOT DETECTED: dropped {sect} line {first}"
          failed := true
      else
        IO.println s!"control dropped {sect} line: skipped (no {sect} lines)"
    let (_, st) := compare reads (allow.push `OldReadControl.stale) height hypothesis
    if st.any (·.endsWith "OldReadControl.stale") then
      IO.println "control stale allow line: detected"
    else
      IO.println "NEGATIVE CONTROL NOT DETECTED: stale allow line"
      failed := true
    -- A hypothesis entry must not accept a value/conclusion or a finality read.
    for n in [`OldReadControl.heightOnly, `OldReadControl.localName] do
      let (u, st) := compare withPlanted allow height (hypothesis.push n)
      if u.any (·.contains n.toString) &&
          st.any (·.startsWith "MISPLACED hypothesis LINE") then
        IO.println s!"control misplaced hypothesis {n}: detected"
      else
        IO.println s!"NEGATIVE CONTROL NOT DETECTED: misplaced hypothesis {n}"
        failed := true
    let k := hypothesisRead.name
    let only := withPlanted.filter fun n _ => n == k
    for (hs, hyps) in [(#[k], #[]), (#[], #[k])] do
      let (u, st) := compare only #[] hs hyps
      unless u.isEmpty && st.isEmpty do
        IO.println "POSITIVE CONTROL FAILED: height/hypothesis compatibility"
        failed := true
    let (_, duplicate) := compare only #[] #[k] #[k]
    let (_, misplaced) := compare reads allow height (hypothesis.push `OldReadControl.stale)
    if duplicate.any (·.startsWith "DUPLICATE LINE") &&
        misplaced.any (·.startsWith "STALE hypothesis LINE") then
      IO.println "control duplicate/stale hypothesis: detected"
    else
      IO.println "NEGATIVE CONTROL NOT DETECTED: duplicate/stale hypothesis"
      failed := true
  IO.println s!"FGSA old-read audit: {if failed then "FAIL" else "PASS"}"
  return if failed then 1 else 0
