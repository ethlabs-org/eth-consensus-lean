import Lean
open Lean

/-! Dump the constants of the given modules for `scripts/const-diff.py`, which compares two dumps
(report-only: did a change alter anything but proofs? `docs/notes/build-speed.md`).

One line per constant declared in a module under one of the given module names, tab-separated:
- name and module;
- kind (`def`, `theorem`, `inductive`, …);
- the universe parameters, by name and in order;
- a hash of the type (`exprHash`: structural, 64 bits; binder names, binder kinds and metadata do not
  count);
- the value: a hash of a definition's or opaque's body, the shape of an inductive (parameters,
  indices, constructors, …), constructor and recursor data (the kernel derives these from the inductive
  and its constructors' types, so they only change with them); `-` for theorems, whose proofs may change;
- safety;
- the axioms it depends on: `collectAxioms`'s walk, done over every copy of each dumped constant
  (below), with Lean's stored answer for the constants of other modules, and over an inductive block
  with its constructors (or a mutual block) at once, so that every member gets the block's union. Lean's
  own walk answers for an inductive according to whether its constructor was walked first (its stored
  answer, what `#print axioms` gives downstream, can lack the constructors' axioms), which a proof-only
  edit elsewhere could flip;
- its scope: `root` for a public name (not an internal detail and not private), `reached` for an
  internal or private constant that a compared constant's type or non-theorem value refers to,
  transitively, with an inductive's constructors and recursors, a compared constant's `implemented_by`
  target and `partial` body (`n._unsafe_rec`), and the field defaults (`S.f._default`, also a child's
  override of an inherited field) of a compared structure `S` except those of `Prop` fields (proofs;
  the declaring structure's projection is a theorem), whose default tactics (`S.f._autoParam`) also get
  value `-`;
  `-` otherwise: an auxiliary or private constant that no compared constant refers to (proofs may use
  it), so a proof change may add, drop or change it.

A theorem (or axiom) that two imported modules both declare with the same type is merged by
`importModules` (`subsumesInfo`), a theorem with an axiom too, and the environment keeps one copy (and
one module's stored axioms) for it. Such a name gets one line, with the first dumped module, and its
axioms, like those of every dumped constant that uses it, are collected over every dumped copy (an axiom
copy counts itself), so a copy in another dumped or undumped module cannot hide one; and a merged name
whose copies' axioms differ is compared (`reached`) even when nothing else refers to it, which covers
users that see it only through a module not dumped.

Usage (imports built; compiled as `lake exe const-dump`, see the lakefile):
`lake exe const-dump <out.tsv> <Module>...` -/

instance : MonadEnv (StateM Environment) where
  getEnv := get
  modifyEnv := modify

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def safety : ConstantInfo → String
  | .defnInfo v => toString (repr v.safety)
  | ci => if ci.isUnsafe then "unsafe" else "safe"

def names (ns : List Name) : String := ",".intercalate (ns.map toString)

def levelHash : Level → UInt64
  | .zero => 3
  | .succ l => mixHash 5 (levelHash l)
  | .max a b => mixHash 7 (mixHash (levelHash a) (levelHash b))
  | .imax a b => mixHash 11 (mixHash (levelHash a) (levelHash b))
  | .param n => mixHash 13 (hash n)
  | .mvar m => mixHash 17 (hash m.name)

/-- A 64-bit structural hash (`Expr.hash` keeps 32 bits), memoised on shared subterms. Binder names,
binder kinds (explicit, implicit, instance) and metadata do not count, as for the kernel; the memo's
key equality (`Expr.eqv`) ignores them too. A reference to an internal theorem of the dumped modules
(`irr`: `foo._proof_1`, `_auxLemma`, private) hashes as one tag, by proof irrelevance: such a proof inside
a definition or statement may change with a proof edit, its type only up to the type its place fixes. -/
partial def exprHash (irr : NameSet) (e : Expr) : StateM (Std.HashMap Expr UInt64) UInt64 := do
  if let some v := (← get)[e]? then return v
  let mix (tag : UInt64) (xs : List UInt64) := xs.foldl mixHash tag
  let v ← match e with
    | .bvar i => pure (mix 19 [hash i])
    | .fvar f => pure (mix 23 [hash f.name])
    | .mvar m => pure (mix 29 [hash m.name])
    | .sort l => pure (mix 31 [levelHash l])
    | .const n ls => pure (if irr.contains n then 71 else mix 37 (hash n :: ls.map levelHash))
    | .app f a => do pure (mix 41 [← exprHash irr f, ← exprHash irr a])
    | .lam _ t b _ => do pure (mix 43 [← exprHash irr t, ← exprHash irr b])
    | .forallE _ t b _ => do pure (mix 47 [← exprHash irr t, ← exprHash irr b])
    | .letE _ t x b nonDep => do pure (mix 53 [← exprHash irr t, ← exprHash irr x, ← exprHash irr b, hash nonDep])
    | .lit (.natVal n) => pure (mix 59 [hash (toString n)])  -- `hash n` is `n` mod 2^64
    | .lit (.strVal s) => pure (mix 61 [hash s])
    | .mdata _ x => exprHash irr x
    | .proj s i x => do pure (mix 67 [hash s, hash i, ← exprHash irr x])
  modify (·.insert e v)
  return v

def h (irr : NameSet) (e : Expr) : String := toString ((exprHash irr e).run' {}).run

/-- What decides the constant beyond its type. Theorems: nothing (proof irrelevance). -/
def value (irr : NameSet) : ConstantInfo → String
  | .defnInfo v => h irr v.value
  | .opaqueInfo v => h irr v.value
  | .inductInfo v => s!"params {v.numParams} indices {v.numIndices} all {names v.all} ctors {names v.ctors} \
      nested {v.numNested} rec {v.isRec} reflexive {v.isReflexive}"
  | .ctorInfo v => s!"{v.induct} {v.cidx} {v.numParams} {v.numFields}"
  | .recInfo v => s!"all {names v.all} {v.numParams} {v.numIndices} {v.numMotives} {v.numMinors} k {v.k} \
      rules {",".intercalate (v.rules.map fun r => s!"{r.ctor}:{r.nfields}:{h irr r.rhs}")}"
  | _ => "-"

/-- Whether `S.f` names a `Prop` field of structure `S`: the projection of the structure that declares `f`
(`S` itself, or a parent for an inherited field that `S` overrides a default of) is a theorem. -/
def isPropField (env : Environment) : Name → Bool
  | .str s f =>
    let decl := (findField? env s (.mkSimple f)).getD s
    (env.find? (decl ++ .mkSimple f) matches some (.thmInfo _))
  | _ => false

/-- The constants whose meaning this one's type and value depend on, and the code that runs for it. -/
def deps (env : Environment) (ci : ConstantInfo) : Array Name :=
  (Compiler.getImplementedBy? env ci.name).toArray ++ match ci with
  | .thmInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.all.toArray ++ v.ctors.toArray ++ v.all.toArray.map mkRecName
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | .recInfo v => v.type.getUsedConstants ++ v.all.toArray ++ v.rules.toArray.flatMap (·.rhs.getUsedConstants)
  | ci => ci.type.getUsedConstants

/-- The constants that refer to each other: an inductive block with its constructors, a mutual block. The
kernel admits no other cycles, so walking each group at once makes every answer independent of the order. -/
def group (env : Environment) (n : Name) : Array Name :=
  let block (all : List Name) := all.toArray ++ all.toArray.flatMap fun i =>
    match env.find? i with | some (.inductInfo v) => v.ctors.toArray | _ => #[]
  match env.find? n with
  | some (.inductInfo v) => block v.all
  | some (.ctorInfo v) => match env.find? v.induct with
    | some (.inductInfo w) => block w.all
    | _ => #[n]
  | some (.defnInfo v) => v.all.toArray
  | some (.thmInfo v) => v.all.toArray
  | some (.opaqueInfo v) => v.all.toArray
  | _ => #[n]

/-- `collectAxioms`'s walk (Lean/Util/CollectAxioms.lean) over every copy of a dumped constant, recursing
through dumped constants and taking Lean's stored answer for the others. Unlike Lean's walk, whose answer for
an inductive depends on whether its constructor was walked first, a group (`group`) is walked at once and
every member gets the union. -/
partial def ownAxioms (env : Environment) (copies : NameMap (Array ConstantInfo))
    (cache : IO.Ref (NameMap NameSet)) (n : Name) : IO NameSet := do
  if let some s := (← cache.get).find? n then return s
  let some _ := copies.find? n | do
    let s := (((collectAxioms n : StateM Environment (Array Name)).run env).1).foldl NameSet.insert {}
    cache.modify (·.insert n s)
    return s
  let members := (group env n).push n
  for m in members do cache.modify (·.insert m {})  -- members met inside the walk add nothing new
  let mut s : NameSet := {}
  for m in members do
    for ci in (copies.find? m).getD #[] do
      for a in ← copyAxioms env copies cache ci do s := s.insert a
  for m in members do cache.modify (·.insert m s)
  return s
where
  /-- One copy's axioms, by the kinds of `CollectAxioms.collect`. -/
  copyAxioms (env copies cache) (ci : ConstantInfo) : IO NameSet := do
    let used := match ci with
      | .axiomInfo v => v.type.getUsedConstants
      | .defnInfo v | .thmInfo v | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
      | .quotInfo _ => #[]
      | .ctorInfo v => v.type.getUsedConstants
      | .recInfo v => v.type.getUsedConstants
      | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
    let mut s : NameSet := if ci matches .axiomInfo _ then ({} : NameSet).insert ci.name else {}
    for d in used do
      for a in ← ownAxioms env copies cache d do s := s.insert a
    return s

unsafe def main (args : List String) : IO UInt32 := do
  let out :: mods@(_ :: _) := args | IO.eprintln "usage: const-dump <out.tsv> <Module>..."; return 2
  initSearchPath (← findSysroot)
  let roots := mods.map String.toName
  -- `loadExts` (with initializers, as in CheckDecls.lean) loads the axiom sets Lean stored for every exported
  -- constant when it wrote each `.olean`; `collectAxioms` reads them instead of walking Mathlib for each constant.
  enableInitializersExecution
  let env ← importModules (roots.toArray.map fun m => { module := m }) {} (loadExts := true) (level := .private)
  -- The constants of the given modules, from each module's data (first module in import order); a name
  -- that several modules declare (merged theorems and axioms, realized `foo.eq_1`) keeps every copy.
  let mut own : Array (Name × Name × ConstantInfo) := #[]
  let mut ownNames : NameSet := {}
  let mut copies : NameMap (Array ConstantInfo) := {}
  for mod in env.header.moduleNames, data in env.header.moduleData do
    if roots.any (·.isPrefixOf mod) then
      for ci in data.constants do
        copies := copies.insert ci.name (((copies.find? ci.name).getD #[]).push ci)
        unless ownNames.contains ci.name do
          own := own.push (ci.name, mod, ci)
          ownNames := ownNames.insert ci.name
  let cache ← IO.mkRef ({} : NameMap NameSet)
  -- internal theorems: proofs, compared neither as constants nor inside a compared expression (their
  -- axioms still count, through `ownAxioms`); a merged one whose copies' axioms differ is still seeded
  let irr : NameSet := own.foldl (init := {}) fun acc (n, _, ci) =>
    if n.isInternalDetail && ci matches .thmInfo _ then acc.insert n else acc
  -- scope: the public names and the merged names whose copies' axioms differ, then everything a compared
  -- type or value refers to, then (until nothing changes) the field defaults and `partial` bodies whose
  -- owner is compared: a child's override `B.x._default` of an inherited field `A.x` has no constant `B.x`
  -- to refer to it, so it goes by its structure `B`; a `Prop` field's default (`S.h` a theorem) is a proof.
  let mut scope : NameMap String := {}
  let mut todo : Array Name := #[]
  for (n, _, _) in own do
    let cs := (copies.find? n).getD #[]
    let differ ← if cs.size ≤ 1 then pure false else do
      let sets ← cs.mapM (ownAxioms.copyAxioms env copies cache)
      pure (sets.any fun t => t.toList.map toString != sets[0]!.toList.map toString)
    if !n.isInternalDetail || differ then
      scope := scope.insert n (if n.isInternalDetail then "reached" else "root")
      todo := todo.push n
  let owner (n : Name) : Option Name := match n with
    | .str field "_default" => if isPropField env field then none else some field.getPrefix
    | .str p "_unsafe_rec" => some p
    | _ => none
  repeat
    while todo.size > 0 do
      let n := todo.back!
      todo := todo.pop
      let some ci := env.find? n | continue
      for d in deps env ci do
        if ownNames.contains d && !irr.contains d && !scope.contains d then
          scope := scope.insert d "reached"
          todo := todo.push d
    for (n, _, _) in own do
      if let some o := owner n then
        if scope.contains o && !scope.contains n then
          scope := scope.insert n "reached"
          todo := todo.push n
    if todo.isEmpty then break
  let mut lines : Array String := #[]
  for (n, mod, ci) in own do
    let axs := (← ownAxioms env copies cache n).toArray
    -- the default tactic of a `Prop` field (`S.f._autoParam`, syntax) is a proof script
    let v := match n with | .str field "_autoParam" => if isPropField env field then "-" else value irr ci | _ => value irr ci
    lines := lines.push <| "\t".intercalate [toString n, toString mod, kind ci, names ci.levelParams,
      h irr ci.type, v, safety ci, ",".intercalate ((axs.map toString).qsort (· < ·)).toList,
      (scope.find? n).getD "-"]
  IO.FS.writeFile out ("\n".intercalate (lines.qsort (· < ·)).toList ++ "\n")
  let merged := own.filter fun (n, _, _) => ((copies.find? n).getD #[]).size > 1
  IO.println s!"{lines.size} constants, {scope.size} compared, {merged.size} declared in several modules"
  return 0
