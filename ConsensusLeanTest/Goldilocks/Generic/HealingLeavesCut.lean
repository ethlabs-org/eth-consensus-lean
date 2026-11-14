module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt

public section

/-! # Cut guard: the generic healing leaves use no Goldilocks AC

`Lemmas/Generic/HealingLeaves` imports AC-generic run modules by an exception
(`scripts/boundaries.toml`) whose closure reaches `Lemmas.AC`, so the import boundaries do not
keep Goldilocks content out of the leaves. This build-time check does: for every theorem declared
in the module `ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves`, it walks the
constants of the theorem's type and value, and of the type and value of every constant reached,
with the constructors and the inductive of every inductive, constructor and recursor reached, to a
fixpoint, and fails if a reached constant is a Goldilocks-AC constant: one under
`Consensus.Goldilocks.SA` or whose name contains `goldilocksNode`, `GoldilocksTrace` or
`GoldilocksRun`, outside `allowed`. It also fails on a reached name that is not in the
environment, on an empty set of leaves, and on an unused `allowed` entry or one whose own cone
holds another Goldilocks-AC constant.

Controls, so that a broken walk cannot pass: the Goldilocks instance `held_atts_safe_at` must
reach Goldilocks-AC constants, and every leaf's cone must be strictly larger than its cone
without theorem values, so imported proofs are walked. -/

open Lean Meta

namespace Consensus.Goldilocks.Generic.Test.HealingLeavesCut

/-- A Goldilocks-AC constant. -/
meta def goldilocksAC (n : Name) : Bool :=
  let s := n.toString
  (`Consensus.Goldilocks.SA).isPrefixOf n || (s.splitOn "goldilocksNode").length > 1 ||
    (s.splitOn "GoldilocksTrace").length > 1 || (s.splitOn "GoldilocksRun").length > 1

/-- The constants reached from `root`, each with the constant it was reached from; with
`proofs := false`, the values of theorems are not walked. -/
meta def cone (env : Environment) (root : Name) (proofs := true) : Std.HashMap Name Name :=
    Id.run do
  let mut parent : Std.HashMap Name Name := {}
  parent := parent.insert root root
  let mut todo := #[root]
  while h : todo.size > 0 do
    let c := todo.back
    todo := todo.pop
    let mut next : Array Name := #[]
    if let some ci := env.find? c then
      next := next ++ ci.type.getUsedConstants
      if proofs || !ci.isTheorem then
        if let some v := ci.value? (allowOpaque := true) then next := next ++ v.getUsedConstants
      match ci with
      | .inductInfo i => next := next ++ i.ctors.toArray
      | .ctorInfo i => next := next.push i.induct
      | .recInfo i => next := next.push i.getMajorInduct
      | _ => pure ()
    for d in next do
      unless parent.contains d do
        parent := parent.insert d c
        todo := todo.push d
  return parent

/-- The path from `root` to `n` in a cone. -/
meta partial def path (parent : Std.HashMap Name Name) (root n : Name) : List Name :=
  if n == root then [root] else
    match parent.get? n with
    | some p => path parent root p ++ [n]
    | none => [n]

/-- Makes the project's modules findable by name for `importModules`. `lake build` runs Lean with
`LEAN_PATH`; a bare `lean --setup` run (`scripts/lint-syntax.py`) resolves its imports from the
setup file only, so the search path then gets the project's and its packages' build directories,
relative to the repository root, as `lake env` would set them. -/
meta def ensureSearchPath (mod : Name) : IO Unit := do
  try discard <| findOLean mod
  catch _ =>
    let root ← IO.currentDir
    let mut sp : SearchPath := [root / ".lake" / "build" / "lib" / "lean"]
    let pkgs := root / ".lake" / "packages"
    if ← pkgs.isDir then
      for e in ← pkgs.readDir do sp := sp ++ [e.path / ".lake" / "build" / "lib" / "lean"]
    initSearchPath (← findSysroot) sp

/-- The guard: see the module docstring. -/
meta def check (mod : Name) (allowed : List Name) (control : Name × Name) : MetaM Unit := do
  -- A `module` sees only the exported part of its imports, without theorem values, so the walk
  -- runs in an environment imported at the private level, which has them (as `ConstDump`).
  ensureSearchPath mod
  let env ← importModules #[{ module := mod }, { module := control.1 }] {} (trustLevel := 1024)
    (leakEnv := true)
  let some idx := env.getModuleIdx? mod | throwError "module {mod} is not imported"
  let theorems := env.constants.fold (init := #[]) fun acc c info =>
    if env.getModuleIdxFor? c == some idx && !c.isInternal && info.isTheorem then acc.push c
    else acc
  if theorems.isEmpty then throwError "no theorem declared in {mod}"
  let mut used : NameSet := {}
  for t in theorems do
    let parent := cone env t
    for (n, _) in parent.toList do
      unless env.contains n do
        throwError "{t}: reached {n}, which is not in the environment: {path parent t n}"
      if goldilocksAC n then
        if allowed.contains n then used := used.insert n
        else throwError "{t} reaches the Goldilocks-AC constant {n}: {path parent t n}"
  for a in allowed do
    unless used.contains a do throwError "allowed entry {a} is reached by no leaf: remove it"
    let parent := cone env a
    for (n, _) in parent.toList do
      if n != a && goldilocksAC n then
        throwError "allowed entry {a} reaches the Goldilocks-AC constant {n}: {path parent a n}"
  unless (cone env control.2).toList.any (goldilocksAC ·.1) do
    throwError "control {control.2} reaches no Goldilocks-AC constant: the walk is broken"
  for t in theorems do
    unless (cone env t).size > (cone env t (proofs := false)).size do
      throwError "control: the cone of {t} is its cone without theorem values: \
        proofs are not walked"

run_meta do
  let allowed := []
  check `ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves allowed
    (`ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.HeldSafetyAt,
      ``Consensus.Goldilocks.Healing.Growing.held_atts_safe_at)

end Consensus.Goldilocks.Generic.Test.HealingLeavesCut

end
