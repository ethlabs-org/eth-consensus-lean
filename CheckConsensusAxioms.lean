import Lean
open Lean

/-- Audit every declaration owned by every Consensus module under `contract/`,
including tests (`ConsensusShapeTests`, with `Reformulations` and `Index`) and
generated declarations, for axioms outside `propext`, `Classical.choice` and
`Quot.sound`. Name existence is checked by the build (`ConsensusShapeTests/Index`).
Run after the six-library Lake build:
`lake env lean --run contract/CheckConsensusAxioms.lean`. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut modules : Array Name := #[]
  for file in ← (System.FilePath.mk "contract").walkDir do
    if file.extension == some "lean" then
      let parts := (file.withExtension "").components.drop 1
      if parts.head!.startsWith "Consensus" then
        modules := modules.push (parts.foldl Name.str .anonymous)
  if modules.isEmpty then
    IO.eprintln "No Consensus modules found"
    return 2
  let env ← importModules (modules.map ({ module := · })) {}
  let mut checked := 0
  let mut bad := false
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if modules.contains env.header.moduleNames[idx.toNat]! then
        checked := checked + 1
        let axioms ← Core.CoreM.toIO' (collectAxioms name)
          { fileName := "CheckConsensusAxioms", fileMap := .ofString "" } { env := env }
        for ax in axioms do
          unless allowed.contains ax do
            IO.eprintln s!"Unexpected axiom: {name} uses {ax}"
            bad := true
  if checked == 0 then
    IO.eprintln "No Consensus declarations found"
    return 2
  IO.println s!"Audited {checked} declarations across {modules.size} modules; standard axioms only: {!bad}"
  return if bad then 1 else 0
