import Lean
open Lean

/-- Audit every declaration owned by every Consensus module, including tests
and generated declarations. Run after the five-library Lake build:
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
  for name in #[`Consensus.Model.canonical_run, `Consensus.Model.holds_of_injective,
      `Consensus.Model.Run.rehash_trace, `Consensus.System.agree_of_accountable,
      `Consensus.Premise.extremal_realizable, `Consensus.Premise.eval_of_evalAt,
      `Consensus.EnvPoint.two_mul_card_faulty_union_lt,
      `Consensus.ProblemClaims.agree_of_accountable,
      `Consensus.Shape.Tests.Premise.provided_mismatch,
      `Consensus.Shape.Tests.Premise.protected_after_window,
      `Consensus.Model.Run.txHeld_mem_mempool, `Consensus.Model.SelSpec.admits_exists,
      `Consensus.Model.sysOf_laws, `Consensus.Model.Run.selected_of_observed,
      `Consensus.Model.Run.candidates_signer, `Consensus.Model.Run.credentials_of_causal,
      `Consensus.Shape.Tests.Model.forged_role_invalid] do
    unless env.contains name do
      IO.eprintln s!"Missing required theorem: {name}"
      return 2
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
