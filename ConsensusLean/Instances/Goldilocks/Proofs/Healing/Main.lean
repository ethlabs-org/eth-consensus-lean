module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Assembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Service

public section

/-! # Goldilocks milestone Healing

`HealingACStatements` (H.1, its corollary, H.2) and `HealingRunStatements` (HR.1–HR.4,
H.2 (run), H.3, H.4) and `PhaseServiceStatements` (HS.1–HS.4) from `Lemmas/Healing/`. -/

namespace Consensus.Goldilocks.Healing

/-- **Healing, the AC statements**: H.1, its corollary and H.2. -/
theorem healing_ac_statements : SA.HealingACStatements where
  standalone := SA.ac_healing_standalone
  corollary := SA.ac_healing_standalone_corollary
  inclusion := SA.ac_inclusion

/-- **Healing, the run statements**: HR.1–HR.4, H.2 (run), H.3 and H.4. -/
theorem healing_run_statements : HealingRunStatements where
  cutAndReset := cut_and_reset
  phaseCount := phase_count
  resetExistence := reset_existence
  heightScopedRetention := height_scoped_retention
  runInclusion := run_inclusion
  nonInterference := non_interference
  availableHealing := available_healing

/-- **Healing, the phase-service statements**: HS.1–HS.4. -/
theorem phase_service_statements : PhaseServiceStatements where
  viableWitnessRetention := viable_witness_retention
  cleanLockDrain := clean_lock_drain
  frozenTreeAgreement := frozen_tree_agreement
  commonPathAcquisition := common_path_acquisition

end Consensus.Goldilocks.Healing

end
