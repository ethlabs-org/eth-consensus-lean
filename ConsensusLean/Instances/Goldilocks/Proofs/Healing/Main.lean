module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Assembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Recovery
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Assembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Coverage
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ResetInv

public section

/-! # Goldilocks milestone Healing

`HealingACStatements` (H.1, its corollary, H.2) and `HealingRunStatements` (HR.1–HR.4, H.2 (run),
H.3, H.4, `healing_run_statements`) from `Lemmas/Healing/`; H.3's `Inv` half after the reset is
`Lemmas/Healing/ResetInv` (`non_interference`, `T_b = max((8k + 20)Δ, 8Δ)`).

`PhaseServiceStatements` (HS.1–HS.4) is proved too (`phase_service_statements`; HS.3 is the
claims' after-`r` part, `frozen_tree_agreement`). `healing_run_statements_of_nonInterference` is the
run bundle from H.3 as stated.

`RecoveryStatements` (HR.5, O.1 and C1.3) is `recovery_statements`: the actual-report and outcome
suppliers close the bounded high-coverage construction, then the recovery adapter discharges
all three unchanged public statements. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Healing, the AC statements**: H.1, its corollary and H.2. -/
theorem healing_ac_statements : SA.HealingACStatements where
  standalone := SA.ac_healing_standalone
  corollary := SA.ac_healing_standalone_corollary
  inclusion := SA.ac_inclusion

/-! ## The run bundle -/

/-- **The run bundle from H.3** as stated (the other fields are proved). -/
theorem healing_run_statements_of_nonInterference (h3 : NonInterference) :
    HealingRunStatements where
  cutAndReset := cut_and_reset
  phaseCount := phase_count
  resetExistence := reset_existence
  heightScopedRetention := height_scoped_retention
  runInclusion := run_inclusion
  nonInterference := h3
  availableHealing := available_healing

/-- **Healing, the run statements**: HR.1–HR.4, H.2 on the run, H.3 (`non_interference`) and H.4. -/
theorem healing_run_statements : HealingRunStatements :=
  healing_run_statements_of_nonInterference non_interference

/-! ## The phase-service bundle -/

/-- **The phase-service statements** HS.1–HS.4. -/
theorem phase_service_statements : PhaseServiceStatements where
  viableWitnessRetention := viable_witness_retention
  cleanLockDrain := clean_lock_drain
  frozenTreeAgreement := frozen_tree_agreement
  commonPathAcquisition := common_path_acquisition

/-- **Healing Recovery**: HR.5 cache acceptance, O.1 pattern recovery and C1.3 finalizing
coverage, with the actual-report and outcome suppliers discharged. -/
theorem recovery_statements : RecoveryStatements := by
  apply Recovery.recovery_statements_of_coverage
  intro sp ro proposer dg H tr g ΔF Gp W M cF kF
  exact Recovery.pattern_coverage_supply Recovery.outcome_service
    (fun _ => Recovery.ready_proposal_report_supply)

end Consensus.Goldilocks.Healing

end
