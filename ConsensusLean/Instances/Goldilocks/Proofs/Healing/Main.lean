module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Inclusion
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Assembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Coverage
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports

public section

/-! # Goldilocks milestone Healing

`HealingACStatements` (H.1, H.2; H.1's corollary is `ac_healing_standalone_corollary`) from
`Lemmas/Healing/`. The run-level bundle (HR.1–HR.4, H.2 (run), H.3, H.4) and the phase-service
bundle (HS.1–HS.4) are retired; the lemmas the recovery proofs read stay in `Lemmas/Healing/`.

`RecoveryStatements` (HR.5, O.1 and C1.3) is `recovery_statements`: the actual-report and outcome
suppliers close the bounded high-coverage construction, then the recovery adapter discharges
all three unchanged public statements.

These bundles package proved milestone lemmas, not separate `Challenge` roots. Their fields
are pinned by `ConsensusLeanTest/MilestoneAxioms.lean`; `Challenge` certifies eight statements: the
five generic review statements and the Goldilocks statements of `Statements/Obligations`.
See `docs/decisions.md`, "Trusted surface and Challenge scope". -/

namespace Consensus.Goldilocks.SA

/-- The AC-level statements of milestone Healing (H.1, H.2), for population-sized committees.
H.1's corollary follows from H.1 (`corollary_of_standalone`), so it is not a field. -/
structure HealingACStatements : Prop where
  standalone : ∀ sp : SAParams, sp.committeeSize = sp.n → ACHealingStandalone (sp := sp)
  inclusion : ∀ sp : SAParams, sp.committeeSize = sp.n → ACInclusion (sp := sp)

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Healing, the AC statements**: H.1 and H.2. -/
theorem healing_ac_statements : SA.HealingACStatements where
  standalone := SA.ac_healing_standalone
  inclusion := SA.ac_inclusion

/-- **Healing Recovery**: HR.5 cache acceptance, O.1 pattern recovery and C1.3 finalizing
coverage, with the actual-report and outcome suppliers discharged. -/
theorem recovery_statements : RecoveryStatements := by
  apply Recovery.recovery_statements_of_coverage
  intro sp ro proposer dg H tr g ΔF Gp W M cF kF
  exact Recovery.pattern_coverage_supply Recovery.outcome_service
    (fun _ => Recovery.ready_proposal_report_supply)

end Consensus.Goldilocks.Healing

end
