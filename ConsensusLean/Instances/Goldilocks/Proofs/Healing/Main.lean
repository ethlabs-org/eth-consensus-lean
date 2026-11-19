module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Recovery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Assembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Coverage
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports

public section

/-! # Goldilocks milestone Healing

The run-level bundle (HR.1–HR.4, H.2 (run), H.3, H.4) and the phase-service
bundle (HS.1–HS.4) are retired; the lemmas the recovery proofs read stay in `Lemmas/Healing/`.

`RecoveryStatements` (HR.5, O.1 and C1.3) is `recovery_statements`: the actual-report and outcome
suppliers close the bounded high-coverage construction, then the recovery adapter discharges
all three unchanged public statements.

This bundle packages proved milestone lemmas, not a separate `Challenge` root. Its fields
are pinned by `ConsensusLeanTest/MilestoneAxioms.lean`; `Challenge` certifies eight statements: the
five generic review statements and the Goldilocks statements of `Statements/Obligations`.
See `docs/decisions.md`, "Trusted surface and Challenge scope". -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Healing Recovery**: HR.5 cache acceptance, O.1 pattern recovery and C1.3 finalizing
coverage, with the actual-report and outcome suppliers discharged. -/
theorem recovery_statements : RecoveryStatements := by
  apply Recovery.recovery_statements_of_coverage
  intro sp ro proposer dg H tr K g ΔF Gp W M cF kF
  exact Recovery.pattern_coverage_supply Recovery.outcome_service
    (fun _ => Recovery.ready_proposal_report_supply)

end Consensus.Goldilocks.Healing

end
