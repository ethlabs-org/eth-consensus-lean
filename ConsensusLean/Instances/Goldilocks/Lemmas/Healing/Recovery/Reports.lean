module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Outcome
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyEffective
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Goldilocks Recovery: actual reports for a post-drain ready proposal

The bounded operational report theorem applies to arbitrary Goldilocks runs, not only the
canonical engine. Restrict the whole-run reset premises to the update deadline and discharge
its timing and proposal bookkeeping. Historical reports and the inclusive deadline are kept.
The narrow import exception belongs to this adapter, not to the shared Recovery interface.
-/

namespace Consensus.Goldilocks.Healing.Recovery

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {g ΔF a : Time}

/-- Actual report coverage, with no extra entry, height, timeout or report-freshness premise. -/
theorem ready_proposal_report_supply : ReadyProposalReportSupply tr H proposer dg g ΔF a where
  report_cover := by
    intro hp hc p k u P hP hR
    obtain ⟨hpH, hdesignated, _, hactual, hslot, _⟩ := hP
    have hΔ := sp.toParams.hΔ
    obtain ⟨hu, hau, hgu⟩ := drain_margins hp hR
    have hacc := Compose.proposal_accepted hp.run hp.noColl hpH hactual
    have hPU : P ∈ tr.HonestBlocks H := by
      refine ⟨p, hpH, k + 1, ?_⟩
      rw [tr.state_succ_of_call hacc,
        (Store.tree_grows _ _ _ _ (Compose.fg_reachable hp.run.toLocalRun hpH _)).1 P _
          (hp.run.toLocalRun.cutLaw p hpH _ _ hacc).2.1]
      exact Set.mem_insert _ _
    have hPg : P.root ≠ sp.genesisRoot := by
      intro he
      have hgen := Compose.honest_eq_genesis hp.run (honest_coherent hp) hPU he
      have hz : P.slot = 0 := by rw [hgen]; rfl
      omega
    have hbounded := hp.toUpTo tr H
      (show a ≤ sp.ts u + 6 * sp.Δ by linarith)
    exact Refinement.UpTo.report_cover_of_proposal hbounded hc hpH hdesignated hactual
      hPU hslot hu hPg hgu hR le_rfl

/-- **C1.2:** exact outcome service, with the actual-report supplier discharged. -/
theorem outcome_service : Compose.OutcomeService :=
  outcome_service_of_reports fun _ _ _ _ _ _ _ _ _ => ready_proposal_report_supply

end Consensus.Goldilocks.Healing.Recovery

end
