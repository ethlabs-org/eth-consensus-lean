module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Interface
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
    have hcut := lt_cutZ sp g
    have hca := cutZ_lt_reset hp.run hp.healthy hp.reset
    have ha0 : 0 ≤ a := by linarith [SA.gbar_nonneg g]
    have haR : a ≤ drainTime sp a := by
      have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
        have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
        omega
      apply ha'.le.trans
      rw [drainTime_eq]
      exact (SA.ts_le_iff sp).2 (by push_cast; omega)
    have hau : a ≤ sp.ts u := haR.trans hR
    have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u := by linarith
    have hu : 0 < u := by
      rw [drainTime_eq] at hR
      have := (SA.ts_le_iff sp).1 hR
      push_cast at this
      omega
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

end Consensus.Goldilocks.Healing.Recovery

end
