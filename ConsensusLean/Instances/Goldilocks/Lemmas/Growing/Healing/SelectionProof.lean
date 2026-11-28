module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionFinalityProof
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionPool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UnanimousPool
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.ProposalViable
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.StopAtParent
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.SuffixBest
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.CallLocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Pivot
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Timing
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UpdateCalls
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ReportCover
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee

public section

/-! # Operational update selection with independently honest observations -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a : Time}
variable {hold : Time}

/-- The operational proposal is held and selected at every bounded honest update. -/
theorem operational_update_selection_proof_at {b : Time}
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {p : Fin sp.n} {k u : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) (hgu : AC.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} {j : Nat}
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp)}
    (hup : AC.UpdateAt tr.projAC y j u ell) :
    P ∈ ell.frame.tree ∧
      AC.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ AC.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      AC.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = AC.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (AC.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hDelta := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  have hun : ∀ z q e, z ∈ H (tr.time q) → AC.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z q e hz hv hqb hs =>
    hp.operational_unanimous_at hhold hdesignated hactual hPs hR (by linarith)
      z q e hz hv hs hqb
  have hRnext := hR.trans ((AC.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (AC.ts_le_iff sp).1 hR
    push_cast at this
    omega
  have hpk : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hactual.2.2
  have hph : p ∈ H (tr.time k) := hp.run.antitone (by rw [hpk]; linarith) hhold
  have hactual' : (tr.upTo (tr.time k)).ProposesAt p k P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hactual.1⟩, hactual.2.1, hactual.2.2⟩
  obtain ⟨_, hPm, _⟩ := Healing.accept_of_proposesAt (hp.run.upTo (hp.run.time_nonneg k))
    (hp.noColl.upTo _) hph hactual'
  rw [Trace.upTo_state tr p (i := k + 1) (fun _ hq => hp.run.time_mono (by omega))] at hPm
  have hPU : P ∈ tr.HonestBlocksAt H :=
    ⟨p, k + 1, tr.time k, hp.run.time_nonneg k,
      fun _ hq => hp.run.time_mono (by omega), hph, hPm⟩
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hca := hp.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := AC.gbar_nonneg g
    linarith
  have haR : a ≤ drainTime sp a := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (AC.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    apply ha'.le.trans
    rw [drainTime_eq]
    exact (AC.ts_le_iff sp).2 (by push_cast; omega)
  have hFP := finalized_below_unanimous_at_update_at hp hPU hPs hu hun hgu hRnext hTb hy hup
    (by rw [ht]; linarith [haR.trans hR])
  -- an honest member of the slot-`u` committee votes for `P`, which then reaches `y`
  obtain ⟨w, hwK, hw⟩ := hp.committee_honest_nonempty_at (s := u) (by linarith)
    (by linarith) (by linarith [AC.gbar_nonneg g]) hub
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot_at hp hgu hRnext hub w hw hwK
  have hwq : w ∈ H (tr.time q) := hp.run.antitone hq hw
  have hfr := (hp.run.cutLaw y j _ (Compose.projAC_callAt.mp hup.1) hy).1
  have hPt : P ∈ ell.frame.tree := unanimous_head_held_at_call_at hp hPU hun hgu hRnext hy hup.1
    (by rw [ht]; linarith) hjb (by rw [hfr] at hFP; exact hFP)
  have hPg : P.root ≠ sp.genesisRoot := by
    intro heq
    have hG := Healing.Store.genesis_mem (fg_reachable_at hp.run (hp.run.time_nonneg j)
      (fun _ hq => hp.run.time_mono hq.le) hy)
    have hGU : sp.toParams.genesisBlock (goldilocksNode sp).genesisPayload ∈
        tr.HonestBlocksAt H :=
      ⟨y, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hp.run.time_mono hq.le, hy, hG⟩
    have he := hU.1 hPU hGU heq
    have hz : P.slot = 0 := by rw [he]; rfl
    omega
  have hpool := unanimous_pool_at hp hun hgu hRnext hy hup.1
    (by rw [ht]; linarith) hjb hPt
  have hts : cutZ sp.toParams g ≤ sp.ts u := hca.le.trans (haR.trans hR)
  have hvote : ∃ z q ell e, z ∈ H (tr.time q) ∧ AC.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u := ⟨w, q, ellv, e, hwq, hv, hq.trans hub, hs⟩
  have hlocks := hp.call_locks_compatible_of_unanimous_at hPU hts hun hvote hy hup.1 hjb
    (by rw [ht]; linarith) ht.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible_at hp hPU hPs hu hun hgu hRnext hub
        (hp.run.antitone (hp.run.time_mono hr.le) hy) ho ((hp.run.time_mono hr.le).trans hjb))
  exact ⟨hPt, hp.ready_update_selection_of_pool_at hy hjb (by linarith) hup hPt hPg hpool
    hlocks⟩

end Consensus.Goldilocks.Healing.Growing

end
