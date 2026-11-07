module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionFinalityProof
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.SelectionPool
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.UnanimousPool
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierViews
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.FiniteSources
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
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served

public section

/-! # Operational update selection with independently honest observations -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a : Time}

/-- The operational proposal is held and selected at every bounded honest update. -/
theorem operational_update_selection_proof_at {b : Time}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hhold : p ∈ H (sp.ts u + sp.Δ)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) {y : Fin sp.n} {j : Nat}
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    (hup : SA.UpdateAt tr.projAC y j u ell) :
    P ∈ ell.frame.tree ∧
      SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P ∧
      ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P ∧
      SA.fastSelect sp (tr.projAC.state y j) ell.frame u P = some P ∧
      tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hDelta := sp.toParams.hΔ
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hup.2.2.1
  have hjb : tr.time j ≤ b := ht ▸ hTb
  have hub : sp.ts u + sp.Δ ≤ b := by linarith
  have hun : ∀ z q e, z ∈ H (tr.time q) → SA.VoteAt tr.projAC z q e → tr.time q ≤ b →
      e.msg.slot = u → e.msg.head = P.root := fun z q e hz hv hqb hs =>
    hp.operational_unanimous_at hc hhold hdesignated hactual hPs hR (by linarith)
      z q e hz hv hs hqb
  have hRnext := hR.trans ((SA.ts_le_iff sp).2 (show (u : Int) ≤ (u + 1 : Nat) by omega))
  have hu : 0 < u := by
    rw [drainTime_eq] at hR
    have := (SA.ts_le_iff sp).1 hR
    push_cast at this
    omega
  have hpk : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hactual.2.2
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
    have := SA.gbar_nonneg g
    linarith
  have haR : a ≤ drainTime sp a := by
    have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
      have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
      omega
    apply ha'.le.trans
    rw [drainTime_eq]
    exact (SA.ts_le_iff sp).2 (by push_cast; omega)
  have hFP := finalized_below_unanimous_at_update_at hp hc hPU hPs hu hun hgu hRnext hTb hy hup
    (by rw [ht]; linarith [haR.trans hR])
  have hyd : y ∈ H (sp.ts u + sp.Δ) := hp.run.antitone (by rw [ht]; linarith) hy
  obtain ⟨q, e, ⟨ellv, hv⟩, hs, hq⟩ := honest_votes_in_slot_at hp hc hgu hRnext hub y hyd
  have hyq : y ∈ H (tr.time q) := hp.run.antitone hq hyd
  have hr :=
    (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl).localRun
  have hcq : SA.CastAt (tr.projAC.upTo (tr.time q)) y q ellv e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hv.1⟩, hv.2⟩
  obtain ⟨⟨Hd, hHd, he, _⟩, _⟩ := Compose.cast_head_fcRoot
    (hr.upTo (hp.run.time_nonneg q)) hyq hcq
  have hPsiU : ellv.frame.tree ⊆ tr.HonestBlocksAt H := by
    rcases hr.frameLaw y q ellv hyq hv.1 with
      ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.1.2
  obtain rfl : Hd = P := hU.1 (hPsiU hHd) hPU
    (he.trans (hun y q e hyq ⟨ellv, hv⟩ (hq.trans hub) hs))
  have hqj : q ≤ j := by
    by_contra hn
    have := hp.run.time_mono (show j ≤ q by omega)
    rw [ht] at this
    linarith
  have hPq := (frame_tree_subset_at hp.run hp.noColl hyq hv.1).2 hHd
  have hPj : Hd ∈ (tr.state y j).fg.tree := by
    have h := (Compose.fg_grows (hp.run.upTo (hp.run.time_nonneg j)) hy hqj).1
      (show Hd ∈ ((tr.upTo (tr.time j)).state y q).fg.tree by
        rwa [RunTrace.upTo_state_of_le hp.run.time_mono (hp.run.time_mono hqj)])
    rwa [RunTrace.upTo_state_of_le hp.run.time_mono le_rfl] at h
  have hfr := (hp.run.cutLaw y j _ (Compose.projAC_callAt.mp hup.1) hy).1
  have hPt : Hd ∈ ell.frame.tree := by
    rw [hfr]
    rw [hfr] at hFP
    exact ⟨hPj, store_anc_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg j)
      (fun _ hq => hp.run.time_mono hq.le) hy hFP hPj⟩
  have hPg : Hd.root ≠ sp.genesisRoot := by
    intro heq
    have hG := Healing.Store.genesis_mem (fg_reachable_at hp.run (hp.run.time_nonneg j)
      (fun _ hq => hp.run.time_mono hq.le) hy)
    have hGU : sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload ∈
        tr.HonestBlocksAt H :=
      ⟨y, j, tr.time j, hp.run.time_nonneg j, fun _ hq => hp.run.time_mono hq.le, hy, hG⟩
    have he := hU.1 hPU hGU heq
    have hz : Hd.slot = 0 := by rw [he]; rfl
    omega
  have hpool := unanimous_pool_at hp hc hun hgu hRnext hy hup.1
    (by rw [ht]; linarith) hjb hPt
  have hts : cutZ sp.toParams g ≤ sp.ts u := hca.le.trans (haR.trans hR)
  have hvote : ∃ z q ell e, z ∈ H (tr.time q) ∧ SA.CastAt tr.projAC z q ell e ∧
      tr.time q ≤ b ∧ e.msg.slot = u := ⟨y, q, ellv, e, hyq, hv, hq.trans hub, hs⟩
  have hlocks := hp.call_locks_compatible_of_unanimous_at hc hPU hts hun hvote hy hup.1 hjb
    (by rw [ht]; linarith) ht.le (fun r hr B CV ho =>
      unanimous_next_optimistic_compatible_at hp hc hPU hPs hu hun hgu hRnext hub
        (hp.run.antitone (hp.run.time_mono hr.le) hy) ho ((hp.run.time_mono hr.le).trans hjb))
  exact ⟨hPt, hp.ready_update_selection_of_pool_at hy hjb hup hPt hPg hpool hlocks⟩

end Consensus.Goldilocks.Healing.Growing

end
