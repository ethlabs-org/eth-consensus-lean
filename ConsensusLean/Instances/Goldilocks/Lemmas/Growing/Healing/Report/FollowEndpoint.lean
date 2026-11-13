module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowHeads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshEndpoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.CandidateReport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The actual warm report and its later proposal heads -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The fresh candidate yields an actual report, including when an earlier report suppresses it. -/
theorem proposal_report_follow_at
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hN : u + 1 ≤ N) (hmb : sp.ts N + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} (hy : y ∈ H (sp.ts (u + 1 : Nat) + 2 * sp.Δ))
    (hstock : sp.committeeSize = sp.n) :
    ∃ i ell R, y ∈ H (tr.time i) ∧ SA.ToFGAt tr.projAC y i ell R ∧
      sp.ts u ≤ tr.time i ∧ tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧
      Anc (tr.HonestBlocksAt H) P R ∧
      ∀ x, u + 3 ≤ x → x ≤ N → ∀ w c ellp, w ∈ H (tr.time c) →
        tr.projAC.CallAt w c ellp → ellp.call = .proposal → tr.time c = sp.ts x →
        ∀ d pay, (SA.acProposal sp (tr.projAC.state w c) ellp.frame (tr.time c)).2 =
          some (d, pay) → Anc (tr.HonestBlocksAt H) R d.head := by
  have hΔ := sp.toParams.hΔ
  have hk := sp.two_le_k
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hsub {lo hi : Time} (hlo : sp.ts s₀ ≤ lo) (hhi : hi ≤ sp.ts N + 2 * sp.Δ) :
      FrameWindow tr H lo hi floor kindJ J :=
    ⟨fun w i hw hl hh => hframe.floor_eq w i hw (hlo.trans hl) (hh.trans hhi),
     fun w i hw hl hh => hframe.kind_iff w i hw (hlo.trans hl) (hh.trans hhi),
     fun w i hw hl hh => hframe.root_eq w i hw (hlo.trans hl) (hh.trans hhi)⟩
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ sp.ts N + 2 * sp.Δ := by
    have := hts hN
    linarith only [this]
  have hun := honest_vote_heads_eq_at (hsub le_rfl (by
      have := hts (show u ≤ N by omega); linarith only [this, hΔ]))
    hrun hnc hsvc hawake hf hcatch hnr hm hwarm
    (by have := hts (show u ≤ N by omega); linarith only [this, hΔ, hmb])
    hz hdes hP hPs hstock
  have hshort := hsub (hts (by omega : s₀ ≤ u)) hT
  have hjoin := fun w hw => joined_voteTime_of_warm_frame_at hrun hnr hm
    (by omega : s₀ + 1 ≤ u) (y := w) hw
  have hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u := by
    have := hts (show s₀ ≤ u by omega)
    linarith only [hm, this, hΔ]
  obtain ⟨k, ell, ell', hu, hc, hto, ht, _, _, _, _, hva, hv, e, he, _, hl⟩ :=
    fresh_fast_lock_update_toFG_at hrun hnc hsvc hawake hf hcatch hnr hmargin hjoin
      (hT.trans hmb) hshort hz hdes hP hPs hun hy hstock
  have hyc : y ∈ H (tr.time (k + 1)) := ht ▸ hy
  have hPc := Healing.fresh_lock_toFG_candidate hv hva hl he ht
  have hr := (Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).upTo
    (hrun.time_nonneg (k + 1))
  have hj : SA.joined sp (tr.projAC.state y (k + 1)) (tr.time (k + 1)) := by
    have hs := Trace.upTo_state tr.projAC y (d := tr.time (k + 1)) (i := k + 1)
      (fun q hq => hrun.time_mono hq.le)
    unfold SA.joined
    rcases SA.restartTime_state hr.localRun hyc (k + 1) with h | ⟨q, _, hq, h⟩
    · rw [hs] at h
      rw [h]; exact bot_le
    · rw [hs] at h
      rw [h]
      apply WithBot.coe_le_coe.mpr
      have hq0 := ((ACTrace.upTo_restartAt (tr := tr.projAC)).mp hq).2
      have hqt := ((ACTrace.upTo_restartAt (tr := tr.projAC)).mp hq).1
      have hqy := hrun.antitone hqt hyc
      have hqg := hnr y q hqy (Compose.projAC_restartAt.mp hq0)
      have hslot : sp.slot (tr.time (k + 1)) = u + 1 := by
        rw [ht]
        apply SA.slot_of_mem sp (u + 1)
        all_goals simp only [SAParams.ts]; push_cast; linarith only [hΔ]
      rw [hslot]
      have hcast : ((u + 1 : Nat) : Int) - 1 = u := by omega
      rw [hcast]
      exact hqg.trans (by linarith only [hmargin, hΔ])
  have hptime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [hptime]; linarith only [hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hacc, _⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hacc
  have hPg := SA.accept_ne_genesis sp
    (Compose.goldilocks_ac_projection sp ro dg (H (tr.time kP)) (tr.upTo (tr.time kP))
      proposer (hrun.upTo (hrun.time_nonneg kP)) (hnc.upTo _)).localRun hzk hacc
  obtain ⟨i, ellr, R, hR, htime, hPR⟩ := report_of_compatible_candidate_of_run_at
    hrun hnc hyc hc hto hj hPg hPc
    (toFG_candidates_compatible_at_call_at hrun hnc hyc hc hPc)
  have hyi := hrun.antitone htime hyc
  have hit := htime.trans ht.le
  have hib := hit.trans (hT.trans hmb)
  refine ⟨i, ellr, R, hyi, hR,
    toFG_time_ge_of_ancestor_slot_at hrun hnc hyi (hf _ (hrun.time_nonneg i) hib) hR hPs hPR
      hstock,
    hit, hPR, ?_⟩
  intro x hx hNx w c ellp hw hcp hcall htc d pay hd
  have hbound : tr.time i ≤ sp.ts N + sp.Δ := by
    have htx := hts (show u + 2 ≤ N by omega)
    have hstep := SA.ts_succ (u + 1) (sp := sp)
    linarith only [hit, htx, hstep, hΔ]
  exact (hsub le_rfl (by linarith only [hΔ])).toFG_later_proposal_head_at
    hrun hnc hsvc hawake hf hcatch hnr hm hwarm (by linarith only [hmb, hΔ])
    hyi hR hPs hPR hbound hit hx hNx hw hcp hcall htc hd hstock

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
