module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNextCore

public section

/-! # Next-slot extension from the warm frame

The warm frame supplies the fork-choice root and height floor at each cast.
Participation is counted at that cast, never at a fixed honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Warm full-frame persistence discharges the service core's root and floor
premises for every next-slot cast. -/
theorem FrameWindow.unanimous_next_votes_at
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → SA.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → SA.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he] at hmargin
    simp only [SAParams.ts, Nat.cast_zero, mul_zero] at hmargin
    linarith [SA.gbar_nonneg g]
  have hshort : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) := by
    simp only [SAParams.ts]; push_cast; linarith
  have hdeadline : sp.ts u + sp.Δ ≤ b := by linarith
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [SA.gbar_nonneg g]) hdeadline
  have hvotes := honest_votes_of_joined_before_at hS hgu hjoin
  have hPh : P ∈ tr.HonestBlocksAt H := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, ha, hta⟩ :=
      honestProposalRun_of_proposesAt_at hrun hnc hz hdes hP hPs
    change tr.time a = sp.ts u at hta
    have hza : proposer u ∈ H (tr.time a) :=
      hrun.antitone (by rw [hta]; linarith) (hdes ▸ hz)
    have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time a))
      (tr.upTo (tr.time a)) proposer (hrun.upTo (hrun.time_nonneg a))
      (hnc.upTo (tr.time a))).localRun
    rw [RunTrace.upTo_projAC] at hr
    have ha' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time a)) (proposer u) a P := by
      obtain ⟨ella, hca, hea⟩ := ha
      exact ⟨ella, (Trace.upTo_callAt _).mpr ⟨le_rfl, hca⟩, hea⟩
    have hnew := SA.accept_new sp hr hza ha'
    obtain ⟨ella, hca, _⟩ := ha'
    exact RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg a)
      ((SA.frameIn_of_callAt hr hza hca).2 (hnew.1 ella hca))
  have geometry : ∀ y j ell e, y ∈ H (tr.time j) → SA.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P ∧
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h := by
    intro y j ell e hy hc hes hjb
    have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
      (tr.upTo (tr.time j)) proposer (hrun.upTo (hrun.time_nonneg j))
      (hnc.upTo (tr.time j))).localRun
    rw [RunTrace.upTo_projAC] at hr
    have hc' : SA.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
      ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
    have hslot := (SA.castAt_spec hr hy hc').2.1
    change e.msg.slot = sp.slot (tr.time j) at hslot
    have hlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
      (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← hslot, hes])
    have hhi : tr.time j ≤ sp.ts (u + 1 : Nat) + sp.Δ := by
      have hv := SA.vote_time_le hr hy ⟨ell, hc'⟩
      change tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ at hv
      rwa [← hslot, hes] at hv
    obtain ⟨hvi, _, hv⟩ := hframe.proposal_viable_after_votes_at hrun hnc hsvc hawake hf hcatch
      hnr hgu hu0 hTb hz hdes hP hPs hy hc.1
      (by simp only [SAParams.ts] at hlo ⊢; push_cast at hlo; linarith)
      (by linarith) (hvotes y (hrun.antitone (hshort.trans hlo) hy))
    have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg j)
    refine ⟨hvi.2.1.mono (fun Q hQ => hsub ((SA.frameIn_of_callAt hr hy hc'.1).2 hQ)), ?_⟩
    have hframeeq : ell.frame = Node.frame (tr.state y j) := by
      exact (hrun.cutLaw y j _ (Compose.projAC_callAt.mp hc.1) hy).1
    rw [hframeeq] at hv
    exact hv.2.2.2
  apply unanimous_next_votes_extend_core_at hrun hnc hsvc hcatch hPh hPs hu0
    (fun y j e hy hv _ hs => hun y j e hy hv hs) hgu
    (fun x hx => hvotes x (hrun.antitone hshort hx))
  · intro i hlo hib
    have hslot : u + 1 ≤ sp.slot (tr.time i) := by
      exact_mod_cast (SA.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hlo
    have hprev : gbar g ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1) :=
      hgu.trans ((SA.ts_le_iff sp).2 (by omega))
    have hsub : H (tr.time i) ⊆ {y | y ∈ H (tr.time i) ∧
        tr.projAC.awake y (tr.time i) ∧ SA.JoinedAt tr.projAC y (tr.time i)} := by
      intro y hy
      refine ⟨hy, hawake y (tr.time i) hy (hgu.trans (by
        have := (SA.ts_le_iff sp).2 (show (u : Int) ≤ u + 1 by omega); linarith)) hib, ?_⟩
      intro k hrs hkt
      exact (hnr y k (hrun.antitone hkt hy) (Compose.projAC_restartAt.mp hrs)).trans hprev
    have hn : (H (tr.time i)).ncard + (H (tr.time i))ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hb := hf (tr.time i) (hrun.time_nonneg i) hib
    have hcount := Set.ncard_le_ncard hsub
    change (H (tr.time i))ᶜ.ncard < _
    have := sp.toParams.hn
    omega
  · intro y j ell e hy hc hs hjb
    exact (geometry y j ell e hy hc hs hjb).1
  · intro y j ell e hy hc hs hjb _
    exact (geometry y j ell e hy hc hs hjb).2

end Consensus.Goldilocks.Healing.Growing

end
