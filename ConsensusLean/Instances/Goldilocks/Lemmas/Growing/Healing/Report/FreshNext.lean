module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshSupport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.UnanimousNextCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSupport
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Next-slot extension from the warm frame

The warm frame supplies the fork-choice root and height floor at each cast.
Participation is counted at that cast, never at a fixed honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

/-- Warm full-frame persistence discharges the service core's root and floor
premises for every next-slot cast, at the slot committees `K` of a run from `K`'s committee
start. -/
theorem FrameWindow.unanimous_next_votes_at {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → AC.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ y j e, y ∈ H (tr.time j) → AC.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he] at hmargin
    simp only [ACParams.ts, Nat.cast_zero, mul_zero] at hmargin
    linarith [AC.gbar_nonneg g]
  have hshort : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) := by
    simp only [ACParams.ts]; push_cast; linarith
  have hdeadline : sp.ts u + sp.Δ ≤ b := by linarith
  have hnextb : sp.ts (u + 1 : Nat) ≤ b := by linarith
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [AC.gbar_nonneg g]) hdeadline
  have hvotes := honest_votes_of_joined_before_at hS hgu hjoin
  have hPh : P ∈ tr.HonestBlocksAt H := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, ha, hta⟩ :=
      honestProposalRun_of_proposesAt_at hrun hnc hz hdes hP hPs
    change tr.time a = sp.ts u at hta
    have hza : proposer u ∈ H (tr.time a) :=
      hrun.antitone (by rw [hta]; linarith) (hdes ▸ hz)
    have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg a))
      (hnc.upTo (tr.time a))).localRun
    rw [RunTrace.upTo_projAC] at hr
    have ha' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time a)) (proposer u) a P := by
      obtain ⟨ella, hca, hea⟩ := ha
      exact ⟨ella, (Trace.upTo_callAt _).mpr ⟨le_rfl, hca⟩, hea⟩
    have hnew := AC.accept_new sp hr hza ha'
    obtain ⟨ella, hca, _⟩ := ha'
    exact RunTrace.honestBlocks_upTo_subset hrun.time_mono (hrun.time_nonneg a)
      ((AC.frameIn_of_callAt hr hza hca).2 (hnew.1 ella hca))
  have geometry : ∀ y j ell e, y ∈ H (tr.time j) → AC.CastAt tr.projAC y j ell e →
      e.msg.slot = u + 1 → tr.time j ≤ b →
      Anc (tr.HonestBlocksAt H) ell.frame.fcRoot P ∧
      (tr.state y j).fg.headHeightFloor ≤ ((tr.state y j).fg.σ P.root).h := by
    intro y j ell e hy hc hes hjb
    have hr := (Compose.goldilocks_ac_projection_from (hrun.upTo (hrun.time_nonneg j))
      (hnc.upTo (tr.time j))).localRun
    rw [RunTrace.upTo_projAC] at hr
    have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
      ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
    have hslot := (AC.castAt_specU hr.toU hy hc').2.1
    change e.msg.slot = sp.slot (tr.time j) at hslot
    have hlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
      (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← hslot, hes])
    have hhi : tr.time j ≤ sp.ts (u + 1 : Nat) + sp.Δ := by
      have hv := AC.vote_time_leU hr.toU hy ⟨ell, hc'⟩
      change tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ at hv
      rwa [← hslot, hes] at hv
    obtain ⟨hvi, _, hv⟩ := hframe.proposal_viable_after_votes_at hrun hnc hsvc hf hnr hgu hTb
      hz hdes hP hPs hy hc.1
      (by simp only [ACParams.ts] at hlo ⊢; push_cast at hlo; linarith) (by linarith)
    have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg j)
    refine ⟨hvi.2.1.mono (fun Q hQ => hsub ((AC.frameIn_of_callAt hr hy hc'.1).2 hQ)), ?_⟩
    have hframeeq : ell.frame = Node.frame (tr.state y j) := by
      exact (hrun.cutLaw y j _ (Compose.projAC_callAt.mp hc.1) hy).1
    rw [hframeeq] at hv
    exact hv.2.2.2
  -- an honest member of the slot-`u` committee witnesses `P` by the slot's vote deadline
  have hnext0 : 0 ≤ sp.ts (u + 1 : Nat) := (AC.gbar_nonneg g).trans (hgu.trans (by linarith))
  obtain ⟨w, hwK, hw⟩ : (K.committee u ∩ H (sp.ts (u + 1 : Nat))).Nonempty := by
    have hcs := hK.cs2 u hgu (by linarith) _ hnext0 hnextb
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard (K.committee u)
      (H (sp.ts (u + 1 : Nat))) (Set.toFinite _)
    rw [hK.facts.hsize u, Set.sdiff_eq_compl_inter, Set.inter_comm (H _)ᶜ] at hsplit
    exact Set.nonempty_of_ncard_ne_zero (by omega)
  have hw' := hrun.antitone hshort hw
  obtain ⟨q, e, hv, hes, hq⟩ := hvotes w hw' hwK
  refine unanimous_next_votes_extend_core_at hrun hnc hsvc hcatch hPh hPs hu0
    (fun y j e hy hv _ hs => hun y j e hy hv hs) hgu hK.facts.hP (hK.facts.committeeTAt hrun hnc)
    hK.facts.hsize (fun y k hy hk _ => hnr y k hy hk)
    ⟨w, q, e, hrun.antitone hq hw', hv, hes, hq⟩
    (fun x hx hxK => hvotes x (hrun.antitone hshort hx) hxK) ?_ ?_ ?_ ?_
  · intro i hlo hib
    have hslot : u + 1 ≤ sp.slot (tr.time i) := by
      exact_mod_cast (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).1 hlo
    exact KernelProof.faultBoundK_of_service_at hK hrun hawake hnr hgu (by linarith)
      (hrun.time_nonneg i) (hgu.trans ((AC.ts_le_iff sp).2 (by omega))) hib
  · intro i hlo hib
    exact hK.cs2 (u + 1) (hgu.trans (by linarith)) hnextb _ (hrun.time_nonneg i) hib
  · intro y j ell e hy hc hs hjb
    exact (geometry y j ell e hy hc hs hjb).1
  · intro y j ell e hy hc hs hjb _
    exact (geometry y j ell e hy hc hs hjb).2

end Consensus.Goldilocks.Healing.Growing

end
