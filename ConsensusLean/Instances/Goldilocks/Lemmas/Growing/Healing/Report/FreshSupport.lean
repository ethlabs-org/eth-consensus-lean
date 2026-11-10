module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVeto
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Honest support at the receiver's next-slot cast

The supporting committee is honest at this read. Proposal acceptance is instead
charged to its historical sender, so that sender need not belong to the committee.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Every validator still honest at the next-slot read supports the unanimous
proposal in that read's merged view. -/
theorem unanimous_next_cast_supporters_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {u : Nat} (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → SA.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} {a : Nat} (hz : z ∈ H (tr.time a))
    (ha : tr.projAC.AcceptAt z a P) (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u + 1)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hPt : P ∈ ell.frame.tree)
    (hvotes : ∀ x, x ∈ H (tr.time j) → ∃ i ev,
      SA.VoteAt tr.projAC x i ev ∧ ev.msg.slot = u ∧ tr.time i ≤ tr.time j) :
    ∀ x, x ∈ H (tr.time j) →
      x ∈ SA.supporters ell.frame (SA.mergedVoteView sp e.readPoint ell.frame (u + 1)) u P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (hrun.time_nonneg j) hjb
  have hr := hS.run.localRun
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time j)) y j ell e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  have hPhi := SA.frameIn_of_callAt hr hy hc'.1
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono
    (hrun.time_nonneg j)
  obtain ⟨q, hqj, haq, hqt⟩ := accepted_relay_before_at hrun hsvc hnr hz ha
    (hta ▸ hgu) hy hc.1 (by rw [hta]; linarith)
    ((hPhi.1.rooted.2 P hPt).mono (fun Q hQ => hsub (hPhi.2 hQ)))
  have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time j)) y q P := by
    obtain ⟨ellq, hcq, heq⟩ := haq
    exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqj, hcq⟩, heq⟩
  have hrst : ∀ k ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y k →
      tr.time k < sp.ts u := by
    intro k _ ⟨ellk, hck, hk⟩
    have hkt := ((Trace.upTo_callAt _).mp hck).1
    have hb := hnr y k (hrun.antitone hkt hy)
      (Compose.projAC_restartAt.mp ⟨ellk, ((Trace.upTo_callAt _).mp hck).2, hk⟩)
    linarith
  intro x hx
  obtain ⟨i, ev, hv, hs, hit⟩ := hvotes x hx
  have hv' : SA.VoteAt (tr.projAC.upTo (tr.time j)) x i ev := by
    obtain ⟨ellx, hcx, he⟩ := hv
    exact ⟨ellx, (Trace.upTo_callAt _).mpr ⟨hit, hcx⟩, he⟩
  have hval := (SA.castAt_spec hr hx ⟨hv'.choose_spec.1, hv'.choose_spec.2⟩).1
  have heP := hun x i ev (hrun.antitone hit hx) hv hs
  have hheld : SA.HeldBefore e.readPoint ev.msg (sp.ts u + 2 * sp.Δ) := by
    apply SA.heldBefore_readPoint hr hy hc' (by omega)
    simpa only [hs] using SA.honest_vote_early_pool_before hS hy hc'.1 hgu ht le_rfl
      (fun k hkj t _ => Compose.ac_deadline_le_of_restarts
        (fun r hr hrs => (hrst r (hr.trans hkj) hrs).le) t)
      hrst hx hv' hs (j + 1) (Or.inr rfl)
  have hsupp := SA.carried_supporter hS.run hy hc' hes hPt hs
    ⟨hheld.1, lt_trans hheld.2
      (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith)))⟩
    ⟨P, hPhi.2 hPt, heP.symm, hPs.le, .refl,
      Or.inr ⟨q, haq', by change tr.time q < _; rw [hta] at hqt; linarith⟩⟩
    (SA.honest_not_equivocator hS.run hy hc' (hval ▸ hx))
  rwa [hval] at hsupp

/-- The receiver's actual next-slot cast clears every older incompatible lock
before the update, including labels surviving an intervening update. -/
theorem FrameWindow.older_locks_compatible_at_update_at
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
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k u ell) :
    ∀ l ∈ (tr.projAC.state y k).locks, l.slot < u →
      ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
        Compatible (tr.HonestBlocksAt H) L P := by
  have hΔ := sp.toParams.hΔ
  have hgu : gbar g ≤ sp.ts u := by linarith
  have hu0 : 0 < u := by
    by_contra hn
    have he : u = 0 := by omega
    rw [he] at hmargin
    simp only [SAParams.ts, Nat.cast_zero, mul_zero] at hmargin
    linarith [SA.gbar_nonneg g]
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hnext : sp.ts (u + 1 : Nat) + sp.Δ ≤ tr.time k := by
    rw [hkt]; simp only [SAParams.ts]; push_cast; linarith
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts (u + 1 : Nat) + sp.Δ by
      have ht : sp.ts u ≤ sp.ts (u + 1 : Nat) := (SA.ts_le_iff sp).2 (by omega)
      linarith [SA.gbar_nonneg g]) (hnext.trans hkb)
  have hslot : sp.slot (sp.ts (u + 1 : Nat) + sp.Δ) = u + 1 := by
    apply SA.slot_of_mem sp (u + 1)
    all_goals simp only [SAParams.ts]; push_cast; linarith
  have hjn : ∀ x, x ∈ H (sp.ts (u + 1 : Nat) + sp.Δ) →
      SA.JoinedAt tr.projAC x (sp.ts (u + 1 : Nat) + sp.Δ) := by
    intro x hx r hrs hrt
    change tr.time r ≤ sp.ts ((sp.slot (sp.ts (u + 1 : Nat) + sp.Δ) : Int) - 1)
    rw [hslot, show ((u + 1 : Nat) : Int) - 1 = u by omega]
    exact (hnr x r (hrun.antitone hrt hx) (Compose.projAC_restartAt.mp hrs)).trans hgu
  obtain ⟨j, e, ⟨ellj, hc⟩, hs, hjt⟩ := honest_votes_of_joined_before_at hS
    (by have := (SA.ts_le_iff sp).2 (show (u : Int) ≤ u + 1 by omega); linarith) hjn y
    (hrun.antitone hnext hy)
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time k))
    (tr.upTo (tr.time k)) proposer (hrun.upTo (hrun.time_nonneg k))
    (hnc.upTo (tr.time k))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hjk : j < k := by
    by_contra hn
    have hm := hrun.time_mono (show k ≤ j by omega)
    rw [hkt] at hm
    simp only [SAParams.ts] at hjt
    push_cast at hjt
    simp only [SAParams.ts] at hm
    linarith
  have hc' : SA.CastAt (tr.projAC.upTo (tr.time k)) y j ellj e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨hrun.time_mono hjk.le, hc.1⟩, hc.2⟩
  have hjslot := (SA.castAt_spec hr hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at hjslot
  have hjlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (SA.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by rw [← hjslot, hs])
  have hjlate : sp.ts u + 2 * sp.Δ ≤ tr.time j := by
    simp only [SAParams.ts] at hjlo ⊢; push_cast at hjlo; linarith
  have hjfinite : tr.time j ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by linarith
  have hyj := hrun.antitone (hrun.time_mono hjk.le) hy
  have hshort : sp.ts u + sp.Δ ≤ tr.time j := by linarith
  have hS0 := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts u + sp.Δ by linarith [SA.gbar_nonneg g])
    (hshort.trans (hrun.time_mono hjk.le |>.trans hkb))
  have hvotes := honest_votes_of_joined_before_at hS0 hgu hjoin
  obtain ⟨hvi, _, _⟩ := hframe.proposal_viable_after_votes_at hrun hnc hsvc hawake hf hcatch
    hnr hgu hu0 hTb hz hdes hP hPs hyj hc.1 hjlate hjfinite
    (hvotes y (hrun.antitone hshort hyj))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, a, _, ha, hta⟩ :=
    honestProposalRun_of_proposesAt_at hrun hnc hz hdes hP hPs
  change tr.time a = sp.ts u at hta
  have hza : proposer u ∈ H (tr.time a) :=
    hrun.antitone (by rw [hta]; linarith) (hdes ▸ hz)
  have hsupp := unanimous_next_cast_supporters_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hPs hun hza ha hta hyj hc hs hjlate
    ((hrun.time_mono hjk.le).trans hkb) hvi.1
    (fun x hx => by
      obtain ⟨i, ev, hv, hes, hit⟩ := hvotes x (hrun.antitone hshort hx)
      exact ⟨i, ev, hv, hes, hit.trans hshort⟩)
  have hhalf : sp.n ≤ 2 * (H (tr.time j)).ncard := by
    have hn : (H (tr.time j)).ncard + (H (tr.time j))ᶜ.ncard = sp.n := by
      rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hb := hf (tr.time j) (hrun.time_nonneg j) ((hrun.time_mono hjk.le).trans hkb)
    omega
  exact older_locks_compatible_after_unlock_at hrun hnc hy hc hs hjk hvi.1
    (fun x hx => Or.inr (hsupp x hx).2) hhalf

end Consensus.Goldilocks.Healing.Growing

end
