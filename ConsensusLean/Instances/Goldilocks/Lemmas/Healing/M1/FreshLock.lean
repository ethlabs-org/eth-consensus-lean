module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OptimisticBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.FloorUpdate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier

public section

/-! # Fresh fast locks under finite service

Actual votes and strict early resolution are separate from unanimous vote agreement.
The vote deadline uses explicit joinedness, rather than a stronger GST margin.
-/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {g b : Time}
  {proposer : Nat → Fin sp.n}

/-- Finite service and joinedness at the actual vote deadline supply an honest vote.
No `4Δ` warm-start margin is needed when joinedness is supplied explicitly. -/
theorem honest_votes_of_joined_before (hS : HealthyBaseUpTo tr H U proposer g b)
    {u : Nat} (hgu : gbar g ≤ sp.ts u) (hub : sp.ts u + sp.Δ ≤ b)
    (hjoin : ∀ x ∈ H, JoinedAt tr x (sp.ts u + sp.Δ)) :
    ∀ x ∈ H, ∃ j e, VoteAt tr x j e ∧ e.msg.slot = u ∧ tr.time j ≤ sp.ts u + sp.Δ := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hg0 := gbar_nonneg g
  intro x hx
  have hslot : sp.slot (sp.ts u + sp.Δ) = u := by
    apply slot_of_mem sp u (by linarith)
    simp only [SAParams.ts]; push_cast; linarith
  obtain ⟨c, ell, hc, hcall, htc⟩ := hS.driven.tick x hx (sp.ts u + sp.Δ) (by linarith)
    ⟨4 * u + 1, by simp only [SAParams.ts]; ring⟩ (hS.awake x hx _ (by linarith) hub)
  have hj : joined sp (tr.state x c) (tr.time c) := by
    unfold joined
    rcases restartTime_state hr hx c with h | ⟨r, hrc, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      rw [htc]
      exact hjoin x hx r hrs ((hr.time_mono hrc.le).trans htc.le)
  by_cases hv : (tr.state x c).votedSlot = (sp.slot (tr.time c) : Int)
  · obtain ⟨j, hjc, e, he, hes⟩ := vote_of_votedSlot hr hx c _ hv
    exact ⟨j, e, he, by rw [hes, htc, hslot], (hr.time_mono hjc.le).trans htc.le⟩
  · have hT : tr.time c = sp.ts (sp.slot (tr.time c)) + sp.Δ := by rw [htc, hslot]
    obtain ⟨e, hem, hes⟩ := tryVote_votes x ell.frame hj hv hT
    have he := hr.exec c ell hc.2 (hc.1 ▸ hx)
    rw [hc.1, hcall] at he
    have h2 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 = ell.emits :=
      congrArg Prod.snd he
    have h3 : (acOnTick sp x (tr.state x c) ell.frame (tr.time c)).2 =
        (tryVote sp x (tr.state x c) ell.frame (tr.time c)).2 := by
      unfold acOnTick
      dsimp only
      split_ifs
      all_goals first | rfl | exact absurd hj ‹_›
    exact ⟨c, e, ⟨ell, hc, h2 ▸ h3 ▸ hem⟩, by rw [hes, htc, hslot], htc.le⟩

/-- An actual honest vote emitted after GST is held with its strict early stamp.
The restart and deadline premises concern only cuts through the receiving call. -/
theorem honest_vote_early_pool_before (hS : HealthyBaseUpTo tr H U proposer g b)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell) {u : Nat}
    (hgu : gbar g ≤ sp.ts u) (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j)
    (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts u) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts u)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {e : Em sp FGP}
    (hv : VoteAt tr x i e) (hes : e.msg.slot = u) :
    ∀ c, (c = j ∨ c = j + 1) → e.msg ∈ (tr.state y c).pool u ∧
      (tr.state y c).voteStamp e.msg < ETime.of (sp.ts u + 2 * sp.Δ) := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨ellx, hcx, hex⟩ := hv
  obtain ⟨hval, hslot, -, -⟩ := castAt_spec hr hx ⟨hcx, hex⟩
  have hti : tr.time i ≤ sp.ts u + sp.Δ := by
    have hh := vote_time_le hr hx ⟨ellx, hcx, hex⟩
    rwa [← hslot, hes] at hh
  have hti0 : sp.ts u ≤ tr.time i :=
    (ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by rw [← hslot, hes])
  have hgi : gbar g ≤ tr.time i := hgu.trans hti0
  have hdl := hdeadline j le_rfl (tr.time i) hgi
  rw [max_eq_left hti0] at hdl
  obtain ⟨q, hqj, hiq, hproc, hqt⟩ := hS.sync.message x hx i e.msg
    ⟨ellx, hcx, Or.inl ⟨e, hex, rfl⟩⟩ hgi y hy j ell hc
    (by linarith) (by linarith)
  have hqT : tr.time q < sp.ts u + 2 * sp.Δ := by
    have hqdl := hdeadline q hqj (tr.time i) hgi
    rw [max_eq_left hti0] at hqdl
    linarith
  have hqj' : q < j := lt_of_le_of_ne hqj (by rintro rfl; linarith)
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hqs : sp.slot (tr.time q) = u :=
    slot_of_mem sp u (by linarith) (by rw [hts]; linarith)
  have hxH : e.msg.val ∈ H := hval ▸ hx
  have hheld : e.msg ∈ (tr.state y (q + 1)).pool u := by
    rcases held_of_processAt hr hy hproc (by rw [hqs, hes]; omega) (by rw [hqs, hes]) with
      h | ⟨v, hv, w, hw, hne, hvval, hwval⟩
    · rwa [hes] at h
    · exfalso
      rw [hes] at hv hw
      obtain ⟨iv, -, ev, hev, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) u _ hv (hvval ▸ hxH)
      obtain ⟨iw, -, ew, hew, rfl⟩ := hS.run.honest.pool_vote y hy (q + 1) u _ hw (hwval ▸ hxH)
      have hsv := state_pool_slot sp hr hy (q + 1) u _ hv
      have hsw := state_pool_slot sp hr hy (q + 1) u _ hw
      rw [hvval] at hev
      rw [hwval] at hew
      obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr _ hxH iv iw ev ew hev hew
        (hsv.trans hsw.symm)
      exact hne rfl
  intro c hcj
  have hst := stamp_lt_of_held_of_run hr hy (a := q + 1) (b := c) (by omega)
    (w := e.msg) (by rw [hes]; exact hheld) (T := sp.ts u + 2 * sp.Δ)
    (fun k hk => lt_of_le_of_lt (hr.time_mono (Nat.lt_succ_iff.1 hk)) hqT)
    (by rw [hes]; linarith)
    (fun k hk hrs => lt_trans (hrestart k (by omega) hrs) (by linarith))
    (fun k hqk hkc hrs => by
      have := hrestart k (by omega) hrs
      have := hr.time_mono (show q ≤ k by omega)
      linarith)
  rwa [hes] at hst

/-- Actual joined votes on an honest proposal give a unique, strictly early-resolved
honest batch. Acceptance relay uses the observing frame's finalized ancestor guard. -/
theorem unanimous_early_pool_of_proposal (hS : HealthyBaseUpTo tr H U proposer g b)
    {u : Nat} (hgu : gbar g ≤ sp.ts u)
    (hjoin : ∀ x ∈ H, JoinedAt tr x (sp.ts u + sp.Δ))
    {P : Blk sp.n FGP} (hPs : P.slot = u)
    (hun : ∀ x ∈ H, ∀ i e, VoteAt tr x i e → e.msg.slot = u → e.msg.head = P.root)
    {z : Fin sp.n} (hz : z ∈ H) {a : Nat} (hacc : tr.AcceptAt z a P)
    (hta : tr.time a = sp.ts u)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ell)
    (ht : sp.ts u + 2 * sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hdeadline : ∀ k ≤ j, ∀ t, gbar g ≤ t → tr.deadline y k t ≤ max t (sp.ts u) + sp.Δ)
    (hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k < sp.ts u)
    (hPt : P ∈ ell.frame.tree) :
    ∀ x ∈ H, ∃ v ∈ (tr.state y j).pool u, v.val = x ∧ v.head = P.root ∧
      resolutionTime (tr.state y j) ell.frame v < ETime.of (sp.ts u + 2 * sp.Δ) ∧
      ∀ v' ∈ (tr.state y j).pool u, v'.val = x → v' = v := by
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_callAt hr hy hc
  have hga : gbar g ≤ tr.time a := hta ▸ hgu
  have hdl := hdeadline j le_rfl (tr.time a) hga
  rw [hta, max_self] at hdl
  obtain ⟨q, hqj, haq, hqt⟩ := hS.sync.relay z hz a P hacc hga y hy j ell hc
    (by rw [hta]; linarith) (by rw [hta]; linarith) ((hPhi.rooted.2 P hPt).mono hPhiU)
  rw [hta] at hqt
  have hqT : tr.time q < sp.ts u + 2 * sp.Δ := by
    have hdq := hdeadline q hqj (tr.time a) hga
    rw [hta, max_self] at hdq
    linarith
  have hbs := blockStamp_lt_of_acceptedBefore sp hr hy hc hPt (Or.inr ⟨q, haq, hqT⟩)
    (fun k hk hrs => (hrestart k hk hrs).trans_le (by linarith)) (Or.inl ht)
  intro x hx
  obtain ⟨i, e, hv, hes, _⟩ := honest_votes_of_joined_before hS hgu (by linarith) hjoin x hx
  have heP := hun x hx i e hv hes
  obtain ⟨hmem, hvs⟩ := honest_vote_early_pool_before hS hy hc hgu ht hjb hdeadline hrestart
    hx hv hes j (Or.inl rfl)
  obtain ⟨hval, -⟩ := castAt_spec hr hx ⟨hv.choose_spec.1, hv.choose_spec.2⟩
  refine ⟨e.msg, hmem, hval, heP,
    resolutionTime_lt_of hPhi hPt heP.symm (by omega) hvs (heP ▸ hbs), ?_⟩
  intro v' hv' hv'x
  obtain ⟨q', -, e', he', rfl⟩ := hS.run.honest.pool_vote y hy j u v' hv' (hv'x ▸ hx)
  rw [hv'x] at he'
  obtain ⟨-, rfl⟩ := (one_vote_per_slot sp) FGP ro H U tr hr x hx q' i e' e he' hv
    ((state_pool_slot sp hr hy j u _ hv').trans hes.symm)
  rfl

end Consensus.Goldilocks.SA

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- FS′ carries the actual honest proposal from a joined slot vote to the update's
own frame. Both ends of the FS′ window are inclusive. -/
theorem FrameWindow.proposal_viable_at_update
    {u floor : Nat} {contest kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H)
      (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u) (hu0 : 0 < u)
    (hjoin : ∀ y ∈ H, SA.JoinedAt tr.projAC y (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer u)
    {kP : Nat} (hactual : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} (hy : y ∈ H) {k : Nat} {ell : ACLabel (goldilocksNode sp ro)}
    (hu : SA.UpdateAt tr.projAC y k u ell) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hDelta := sp.toParams.hΔ
  have hts : sp.ts (u + 1 : Nat) = sp.ts u + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hshortT : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    rw [hts]; linarith
  have hub := hshortT.trans hTb
  have hshort : FrameWindow (tr := tr) (H := H) (sp.ts u) (sp.ts u + sp.Δ)
      floor contest kindJ J :=
    ⟨fun x hx i hlo hhi => hframe.floor_eq x hx i hlo (hhi.trans hshortT),
      fun x hx i hlo hhi => hframe.contest_iff x hx i hlo (hhi.trans hshortT),
      fun x hx i hlo hhi => hframe.kind_iff x hx i hlo (hhi.trans hshortT),
      fun x hx i hlo hhi => hframe.root_eq x hx i hlo (hhi.trans hshortT)⟩
  obtain ⟨q, e, ⟨ellq, hcq⟩, hes, hqt⟩ := SA.honest_votes_of_joined_before hS hgu hub hjoin y hy
  have hPv := (hshort.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch hnr hgu
    le_rfl hu0 hub hz hdesignated hactual hPs hy hcq hes).1
  have hqlo : sp.ts u ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) _).2 (by
      rw [← (SA.castAt_spec hr hy hcq).2.1, hes])
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hqk : q ≤ k := by
    by_contra h
    have htime := hrun.time_mono (show k ≤ q by omega)
    change tr.time q ≤ _ at hqt
    linarith
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨hPt, hroot, hPv⟩ := hframe.viableHead_persists hrun hnc hmf hy hqk hqlo
    (by rw [hkt, hts]; linarith) hcq.1 hPv
  rw [← Compose.frame_of_projAC hrun hy hu.1] at hPt hroot hPv
  have hvi : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPt, hroot, P, hPt, hPv, .refl⟩
  exact ⟨hvi, SA.viableAncestor_self (SA.frameIn_of_callAt hr hy hu.1).1 hPt (Or.inl hvi)⟩

end Consensus.Goldilocks.Healing

end
