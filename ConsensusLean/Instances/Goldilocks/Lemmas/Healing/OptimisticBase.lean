module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance

public section

/-! # Optimistic-lock next-slot propagation

An actual optimistic selection supplies the counted votes, including forwarded faulty
votes. A write-time viable witness supplies the frozen path, not assumed vote-head viability.
This is the optimistic base only; later-slot U-W and drain composition are separate. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- The optimistic base G(s+1,X), including below-floor X with a viable descendant Q.
The actual write and its counted set are retained. Q is held in the write frame; its
floor and J are the explicit FS′ values. Service/Catch ends at the next-slot horizon,
and no premise asserts viability of arbitrary honest vote heads. -/
theorem optimistic_next_votes_of_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor contest kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat} {CV : Set (SA.Vote sp.n)}
    (hopt : SA.OptimisticLockAt tr.projAC x c s D CV)
    (hXD : Anc (tr.HonestBlocks H) X D)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt x c ellw)
    (hQw : Q ∈ ellw.frame.tree)
    (hh : floor ≤ ((tr.state x c).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hx hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨x, hx, c, hQ⟩
  have htw := (SA.optimisticLockAt_spec hS.run hx hopt).1
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt x q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hx c ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt htw⟩
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X by
    exact fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e hv hs
    obtain ⟨ell, hc, he⟩ := hv
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hslot : sp.slot (tr.time i) = s + 1 := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
    have hlo : sp.ts s ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).mpr (by
        change (s : Int) ≤ sp.slot (tr.time i)
        rw [hslot]; omega)
    have hhi : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
      have ht := SA.vote_time_le hr hy ⟨ell, hcast⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
      simpa only [hslot] using ht
    have hJQ : kindJ → Anc (tr.HonestBlocks H) J Q := fun hk => (hJ hk).trans hXQ
    rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hx hlo hhi hQ hh hJQ hXQ
      with hFX | hXF
    swap
    · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := SA.castAt_head_anc hr hy hcast (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      refine ⟨W, hPhiU hW, hWr, ?_⟩
      have hFW := hFW.mono hPhiU
      rw [Compose.frame_of_projAC hrun hy hc] at hFW
      exact hXF.trans hFW
    have hFQ : Anc (tr.HonestBlocks H) ell.frame.F Q := by
      rw [Compose.frame_of_projAC hrun hy hc]
      exact hFX.trans hXQ
    have hcatchTime : gbar g + 2 * sp.Δ ≤
        sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
      rw [hs, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]
      linarith
    have hQdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hx hy hQU
      (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
      (by omega) (hhi.trans hmb) hcatchTime hFQ
    obtain ⟨hXt, hrootX, -, hvQ, hXQf⟩ := hframe.witness_path hrun hnc hmf hy hx
      hc hlo hhi hQ hh hJ hXQ (mem_tree_of_frame hrun hy hc hQdom.1) hFX
    have hviab : SA.ViableAtVote ell e (s + 1) X := by
      have hdomA := SA.voterBlockTree_anc hr hy hcast
      rw [hs] at hdomA hQdom
      exact Or.inl ⟨hdomA Q hQdom X hXQf, hrootX, Q, hQdom, hvQ, hXQf⟩
    have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s CV := by
      apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
        hm hS.catchUp (by linarith) hx hy hcast hs (hhi.trans hmb)
      intro v hv
      obtain ⟨hvs, hw, Hv, hHv, hHvr, hDHv, ha⟩ := Compose.optimistic_writer_votes hr hx hopt v hv
      refine ⟨hvs, hw, Hv, hHv, hHvr, ?_, ha⟩
      rw [Compose.frame_of_projAC hrun hy hc]
      exact hFX.trans (hXD.trans hDHv)
    exact SA.optimistic_transfer_stored sp hS.run hx hopt hXD (by
      have hn := sp.toParams.hn
      change 0 < sp.n at hn
      omega) hy hcast hs hcarry hviab
      (fun z hz k hki ev hv hes => ih k hki z hz ev hv hes)

end Consensus.Goldilocks.Healing

end
