module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OptimisticBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer

public section

/-! # Regular slow BASE on a finite FS′ window

Saved results compare actual stored origins. Unlike the archived capped
`frontier_first_transfer_slow`, the current proof uses emission read points,
remapped locks and viableAncestor, not a lease or pivot-cover premise. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- The viable-supporter branch of slow BASE. The witness is above the actual
result C. Saved-result compatibility and causal induction supply lock passage;
no compatibility or viability of receiving locks is assumed. -/
theorem regular_slow_next_votes_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    {s floor : Nat} (hm : gbar g ≤ sp.ts s)
    (hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1))
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {contest kindJ : Prop} {J Q D C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts s + 6 * sp.Δ)
      floor contest kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    (hsl : SA.SlowLockAt tr.projAC x c s D)
    (hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) (Node.frame (tr.state x c)) s C))
    (hCQ : Anc (tr.HonestBlocks H) C Q)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J D) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  obtain ⟨ellx, C', hu, hconf, hveto, hsel, hneq⟩ := hsl
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hsl : SA.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hveto, hsel, hneq⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2
  have hDQ := hDC.trans hCQ
  have hQ := mem_tree_of_frame hrun hw hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨w, hw, a, hQ⟩
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have htwo : 2 * Hᶜ.ncard < sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    omega
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hw a ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt hat⟩
  suffices hall : ∀ i, ∀ y ∈ H, ∀ e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D from fun y hy i e hv hs => hall i y hy e hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y hy e ⟨ell, hc, he⟩ hs
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
    change sp.slot (tr.time i) = s + 1 at hslot
    have hlo : sp.ts s ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
        change (s : Int) ≤ sp.slot (tr.time i); rw [hslot]; omega)
    have hhi : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
      have ht := SA.vote_time_le hr hy ⟨ell, hcast⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
      rwa [hslot] at ht
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hhigh : tr.time i ≤ sp.ts s + 6 * sp.Δ := by linarith [sp.toParams.hΔ]
    rcases hframe.finalized_comparable_of_witness hrun hnc hmf hy hw hlo hhigh hQ hh
      (fun hk => (hJ hk).trans hDQ) hDQ with hFD | hDF
    swap
    · obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := SA.castAt_head_anc hr hy hcast (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      refine ⟨W, hPhiU hW, hWr, ?_⟩
      have hFW := hFW.mono hPhiU
      rw [Compose.frame_of_projAC hrun hy hc] at hFW
      exact hDF.trans hFW
    have hFQ : Anc (tr.HonestBlocks H) ell.frame.F Q := by
      rw [Compose.frame_of_projAC hrun hy hc]; exact hFD.trans hDQ
    have hQdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hw hy hQU
      (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
      (by omega) (hhigh.trans hmb) (by
        rw [hs, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega]; linarith) hFQ
    obtain ⟨hDt, hroot, -, hvQ, hDQf⟩ := hframe.witness_path hrun hnc hmf hy hw hc
      hlo hhigh hQ hh hJ hDQ (mem_tree_of_frame hrun hy hc hQdom.1) hFD
    have hviab : SA.ViableAtVote ell e (s + 1) D := by
      have hdomA := SA.voterBlockTree_anc hr hy hcast
      rw [hs] at hdomA hQdom
      exact Or.inl ⟨hdomA Q hQdom D hDQf, hroot, Q, hQdom, hvQ, hDQf⟩
    have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
        (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := by
      apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
        hm hS.catchUp (by linarith) hx hy hcast hs (hhigh.trans hmb)
      intro v hv
      obtain ⟨hvs, hw, Hv, hHv, hHvr, hCHv, ha⟩ := Compose.result_writer hr hx hres v hv
      refine ⟨hvs, hw, Hv, hHv, hHvr, ?_, ha⟩
      rw [Compose.frame_of_projAC hrun hy hc]; exact hFD.trans (hDC.trans hCHv)
    exact SA.result_prefix_vote_extends_of_stored hS.run htwo hx hy hres hDC hcast hs
      hcarry hviab
      (SA.slow_stored_locks_before hS
        (fun z hz r hrs => hnr z hz r (Compose.projAC_restartAt.mp hrs)) hx hsl
        (hu.2.2.1.trans_le hmb) hslow hy (by change s + 1 ≤ sp.slot (tr.time i); omega)
        (hhigh.trans hmb))
      (fun z hz k hki ev hv hes => ih k hki z hz ev hv hes)
      (SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hS.sync)
        hx hm hu (hu.2.2.1.trans_le hmb) hy hcast hs)

/-- Slow BASE from the actual selection and result, including all three OW
supporter branches. The warm-window margin supplies saved-slot post-GST service;
no separate slow margin is assumed. -/
theorem FrameWindow.regular_slow_next_votes {s₀ s floor : Nat}
    {contest kindJ : Prop} {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts s + 6 * sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    (hsl : SA.SlowLockAt tr.projAC x c s D) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1) := by
    have hts : sp.ts s₀ ≤ sp.ts ((s : Int) - sp.k + 1) :=
      (SA.ts_le_iff sp).2 (by omega)
    linarith [sp.toParams.hΔ]
  have hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int) :=
    hm.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀))
  obtain ⟨ellx, C, hu, hconf, hveto, hsel, hneq⟩ := hsl
  have hsl : SA.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hveto, hsel, hneq⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    simp only [SAParams.ts]; rw [Nat.cast_sub (by omega : 1 ≤ s)]; ring
  have hms : gbar g + 4 * sp.Δ ≤ sp.ts s := by linarith [sp.toParams.hΔ]
  obtain ⟨z, hz, q, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before hrun hnc hsvc hawake hf hcatch hnr hms hx hres
      (hu.2.2.1.trans_le hmb)
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2
  have hDQ := hDC.trans hCQ
  have htq := SA.vote_time_le hr hz ⟨ell, hc, he⟩
  have hslot := (SA.castAt_spec hr hz ⟨hc, he⟩).2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have hqt : sp.ts s₀ ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) _).2 (by
      change (s₀ : Int) ≤ sp.slot (tr.time q); rw [hslot]; omega)
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hrootVotes : kindJ → Anc (tr.HonestBlocks H) D J →
      ∀ y ∈ H, ∀ i ev, SA.VoteAt tr.projAC y i ev → ev.msg.slot = s + 1 →
        SA.VoteExtends (tr.HonestBlocks H) ev.msg D := by
    intro hk hDJ y hy i ev ⟨elly, hcy, hey⟩ hev
    obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcy
    have hsl := (SA.castAt_spec hr hy ⟨hcy, hey⟩).2.1.symm.trans hev
    change sp.slot (tr.time i) = s + 1 at hsl
    have hlo : sp.ts s₀ ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
        change (s₀ : Int) ≤ sp.slot (tr.time i); rw [hsl]; omega)
    have hhi := SA.vote_time_le hr hy ⟨elly, hcy, hey⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
    rw [hsl] at hhi
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hhi' : tr.time i ≤ sp.ts s + 6 * sp.Δ := by linarith [sp.toParams.hΔ]
    obtain ⟨W, hW, hWr, hRW⟩ := SA.castAt_head_anc hr hy ⟨hcy, hey⟩ (Or.inr rfl)
      (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
        (fun h => Or.inr h.2.1) Or.inl) Relation.ReflTransGen.refl
    have hRW := hRW.mono hPhiU
    rw [Compose.frame_of_projAC hrun hy hcy] at hRW
    have hkind := (hframe.kind_iff y hy i hlo hhi').mpr hk
    have hroot : (tr.state y i).fg.fcRoot = J :=
      (ite_eq_left hkind).trans (hframe.root_eq y hy i hlo hhi' hk)
    change Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot W at hRW
    rw [hroot] at hRW
    exact ⟨W, hPhiU hW, hWr, hDJ.trans hRW⟩
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := hframe.vote_head_classification_of_service
    hrun hnc hmf hS hnr hz ⟨hc, he⟩ (by linarith [sp.toParams.hΔ])
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by simpa only [hes] using hm)
    (by rw [hes]; linarith [sp.toParams.hΔ]) (by
      rw [hes]; simp only [SA.freeze]
      have hcast : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
      rw [← hcast]; linarith [sp.toParams.hΔ])
  have hPhi := SA.frameIn_of_callAt hr hz hc
  have hEQ : Hd = Q := hr.coherent.1 (hPhi.2 hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | hj | ho
  · have hvQ := hv.2
    rw [Compose.frame_of_projAC hrun hz hc] at hvQ
    have hJQ : kindJ → Anc (tr.HonestBlocks H) J Q := by
      intro hk
      have hkind := (hframe.kind_iff z hz q hqt (by linarith [sp.toParams.hΔ])).mpr hk
      have hroot := (hPhi.1.fcRoot_anc_viableHeads Q hv.2).mono hPhi.2
      rw [Compose.frame_of_projAC hrun hz hc] at hroot
      change Anc (tr.HonestBlocks H) (tr.state z q).fg.fcRoot Q at hroot
      rwa [show (tr.state z q).fg.fcRoot = (tr.state z q).fg.J from ite_eq_left hkind,
        hframe.root_eq z hz q hqt (by linarith [sp.toParams.hΔ]) hk] at hroot
    by_cases hJD : kindJ → Anc (tr.HonestBlocks H) J D
    · apply regular_slow_next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hnr
        (by linarith [sp.toParams.hΔ]) hslow hmb
        ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i
            (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi,
         fun y hy i hlo hhi => hframe.contest_iff y hy i
            (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi,
         fun y hy i hlo hhi => hframe.kind_iff y hy i
            (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi,
         fun y hy i hlo hhi => hframe.root_eq y hy i
            (((SA.ts_le_iff sp).2 (by exact_mod_cast (show s₀ ≤ s by omega))).trans hlo) hhi⟩
        hx hsl ?_ hCQ hz (by linarith [sp.toParams.hΔ]) hc hHd ?_ hJD
      · simpa only [Compose.frame_of_projAC hrun hx hu.1] using hres
      · rw [← hframe.floor_eq z hz q hqt (by linarith [sp.toParams.hΔ])]
        exact hvQ.2.2.2
    · push Not at hJD
      obtain ⟨hk, hn⟩ := hJD
      exact hrootVotes hk ((SA.anc_total hr.coherent hDQ (hJQ hk)).resolve_right hn)
  · exact hrootVotes hj.1 (hj.2 ▸ hDQ)
  · obtain ⟨hA, l, hl, hls, a, hai, D', CV', hop, -, -, -, hQD⟩ := ho
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
      simp only [SAParams.ts]; push_cast; ring
    have hnext : FrameWindow (tr := tr) (H := H) (sp.ts s₀)
        (sp.ts (s + 1 : Nat) + sp.Δ) floor contest kindJ J :=
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i hlo (by linarith [sp.toParams.hΔ]),
       fun y hy i hlo hhi => hframe.contest_iff y hy i hlo (by linarith [sp.toParams.hΔ]),
       fun y hy i hlo hhi => hframe.kind_iff y hy i hlo (by linarith [sp.toParams.hΔ]),
       fun y hy i hlo hhi => hframe.root_eq y hy i hlo (by linarith [sp.toParams.hΔ])⟩
    have hheads := (hnext.optimistic_supporter_later_heads hrun hnc hsvc hawake hf hcatch hnr
      (by linarith [sp.toParams.hΔ]) (by omega) (by omega) (by linarith [sp.toParams.hΔ])
      hz ⟨hc, he⟩ hes hA (hes ▸ hop) (hQD.mono hPhi.2) (s + 1) le_rfl le_rfl).1
    intro y hy i ev hv hesv
    obtain ⟨W, hW, hWr, hQW⟩ := hheads y hy i ev hv hesv
    exact ⟨W, hW, hWr, hDQ.trans hQW⟩

end Consensus.Goldilocks.Healing

end
