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

/-- U-W from a regular next-vote base and its early supporter witness. Proposals
start at s+2: no circular proposal base is assumed at s+1. The archived
`frontier_heads_transfer` induction used lease frames; here every frozen-domain
stamp is derived at the actual emission read point. -/
theorem regular_later_heads_of_early_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g)) {s N floor : Nat}
    (hm : gbar g ≤ sp.ts s) (hmb : sp.ts N + sp.Δ ≤ b)
    {contest kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts N + sp.Δ)
      floor contest kindJ J)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J X)
    (hXQ : Anc (tr.HonestBlocks H) X Q)
    (hbase : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg X) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) e.msg X) ∧
      (s + 2 ≤ r → ∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts r →
        ∀ d pay, (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
          some (d, pay) → Anc (tr.HonestBlocks H) X d.head) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hQ := mem_tree_of_frame hrun hw hcw hQw
  have hQU : Q ∈ tr.HonestBlocks H := ⟨w, hw, a, hQ⟩
  have hsource : Q.root = sp.genesisRoot ∨
      ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts s + 2 * sp.Δ := by
    rcases Compose.frame_anc_accepted hr hw a ellw hcw Q hQw Q .refl with hg | ⟨q, hqc, ha⟩
    · exact Or.inl hg
    · exact Or.inr ⟨q, ha, (hr.time_mono hqc).trans_lt hat⟩
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  intro r hrlo
  induction r, hrlo using Nat.le_induction with
  | base => exact fun _ => ⟨hbase, fun h => by omega⟩
  | succ m hsm ih =>
    intro hrN
    have hmN : m ≤ N := by omega
    have hprior := (ih hmN).1
    have ht := hts hrN
    have hms := hts hsm
    have hwarm : gbar g + 4 * sp.Δ ≤ sp.ts m := by rw [hstep] at hms; linarith
    have hwin : FrameWindow (tr := tr) (H := H) (sp.ts m)
        (sp.ts (m + 1 : Nat) + sp.Δ) floor contest kindJ J :=
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith)),
       fun y hy i hlo hhi => hframe.contest_iff y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith)),
       fun y hy i hlo hhi => hframe.kind_iff y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith)),
       fun y hy i hlo hhi => hframe.root_eq y hy i ((hts (by omega)).trans hlo)
          (hhi.trans (by linarith))⟩
    have hheld : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = m + 1 →
        Q ∈ (tr.state y i).fg.tree ∧
          e.readPoint.blockStamp Q.root < SA.ETime.of (SA.freeze sp (m + 1)) := by
      intro y hy i e hv hs
      obtain ⟨ell, hc, he⟩ := hv
      have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
      have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
      change sp.slot (tr.time i) = m + 1 at hslot
      have hlo : sp.ts s ≤ tr.time i :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
          change (s : Int) ≤ sp.slot (tr.time i); rw [hslot]; omega)
      have hhi : tr.time i ≤ sp.ts (m + 1 : Nat) + sp.Δ := by
        have h := SA.vote_time_le hr hy ⟨ell, hcast⟩
        change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at h
        rwa [hslot] at h
      have hFQ := hframe.finalized_below_descendant hrun hnc hmf hy hw hw hlo
        (hhi.trans (by linarith)) hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
      change Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F Q at hFQ
      rw [← Compose.frame_of_projAC hrun hy hc] at hFQ
      have hct : gbar g + 2 * sp.Δ ≤ sp.ts ((e.msg.slot : Int) - 1) + 3 * sp.Δ := by
        rw [hs, show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]; linarith
      have hdom := voterBlockTree_of_relay_source hr hS.sync hS.catchUp hw hy hQU
        (Relation.ReflTransGen.refl : Anc (tr.HonestBlocks H) Q Q) hsource hcast
        (by omega) (hhi.trans (by linarith)) hct hFQ
      refine ⟨mem_tree_of_frame hrun hy hc hdom.1, ?_⟩
      rw [← hs]
      rcases hsource with hg | ⟨q, hq, hqt⟩
      · apply SA.readPoint_blockStamp_lt_of_acceptedBefore hr hy hcast hdom.1 (Or.inl hg)
        · intro k hk hrs
          have h := hnr y hy k (Compose.projAC_restartAt.mp hrs)
          change tr.time k < _
          rw [hs]; unfold SA.freeze; rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega]
          linarith
        · have h : sp.ts (m + 1 : Nat) ≤ tr.time i :=
            (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
              change ((m + 1 : Nat) : Int) ≤ sp.slot (tr.time i); rw [hslot])
          change SA.freeze sp e.msg.slot ≤ tr.time i
          rw [hs]; unfold SA.freeze
          rw [show ((m + 1 : Nat) : Int) - 1 = (m : Int) by omega, hstep] at *
          linarith
      · exact (relay_readPoint_stamp_window_before hr hS.sync hS.catchUp hw hy hq hqt
          hcast (by omega) (hhi.trans (by linarith)) hct hFQ).2
    refine ⟨unanimous_next_votes_of_witness hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith) hwin hw hQ hh hJ hXQ hheld hprior, ?_⟩
    intro _ y hy i ell hc hcall hti d pay hd
    have hlo : sp.ts s ≤ tr.time i := by rw [hti]; exact hts (by omega)
    have hhi : tr.time i ≤ sp.ts N + sp.Δ := by rw [hti]; linarith
    have hFQ := hframe.finalized_below_descendant hrun hnc hmf hy hw hw hlo hhi
      hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
    change Anc (tr.HonestBlocks H) (Node.frame (tr.state y i)).F Q at hFQ
    rw [← Compose.frame_of_projAC hrun hy hc] at hFQ
    have hsource' : Q.root = sp.genesisRoot ∨
        ∃ q, tr.projAC.AcceptAt w q Q ∧ tr.projAC.time q < sp.ts m + 2 * sp.Δ := by
      rcases hsource with hg | ⟨q, hq, hqt⟩
      · exact Or.inl hg
      · exact Or.inr ⟨q, hq, by linarith [hts (show s ≤ m by omega)]⟩
    have hQt := (relay_source_at_proposal hS (hm.trans (hts (by omega))) hw hy hc hti
      (hhi.trans hmb) (fun k hk hrs => (hnr y hy k (Compose.projAC_restartAt.mp hrs)).trans
        (hm.trans (hts (by omega)))) hQU hsource' hFQ).1
    exact unanimous_next_proposal_of_witness hrun hnc hsvc hawake hf hcatch hnr hwarm
      (by linarith) hwin hw hQ hh hJ hXQ hprior hy hc hcall hti hd
      (mem_tree_of_frame hrun hy hc hQt)

/-- MI-reg for an actual regular origin, with all supporter cases discharged.
Votes start at s+1 and proposals at s+2. The early viable supporter, not a
write-tick witness with an unproved strict timestamp, supplies every U-W step. -/
theorem FrameWindow.regular_later_heads {s₀ s N floor : Nat}
    {contest kindJ : Prop} {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsN : s + 2 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    (horigin : (∃ CV, SA.FastUpdateAt tr.projAC x c s D CV) ∨
      SA.SlowLockAt tr.projAC x c s D) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocks H) D d.head) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch
  have hr := hS.run.localRun
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hsub {lo hi : Time} (hl : sp.ts s₀ ≤ lo) (hh' : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow (tr := tr) (H := H) lo hi floor contest kindJ J :=
    ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i (hl.trans hlo) (hhi.trans hh'),
     fun y hy i hlo hhi => hframe.contest_iff y hy i (hl.trans hlo) (hhi.trans hh'),
     fun y hy i hlo hhi => hframe.kind_iff y hy i (hl.trans hlo) (hhi.trans hh'),
     fun y hy i hlo hhi => hframe.root_eq y hy i (hl.trans hlo) (hhi.trans hh')⟩
  have h6 : sp.ts s + 6 * sp.Δ ≤ sp.ts N + sp.Δ := by
    have ht := hts hsN
    rw [show s + 2 = (s + 1) + 1 by omega, hstep, hstep] at ht
    linarith [sp.toParams.hΔ]
  have hbase : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
    rcases horigin with ⟨CV, hfast⟩ | hslow
    · exact (hsub le_rfl h6).regular_fast_next_votes hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ (hm.trans (hts hs₀)) (h6.trans hmb) hx hfast .refl
    · exact (hsub le_rfl h6).regular_slow_next_votes hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ hm (h6.trans hmb) hx hslow
  obtain ⟨C, CV, hres, hDC⟩ : ∃ C CV, SA.ResultAt tr.projAC x c s C CV ∧
      Anc (tr.HonestBlocks H) D C := by
    rcases horigin with ⟨CV, ell, C, hu, hconf, -, hsel, -⟩ | ⟨ell, C, hu, hconf, -, hsel, -⟩
    all_goals exact ⟨C, _, ⟨ell, hu, hconf, rfl⟩,
      ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2⟩
  obtain ⟨z, hz, q, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before hrun hnc hsvc hawake hf hcatch hnr
      (hm.trans (hts (by omega))) hx hres (by
        obtain ⟨ell', hu, -, -⟩ := hres
        exact hu.2.2.1.trans_le (h6.trans hmb))
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
  have hrootHeads : kindJ → Anc (tr.HonestBlocks H) D J →
      ∀ r, s + 1 ≤ r → r ≤ N →
        (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
          SA.VoteExtends (tr.HonestBlocks H) e.msg D) ∧
        (s + 2 ≤ r → ∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
          tr.time i = sp.ts r → ∀ d pay,
          (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
            Anc (tr.HonestBlocks H) D d.head) := by
    intro hk hDJ r hrlo hrN
    have hroot (y) (hy : y ∈ H) (i) (hlo : sp.ts s₀ ≤ tr.time i)
        (hhi : tr.time i ≤ sp.ts N + sp.Δ) : (tr.state y i).fg.fcRoot = J :=
      (ite_eq_left ((hframe.kind_iff y hy i hlo hhi).mpr hk)).trans
        (hframe.root_eq y hy i hlo hhi hk)
    constructor
    · intro y hy i ev ⟨elly, hcy, hey⟩ hev
      obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcy
      have hsl := (SA.castAt_spec hr hy ⟨hcy, hey⟩).2.1.symm.trans hev
      change sp.slot (tr.time i) = r at hsl
      have hlo : sp.ts s₀ ≤ tr.time i :=
        (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2 (by
          change (s₀ : Int) ≤ sp.slot (tr.time i); rw [hsl]; omega)
      have hhi := SA.vote_time_le hr hy ⟨elly, hcy, hey⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
      rw [hsl] at hhi
      obtain ⟨W, hW, hWr, hRW⟩ := SA.castAt_head_anc hr hy ⟨hcy, hey⟩ (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) Relation.ReflTransGen.refl
      have hRW := hRW.mono hPhiU
      rw [Compose.frame_of_projAC hrun hy hcy] at hRW
      change Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot W at hRW
      rw [hroot y hy i hlo (hhi.trans (by linarith [hts hrN]))] at hRW
      exact ⟨W, hPhiU hW, hWr, hDJ.trans hRW⟩
    · intro _ y hy i elly hcy hcall hti d pay hd
      obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hcy
      have hRW : Anc (tr.HonestBlocks H) elly.frame.fcRoot d.head := by
        rw [(SA.acProposal_head hd).2]
        exact (SA.anc_getHead_of_compat hPhi (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl)
        (fun B (hB : B ∈ elly.frame.viableTree elly.frame.tree) => hB.1)
        _ _ Relation.ReflTransGen.refl).mono hPhiU
      rw [Compose.frame_of_projAC hrun hy hcy] at hRW
      change Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot _ at hRW
      rw [hroot y hy i (by rw [hti]; exact hts (by omega))
        (by rw [hti]; linarith [hts hrN, sp.toParams.hΔ])] at hRW
      exact hDJ.trans hRW
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := hframe.vote_head_classification_of_service
    hrun hnc hmf hS hnr hz ⟨hc, he⟩ (by linarith [hts (show s ≤ N by omega)])
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by rw [hes]; exact hm.trans (hts hs₀))
    (by rw [hes]; linarith [hts (show s - 1 ≤ N by omega)])
    (by rw [hes]; simp only [SA.freeze]
        have hprev : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by omega
        rw [← hprev]
        have := hm.trans (hts hs₀); linarith [sp.toParams.hΔ])
  have hPhi := SA.frameIn_of_callAt hr hz hc
  have hEQ : Hd = Q := hr.coherent.1 (hPhi.2 hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | hj | ho
  · have hvQ := hv.2
    rw [Compose.frame_of_projAC hrun hz hc] at hvQ
    have hJQ : kindJ → Anc (tr.HonestBlocks H) J Q := by
      intro hk
      have hroot := (hPhi.1.fcRoot_anc_viableHeads Q hv.2).mono hPhi.2
      rw [Compose.frame_of_projAC hrun hz hc] at hroot
      change Anc (tr.HonestBlocks H) (tr.state z q).fg.fcRoot Q at hroot
      rwa [show (tr.state z q).fg.fcRoot = (tr.state z q).fg.J from
          ite_eq_left ((hframe.kind_iff z hz q hqt
            (by linarith [hts (show s ≤ N by omega)])).mpr hk),
        hframe.root_eq z hz q hqt (by linarith [hts (show s ≤ N by omega)]) hk] at hroot
    by_cases hJD : kindJ → Anc (tr.HonestBlocks H) J D
    · exact regular_later_heads_of_early_witness hrun hnc hsvc hawake hf hcatch hnr
        (by linarith [hts (show s₀ ≤ s by omega), sp.toParams.hΔ]) hmb
        (hsub (hts (by omega)) le_rfl) hz (by linarith [sp.toParams.hΔ]) hc hHd
        (by rw [← hframe.floor_eq z hz q hqt (by linarith [hts (show s ≤ N by omega)])]
            exact hvQ.2.2.2) hJD hDQ hbase
    · push Not at hJD
      obtain ⟨hk, hn⟩ := hJD
      exact hrootHeads hk ((SA.anc_total hr.coherent hDQ (hJQ hk)).resolve_right hn)
  · exact hrootHeads hj.1 (hj.2 ▸ hDQ)
  · obtain ⟨hA, l, hl, hls, a, hai, D', CV', hop, -, -, -, hQD⟩ := ho
    have hheads := hframe.optimistic_supporter_later_heads hrun hnc hsvc hawake hf hcatch hnr
      (by linarith [hts (show s₀ ≤ s by omega), sp.toParams.hΔ]) (by omega) (by omega) hmb
      hz ⟨hc, he⟩ hes hA (hes ▸ hop) (hQD.mono hPhi.2)
    intro r hrlo hrN
    constructor
    · intro y hy i ev hv hesv
      obtain ⟨W, hW, hWr, hQW⟩ := (hheads r hrlo hrN).1 y hy i ev hv hesv
      exact ⟨W, hW, hWr, hDQ.trans hQW⟩
    · intro _ y hy i ell' hc' hcall hti d pay hd
      exact hDQ.trans ((hheads r hrlo hrN).2 y hy i ell' hc' hcall hti d pay hd)

/-- Step 4 passage with the regular residue eliminated. Same-write provenance
supplies the selected raw block, its candidate and the actual regular/optimistic
origin together. Only current-label optimistic writes remain for Step 6; this
does not assert head=P (Step 5), causal closure (Step 6), DESC or drain. -/
theorem FrameWindow.current_lock_passage_of_regular_base {s₀ p floor : Nat}
    {contest kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts p + sp.Δ)
      floor contest kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer p)
    {k : Nat} (hactual : tr.ProposesAt z k P) (hPs : P.slot = p)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B' : SA.Blk sp.n (List (FG.Att sp.n))}
    (hB' : B' ∈ ell.frame.tree) (hBr : B'.root = l.block) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame p) ∧
      (Anc (tr.HonestBlocks H) B' P ∨
        (l.slot = p ∧ ∃ a ≤ i, ∃ D CV, SA.OptimisticLockAt tr.projAC y a p D CV ∧
          sp.ts p ≤ tr.time a ∧ Anc (tr.HonestBlocks H) B' D)) := by
  have hΔ := sp.toParams.hΔ
  have hm₀ : gbar g ≤ sp.ts s₀ := by linarith
  obtain ⟨hvP, hdomP⟩ := hframe.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch
    hnr hm₀ hsp hp0 hpb hz hdesignated hactual hPs hy hc hes
  refine ⟨hvP, hdomP, ?_⟩
  have hlabel : s₀ + sp.k ≤ l.slot := by omega
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hslot : sp.slot (tr.time i) = p := ((SA.castAt_spec hr hy hc).2.1).symm.trans hes
  by_cases hcurrent : p ≤ l.slot
  · obtain ⟨hs, a, hai, D, CV, hop, ht, C, hC, hCr, hCD⟩ :=
      SA.current_lock_write_readPoint hr hy hc (hes ▸ hp0) hl (hes ▸ hcurrent)
    obtain rfl : C = B' := hr.coherent.1 hC (hPhiU hB') (hCr.trans hBr.symm)
    rw [hes] at hs hop ht
    exact Or.inr ⟨hs, a, hai, D, CV, hop, ht, hCD⟩
  have hold : l.slot + 1 ≤ p := by omega
  have hk : 0 < sp.k := by omega
  obtain ⟨l₀, hl₀, hs, B, hB, hBr₀, C, hC, hCr, hCB⟩ :=
    SA.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time i); rw [hslot]; exact hp0) l hl
      (by change l.slot ≠ sp.slot (tr.time i); rw [hslot]; omega)
  have hCE : C = B' := hPhi.coherent.1 hC hB' (hCr.trans hBr.symm)
  subst C
  obtain ⟨a, hai, ellw, D, ha, hD, ho, M, hM, hMr, hMA⟩ :=
    SA.lock_selection_candidate_provenance hr hy i l₀ hl₀
  obtain rfl : M = B := hr.coherent.1 hM (hPhiU hB) (hMr.trans hBr₀.symm)
  rw [← hs] at ho
  let A := ellw.frame.viableAncestor D
  have hBA : Anc (tr.HonestBlocks H) B' A := (hCB.mono hPhiU).trans hMA
  have hW := SA.frameIn_of_callAt hr hy ha
  have hAD : Anc (tr.HonestBlocks H) A D := (SA.viableAncestor_anc hW.1 hD).2.mono hW.2
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := SA.vote_time_le hr hy ⟨ell, hc⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot] at ht
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hd, hti, hparent, _, _, _, ja, _, hacc, _⟩ :=
    honestProposalRun_of_proposesAt hrun hnc hz hdesignated hactual hPs
  rw [← hdesignated] at hcp hd
  have hHP : Anc (tr.HonestBlocks H) d.head P := by
    have hH : d.head ∈ ellp.frame.tree := by
      rw [(SA.acProposal_head hd).2]
      exact SA.getHead_mem (SA.frameIn_of_callAt hr hz hcp).1
        (fun X (hX : X ∈ ellp.frame.viableTree ellp.frame.tree) => hX.1) _ _ _ _
    exact .single ⟨(SA.frameIn_of_callAt hr hz hcp).2 hH, hPhiU hdomP.1.1, hparent⟩
  have hregular (horigin : (∃ CV, SA.FastUpdateAt tr.projAC y a l.slot D CV) ∨
      SA.SlowLockAt tr.projAC y a l.slot D) : Anc (tr.HonestBlocks H) B' P := by
    obtain ⟨ell', hu⟩ : ∃ ell', SA.UpdateAt tr.projAC y a l.slot ell' := by
      rcases horigin with ⟨CV, ell', C, hu, -⟩ | ⟨ell', C, hu, -⟩ <;> exact ⟨ell', hu⟩
    have ht := hu.2.2.1
    change tr.time a = _ at ht
    have hgap : l.slot + 2 ≤ p := by
      by_contra hn
      have he : p = l.slot + 1 := by omega
      have htime := hrun.time_mono hai.le
      rw [he] at hhigh
      simp only [SAParams.ts] at ht hhigh
      push_cast at hhigh
      linarith
    have hDP := (hframe.regular_later_heads hrun hnc hsvc hawake hf hcatch hnr
      hlabel (by omega) (by omega) hm hgap hpb hy horigin p (by omega) le_rfl).2
        hgap z hz ip ellp hcp hcall hti d pay hd
    exact hBA.trans (hAD.trans (hDP.trans hHP))
  rcases ho with ⟨_, CV, hfast | hop⟩ | ⟨_, hslow⟩
  · exact Or.inl (hregular (Or.inl ⟨CV, hfast⟩))
  swap
  · exact Or.inl (hregular (Or.inr hslow))
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by omega)
  have hlow : sp.ts l.slot ≤ tr.time a := by
    obtain ⟨_, _, _, hs', _, _⟩ := hop
    exact (SA.ts_le_iff_le_slot sp (hr.time_nonneg a) _).2 (by rw [hs'])
  have halo := hts.trans hlow
  have hcase : ellw.frame.Anc A ellw.frame.fcRoot ∨
      A ∈ ellw.frame.viableTree ellw.frame.tree := (SA.viableAncestor_spec hW.1 hD).2.1
  rcases hcase with hbelow | hAv
  · have hAw := hbelow.mono hW.2
    rw [Compose.frame_of_projAC hrun hy ha] at hAw
    have hmono := hframe.fcRoot_mono hrun hy hai.le halo hhigh
    have hrootP := hdomP.2.1.mono hPhiU
    rw [Compose.frame_of_projAC hrun hy hc.1] at hrootP
    exact Or.inl (hBA.trans (hAw.trans (hmono.trans hrootP)))
  obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
  have hvQ' := hvQ
  rw [Compose.frame_of_projAC hrun hy ha] at hvQ'
  have hh : floor ≤ ((tr.state y a).fg.σ Q.root).h := by
    rw [← hframe.floor_eq y hy a halo ((hrun.time_mono hai.le).trans hhigh)]
    exact hvQ'.2.2.2
  have hJ : kindJ → Anc (tr.HonestBlocks H) J A := by
    intro hk'
    have hkind := (hframe.kind_iff y hy a halo ((hrun.time_mono hai.le).trans hhigh)).mpr hk'
    have hrootA := hAv.2.1.mono hW.2
    rw [Compose.frame_of_projAC hrun hy ha] at hrootA
    change Anc (tr.HonestBlocks H) (tr.state y a).fg.fcRoot A at hrootA
    rwa [show (tr.state y a).fg.fcRoot = (tr.state y a).fg.J from ite_eq_left hkind,
      hframe.root_eq y hy a halo ((hrun.time_mono hai.le).trans hhigh) hk'] at hrootA
  have hsub : FrameWindow (tr := tr) (H := H) (sp.ts l.slot) (sp.ts p + sp.Δ)
      floor contest kindJ J :=
    ⟨fun w hw j hlo hhi => hframe.floor_eq w hw j (hts.trans hlo) hhi,
     fun w hw j hlo hhi => hframe.contest_iff w hw j (hts.trans hlo) hhi,
     fun w hw j hlo hhi => hframe.kind_iff w hw j (hts.trans hlo) hhi,
     fun w hw j hlo hhi => hframe.root_eq w hw j (hts.trans hlo) hhi⟩
  have hAP := (optimistic_later_heads_of_witness hrun hnc hsvc hawake hf hcatch hnr
    (hm₀.trans hts) hpb hsub hy hop hAD ha hQ hh hJ (hAQ.mono hW.2) p hold le_rfl).2
      z hz ip ellp hcp hcall hti d pay hd
  exact Or.inl (hBA.trans (hAP.trans hHP))

end Consensus.Goldilocks.Healing

end
