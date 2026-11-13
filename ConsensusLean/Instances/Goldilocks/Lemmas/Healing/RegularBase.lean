module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.OptimisticBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.H2Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ViewAgree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.ExpiryFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.FloorHead
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ParentStop
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ProposalPath
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The regular slow next-vote base on a finite `FrameWindow`

Saved results compare actual stored origins. Unlike the archived capped
`frontier_first_transfer_slow`, the current proof uses emission read points,
remapped locks and viableAncestor, not a lease or pivot-cover premise. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF b : Time}

/-- The viable-supporter branch of the slow next-vote base. The witness is above the actual
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
    {kindJ : Prop} {J Q D C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s) (sp.ts s + 6 * sp.Δ)
      floor kindJ J)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    (hsl : SA.SlowLockAt tr.projAC x c s D)
    (hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) (Node.frame (tr.state x c)) s C))
    (hCQ : Anc (tr.HonestBlocks H) C Q)
    {w : Fin sp.n} (hw : w ∈ H) {a : Nat}
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocks H) J D) (hstock : sp.committeeSize = sp.n) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch hstock
  have hr := hS.run.localRun
  obtain ⟨ellx, C', hu, hconf, hsel⟩ := hsl
  have he : C' = C := by
    obtain ⟨ell', hu', hconf', -⟩ := hres
    have he : ellx = ell' := Option.some.inj (hu.1.2.symm.trans hu'.1.2)
    subst ell'
    exact Option.some.inj (hconf.symm.trans hconf')
  subst C'
  have hsl : SA.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hsel⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2
  have hDQ := hDC.trans hCQ
  have htwo : 2 * Hᶜ.ncard < sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    clear * - hf hn; omega
  apply next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hm (by
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    linarith only [sp.toParams.hΔ, hts]) hmb hframe hw hat hcw hQw hh hJ hDQ ?_ hstock
  intro y hy i ell e hcast hs hhigh hFD hviab ih
  have hslot := (SA.castAt_spec hr hy hcast).2.1.symm.trans hs
  change sp.slot (tr.time i) = s + 1 at hslot
  have hcarry : SA.CarryAt tr.projAC (tr.HonestBlocks H) y i e s
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := by
    apply Compose.carryAt_of_writer_window_before hr (SA.serviceWindowBefore_of_sync hS.sync)
      hm hS.catchUp (by linarith only [sp.toParams.hΔ, hm]) hx hy hcast hs (hhigh.trans hmb)
    intro v hv
    obtain ⟨hvs, hw, Hv, hHv, hHvr, hCHv, ha⟩ := Compose.result_writer hr
      (fun _ => SA.voteStart_initial _) hx hres v hv
    refine ⟨hvs, hw, Hv, hHv, hHvr, ?_, ha⟩
    rw [Compose.frame_of_projAC hrun hy hcast.1]; exact hFD.trans (hDC.trans hCHv)
  exact SA.result_prefix_vote_extends_of_stored hS.run htwo hx hy hres hDC hcast hs
    hcarry hviab
    (SA.slow_stored_locks_before hS
      (fun z hz r hrs => hnr z hz r (Compose.projAC_restartAt.mp hrs)) hx hsl
      (hu.2.2.1.trans_le hmb) hslow hy
      (by change s + 1 ≤ sp.slot (tr.time i); clear * - hslot; omega)
      (hhigh.trans hmb)) ih
    (SA.writer_merged_window_before hS.run (SA.serviceWindowBefore_of_sync hS.sync)
      hx hm hu (hu.2.2.1.trans_le hmb) hy hcast hs) hstock

/-- The slow next-vote base from the actual selection and result, including all three supporter
branches of `FrameWindow.vote_head_classification`. The warm-window margin supplies saved-slot
post-GST service; no separate slow margin is assumed. -/
theorem FrameWindow.regular_slow_next_votes {s₀ s floor : Nat}
    {kindJ : Prop} {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts s + 6 * sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y ∈ H, ∀ t, gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : 3 * Hᶜ.ncard ≤ sp.n - 1) (hcatch : CatchRun tr H g (2 * sp.Δ))
    (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hmb : sp.ts s + 6 * sp.Δ ≤ b)
    {x : Fin sp.n} (hx : x ∈ H) {c : Nat}
    (hsl : SA.SlowLockAt tr.projAC x c s D) (hstock : sp.committeeSize = sp.n) :
    ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch hstock
  have hr := hS.run.localRun
  have hslow : gbar g ≤ sp.ts ((s : Int) - sp.k + 1) := by
    have hts : sp.ts s₀ ≤ sp.ts ((s : Int) - sp.k + 1) :=
      (SA.ts_le_iff sp).2 (by clear * - hwarm; omega)
    linarith only [sp.toParams.hΔ, hm, hts]
  have hm : gbar g + 4 * sp.Δ ≤ sp.ts ((s - 1 : Nat) : Int) :=
    hm.trans ((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀))
  obtain ⟨ellx, C, hu, hconf, hsel⟩ := hsl
  have hsl : SA.SlowLockAt tr.projAC x c s D := ⟨ellx, C, hu, hconf, hsel⟩
  have hres : SA.ResultAt tr.projAC x c s C
      (SA.fastCounted sp (tr.projAC.state x c) ellx.frame s C) := ⟨ellx, hu, hconf, rfl⟩
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by clear * - hpos; omega : 1 ≤ s), Nat.cast_one, SA.ts_sub_one]
  have hms : gbar g + 4 * sp.Δ ≤ sp.ts s := by linarith only [sp.toParams.hΔ, hm, hprev]
  obtain ⟨z, hz, q, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before hrun hnc hsvc hawake hf hcatch hnr hms hx hres
      (hu.2.2.1.trans_le hmb) hstock
  have hDC := ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2
  have hDQ := hDC.trans hCQ
  have htq := SA.vote_time_le hr hz ⟨ell, hc, he⟩
  have hslot := (SA.castAt_spec hr hz ⟨hc, he⟩).2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  apply hframe.next_votes_of_supporter hrun hnc hsvc hawake hf hcatch hnr
    hwarm hpos hs₀ hm hmb hz ⟨hc, he⟩ hes hQU hQr hDQ ?_ ?_ hstock
  · intro hQ hh hJD
    have hs₀s : s₀ ≤ s := by clear * - hwarm; omega
    apply regular_slow_next_votes_of_early_witness hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [sp.toParams.hΔ, hm, hprev]) hslow hmb
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i
          (((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s)).trans hlo) hhi,
       fun y hy i hlo hhi => hframe.kind_iff y hy i
          (((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s)).trans hlo) hhi,
       fun y hy i hlo hhi => hframe.root_eq y hy i
          (((SA.ts_le_iff sp).2 (by exact_mod_cast hs₀s)).trans hlo) hhi⟩
      hx hsl ?_ hCQ hz (by linarith only [sp.toParams.hΔ, htq]) hc hQ hh hJD hstock
    simpa only [Compose.frame_of_projAC hrun hx hu.1] using hres
  · intro hA a D' CV' hop hQD
    have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
    have hnext : FrameWindow (tr := tr) (H := H) (sp.ts s₀)
        (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J :=
      ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i hlo
          (by linarith only [sp.toParams.hΔ, hts, hhi]),
       fun y hy i hlo hhi => hframe.kind_iff y hy i hlo
          (by linarith only [sp.toParams.hΔ, hts, hhi]),
       fun y hy i hlo hhi => hframe.root_eq y hy i hlo
          (by linarith only [sp.toParams.hΔ, hts, hhi])⟩
    exact (hnext.optimistic_supporter_later_heads hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [sp.toParams.hΔ, hm, hprev]) (by clear * - hwarm; omega)
      (by clear * -; omega)
      (by linarith only [sp.toParams.hΔ, hmb, hts])
      hz ⟨hc, he⟩ hes hA hop hQD hstock (s + 1) le_rfl le_rfl).1

/-- Later-label propagation for an actual regular origin, with all supporter cases discharged.
Votes start at s+1 and proposals at s+2. The early viable supporter, not a
write-tick witness with an unproved strict timestamp, supplies every propagation step. -/
theorem FrameWindow.regular_later_heads {s₀ s N floor : Nat}
    {kindJ : Prop} {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + sp.Δ)
      floor kindJ J)
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
      SA.SlowLockAt tr.projAC x c s D) (hstock : sp.committeeSize = sp.n) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocks H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y ∈ H, ∀ i ell, tr.projAC.CallAt y i ell → ell.call = .proposal →
        tr.time i = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocks H) D d.head) := by
  have hS := healthy_base_of_service_catch_before hrun hnc hsvc hawake hf hcatch hstock
  have hr := hS.run.localRun
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := SA.ts_succ a
  have hsub {lo hi : Time} (hl : sp.ts s₀ ≤ lo) (hh' : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow (tr := tr) (H := H) lo hi floor kindJ J :=
    ⟨fun y hy i hlo hhi => hframe.floor_eq y hy i (hl.trans hlo) (hhi.trans hh'),
     fun y hy i hlo hhi => hframe.kind_iff y hy i (hl.trans hlo) (hhi.trans hh'),
     fun y hy i hlo hhi => hframe.root_eq y hy i (hl.trans hlo) (hhi.trans hh')⟩
  have h6 : sp.ts s + 6 * sp.Δ ≤ sp.ts N + sp.Δ := by
    have ht := hts hsN
    rw [show s + 2 = (s + 1) + 1 by clear * -; omega, hstep, hstep] at ht
    linarith only [sp.toParams.hΔ, ht]
  have hbase : ∀ y ∈ H, ∀ i e, SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocks H) e.msg D := by
    rcases horigin with ⟨CV, hfast⟩ | hslow
    · exact (hsub le_rfl h6).regular_fast_next_votes hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ (hm.trans (hts hs₀)) (h6.trans hmb) hx hfast .refl hstock
    · exact (hsub le_rfl h6).regular_slow_next_votes hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ hm (h6.trans hmb) hx hslow hstock
  obtain ⟨C, CV, hres, hDC⟩ : ∃ C CV, SA.ResultAt tr.projAC x c s C CV ∧
      Anc (tr.HonestBlocks H) D C := by
    rcases horigin with ⟨CV, ell, C, hu, hconf, hsel, -⟩ | ⟨ell, C, hu, hconf, hsel⟩
    all_goals exact ⟨C, _, ⟨ell, hu, hconf, rfl⟩,
      ((SA.deepest_mem hsel).1.1.2.2).mono (SA.frameIn_of_callAt hr hx hu.1).2⟩
  obtain ⟨z, hz, q, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before hrun hnc hsvc hawake hf hcatch hnr
      (hm.trans (hts (by clear * - hwarm; omega))) hx hres (by
        obtain ⟨ell', hu, -, -⟩ := hres
        exact hu.2.2.1.trans_le (h6.trans hmb)) hstock
  have hDQ := hDC.trans hCQ
  have htq := SA.vote_time_le hr hz ⟨ell, hc, he⟩
  have hslot := (SA.castAt_spec hr hz ⟨hc, he⟩).2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have hqt : sp.ts s₀ ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg q) _).2 (by
      change (s₀ : Int) ≤ sp.slot (tr.time q); rw [hslot]; clear * - hwarm; omega)
  have hmf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change Hᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    clear * - hf hn; omega
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
          change (s₀ : Int) ≤ sp.slot (tr.time i); rw [hsl]; clear * - hwarm hrlo; omega)
      have hhi := SA.vote_time_le hr hy ⟨elly, hcy, hey⟩
      change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at hhi
      rw [hsl] at hhi
      obtain ⟨W, hW, hWr, hRW⟩ := SA.castAt_head_anc hr hy ⟨hcy, hey⟩ (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) Relation.ReflTransGen.refl
      have hRW := hRW.mono hPhiU
      rw [Compose.frame_of_projAC hrun hy hcy] at hRW
      change Anc (tr.HonestBlocks H) (tr.state y i).fg.fcRoot W at hRW
      rw [hroot y hy i hlo (hhi.trans (by linarith only [hts hrN]))] at hRW
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
      rw [hroot y hy i (by rw [hti]; exact hts (by clear * - hwarm hrlo; omega))
        (by rw [hti]; linarith only [hts hrN, sp.toParams.hΔ])] at hRW
      exact hDJ.trans hRW
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := hframe.vote_head_classification_of_service
    hrun hnc hmf hS hnr hz ⟨hc, he⟩
    (by linarith only [hts (show s ≤ N by clear * - hsN; omega), htq])
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by rw [hes]; exact hm.trans (hts hs₀))
    (by rw [hes]; linarith only [hts (show s - 1 ≤ N by clear * - hsN; omega), hmb])
    (by rw [hes]; simp only [SA.freeze]
        have hprev : ((s - 1 : Nat) : Int) = (s : Int) - 1 := by clear * - hpos; omega
        rw [← hprev]
        have := hm.trans (hts hs₀); linarith only [sp.toParams.hΔ, this])
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
            (by linarith only [hts (show s ≤ N by clear * - hsN; omega), htq])).mpr hk),
        hframe.root_eq z hz q hqt (by linarith only [hts (show s ≤ N by clear * - hsN; omega), htq])
          hk] at hroot
    by_cases hJD : kindJ → Anc (tr.HonestBlocks H) J D
    · exact later_heads_of_early_witness hrun hnc hsvc hawake hf hcatch hnr
        (by linarith only [hts (show s₀ ≤ s by clear * - hwarm; omega), sp.toParams.hΔ, hm]) hmb
        (hsub (hts (by clear * - hwarm; omega)) le_rfl) hz (by linarith only [sp.toParams.hΔ, htq])
        hc hHd
        (by rw [← hframe.floor_eq z hz q hqt
              (by linarith only [hts (show s ≤ N by clear * - hsN; omega), htq])]
            exact hvQ.2.2.2) hJD hDQ hbase hstock
    · push Not at hJD
      obtain ⟨hk, hn⟩ := hJD
      exact hrootHeads hk ((SA.anc_total hr.coherent hDQ (hJQ hk)).resolve_right hn)
  · exact hrootHeads hj.1 (hj.2 ▸ hDQ)
  · obtain ⟨hA, l, hl, hls, a, hai, D', CV', hop, -, -, -, hQD⟩ := ho
    have hheads := hframe.optimistic_supporter_later_heads hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [hts (show s₀ ≤ s by clear * - hwarm; omega), sp.toParams.hΔ, hm])
      (by clear * - hwarm; omega) (by clear * - hsN; omega) hmb
      hz ⟨hc, he⟩ hes hA (hes ▸ hop) (hQD.mono hPhi.2) hstock
    intro r hrlo hrN
    constructor
    · intro y hy i ev hv hesv
      obtain ⟨W, hW, hWr, hQW⟩ := (hheads r hrlo hrN).1 y hy i ev hv hesv
      exact ⟨W, hW, hWr, hDQ.trans hQW⟩
    · intro _ y hy i ell' hc' hcall hti d pay hd
      exact hDQ.trans ((hheads r hrlo hrN).2 y hy i ell' hc' hcall hti d pay hd)

/-- Lock passage with the regular residue eliminated. Same-write provenance
supplies the selected raw block, its candidate and the actual regular/optimistic
origin together. Only current-label optimistic writes remain for the causal closure; this
does not assert head=P (`FrameWindow.honest_vote_heads_eq`), causal closure or drain. -/
theorem FrameWindow.current_lock_passage_of_regular_base {s₀ p floor : Nat}
    {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts p + sp.Δ)
      floor kindJ J)
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
    (hB' : B' ∈ ell.frame.tree) (hBr : B'.root = l.block) (hstock : sp.committeeSize = sp.n) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame p) ∧
      (Anc (tr.HonestBlocks H) B' P ∨
        (l.slot = p ∧ ∃ a ≤ i, ∃ D CV, SA.OptimisticLockAt tr.projAC y a p D CV ∧
          sp.ts p ≤ tr.time a ∧ Anc (tr.HonestBlocks H) B' D)) := by
  have hΔ := sp.toParams.hΔ
  have hm₀ : gbar g ≤ sp.ts s₀ := by linarith only [hm, hΔ]
  obtain ⟨hvP, hdomP⟩ := hframe.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch
    hnr hm₀ hsp hp0 hpb hz hdesignated hactual hPs hy hc hes hstock
  refine ⟨hvP, hdomP, ?_⟩
  have hlabel : s₀ + sp.k ≤ l.slot := by clear * - hmargin hlive; omega
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc.1
  have hslot : sp.slot (tr.time i) = p := ((SA.castAt_spec hr hy hc).2.1).symm.trans hes
  by_cases hcurrent : p ≤ l.slot
  · obtain ⟨hs, a, hai, D, CV, hop, ht, C, hC, hCr, hCD⟩ :=
      SA.current_lock_write_readPoint hr hy hc (hes ▸ hp0) hl (hes ▸ hcurrent)
    obtain rfl : C = B' := hr.coherent.1 hC (hPhiU hB') (hCr.trans hBr.symm)
    rw [hes] at hs hop ht
    exact Or.inr ⟨hs, a, hai, D, CV, hop, ht, hCD⟩
  have hold : l.slot + 1 ≤ p := by clear * - hcurrent; omega
  have hk : 0 < sp.k := by clear * - hlive hcurrent; omega
  obtain ⟨l₀, hl₀, hs, B, hB, hBr₀, C, hC, hCr, hCB⟩ :=
    SA.readPoint_locks_below_stored hr hy hc
      (by change 0 < sp.slot (tr.time i); rw [hslot]; exact hp0) l hl
      (by change l.slot ≠ sp.slot (tr.time i); rw [hslot]; clear * - hcurrent; omega)
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
      have he : p = l.slot + 1 := by clear * - hcurrent hn; omega
      have htime := hrun.time_mono hai.le
      rw [he] at hhigh
      simp only [SAParams.ts] at ht hhigh
      push_cast at hhigh
      linarith only [hΔ, ht, htime, hhigh]
    have hDP := (hframe.regular_later_heads hrun hnc hsvc hawake hf hcatch hnr
      hlabel (by clear * - hlive hlabel hcurrent; omega)
      (by clear * - hmargin hlive hcurrent; omega) hm hgap hpb hy horigin hstock p
      (by clear * - hcurrent; omega) le_rfl).2
        hgap z hz ip ellp hcp hcall hti d pay hd
    exact hBA.trans (hAD.trans (hDP.trans hHP))
  rcases ho with ⟨_, CV, hfast | hop⟩ | ⟨_, hslow⟩
  · exact Or.inl (hregular (Or.inl ⟨CV, hfast⟩))
  swap
  · exact Or.inl (hregular (Or.inr hslow))
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by clear * - hmargin hlive; omega)
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
      floor kindJ J :=
    ⟨fun w hw j hlo hhi => hframe.floor_eq w hw j (hts.trans hlo) hhi,
     fun w hw j hlo hhi => hframe.kind_iff w hw j (hts.trans hlo) hhi,
     fun w hw j hlo hhi => hframe.root_eq w hw j (hts.trans hlo) hhi⟩
  have hAP := (optimistic_later_heads_of_witness hrun hnc hsvc hawake hf hcatch hnr
    (hm₀.trans hts) hpb hsub hy hop hAD ha hQ hh hJ (hAQ.mono hW.2) hstock p hold le_rfl).2
      z hz ip ellp hcp hcall hti d pay hd
  exact Or.inl (hBA.trans (hAP.trans hHP))

/-- All actual read locks are below P under the strict earlier-cast IH. The
regular passage is unconditional; only its exact current-label alternative
uses causal minimality. This is the input to head equality (`FrameWindow.honest_vote_heads_eq`),
not head equality itself. -/
theorem FrameWindow.read_locks_below_of_earlier_heads {s₀ p floor : Nat}
    {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts p + sp.Δ)
      floor kindJ J)
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
    (hIH : ∀ x ∈ H, ∀ j < i, ∀ e', SA.VoteAt tr.projAC x j e' →
      e'.msg.slot = p → e'.msg.head = P.root)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocks H) B P := by
  obtain ⟨-, hdom, hpass⟩ := hframe.current_lock_passage_of_regular_base hrun hnc hsvc
    hawake hf hcatch hnr hm hsp hp0 hpb hz hdesignated hactual hPs hy hc hes
    hmargin hl hlive hB hBr hstock
  rcases hpass with h | ⟨hs, -⟩
  · exact h
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hPhi := SA.frameIn_of_callAt hac.localRun hy hc.1
  exact SA.current_read_lock_below_of_earlier_heads hac hy hc hl (hs.trans hes.symm)
    (SA.CommitteeDict.full sp.n) SA.CommitteeP.full
    (SA.four_thirds_full hstock (by have := sp.toParams.hn; omega))
    (hPhi.2 hdom.1.1) (fun x hx j hj e' he' hs' => hIH x hx j hj e' he' (hs'.trans hes))
    (hPhi.2 hB) hBr

/-- Finite frame transport for head equality. The receiver's finalized-ancestor guard
is explicit; old acceptances use Catch and newer ones use their relay deadline.
No settled phase, shared finalized root or frame equality is required. -/
theorem frame_relay_before
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    {x y : Fin sp.n} (hx : x ∈ H) (hy : y ∈ H) {q j : Nat}
    {ellx elly : ACLabel (goldilocksNode sp ro)}
    (hcx : tr.projAC.CallAt x q ellx) (hcy : tr.projAC.CallAt y j elly)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ellx.frame.tree)
    (hg : gbar g + 2 * sp.Δ ≤ tr.time j)
    (hq : tr.time q + sp.Δ ≤ tr.time j) (hjb : tr.time j ≤ b)
    (hF : Anc (tr.HonestBlocks H) elly.frame.F B) : B ∈ elly.frame.tree := by
  have hr := hS.run.localRun
  rcases Compose.frame_anc_accepted hr hx q ellx hcx B hB B .refl with
      hgen | ⟨k, hk, ha⟩
  · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hy j elly hcy
    obtain rfl : B = G := hr.coherent.1 ((SA.frameIn_of_callAt hr hx hcx).2 hB)
      hGU (hgen.trans hGr.symm)
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hF with he | ⟨c, _, hpar⟩
    · exact he ▸ (SA.frameIn_of_callAt hr hy hcy).1.rooted.1
    · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
  have hkt : tr.time k + sp.Δ ≤ tr.time j := by
    have := hr.time_mono hk
    change tr.time k ≤ tr.time q at this
    linarith
  by_cases hnew : gbar g ≤ tr.time k
  · have hdl : tr.projAC.deadline y j (tr.time k) ≤ tr.time j := by
      have hd := Compose.ac_deadline_le_of_restarts (T := tr.projAC) (c := j)
        (fun r _ hrs => hnr y hy r (Compose.projAC_restartAt.mp hrs)) (tr.time k)
      change _ ≤ max (tr.time k) (gbar g) + sp.Δ at hd
      rw [max_eq_left hnew] at hd
      exact hd.trans hkt
    obtain ⟨a, haj, hacc, -⟩ := hS.sync.relay x hx k B ha hnew y hy j elly hcy
      (hdl.trans hjb) hdl hF
    exact SA.mem_tree_of_acceptAt sp hr hy hacc haj hcy hF
  · obtain ⟨a, haj, hacc, -⟩ := hS.catchUp.relay x hx k B ha (not_le.mp hnew)
      y hy j elly hcy hg hjb hF
    exact SA.mem_tree_of_acceptAt sp hr hy hacc haj hcy hF

/-- The finite view comparison at an actual cast. Pre-freeze blocks
relay to the proposer; payload support heads are held at an early ready cast
or relay by the deadline. The statement has no settled/phase assumption. -/
theorem proposal_views_agree_before
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g)) {s : Nat}
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)} {pay : Payload sp.n}
    (hp : SA.ProposalAt tr.projAC z ip ellp pay) (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : P.acPayload = pay)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat}
    {elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hP : P ∈ elly.frame.tree) (hjb : tr.time j ≤ b) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hr := hS.run.localRun
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
  have hslot := (SA.castAt_spec hr hy hc).2.1.symm.trans hes
  have hjlo : sp.ts (s + 1 : Nat) ≤ tr.time j :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg j) _).2 (by rw [hslot])
  have hipb : tr.time ip ≤ b := by rw [hti]; exact hjlo.trans hjb
  have hPhiY := SA.frameIn_of_callAt hr hy hc.1
  have hPhiP := SA.frameIn_of_callAt hr hz hp.1
  apply SA.view_agree_window_before hS.run hz hy hdesignated hp hti hc
    ⟨P, hP, hPs, hpay⟩ (SA.serviceWindowBefore_of_sync hS.sync) (by linarith only [hm, hΔ]) hipb
  · intro B hB _ hstamp hFB
    rw [SA.readPoint_blockStamp_eq hr hy hc] at hstamp
    rcases stamp_origin hr hy j elly hc.1 B hB with hg | ⟨q, -, ellq, hq, hBq, hsq⟩
    · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hz ip ellp hp.1
      obtain rfl : B = G := hr.coherent.1 (hPhiY.2 hB) hGU (hg.trans hGr.symm)
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hFB with he | ⟨c, _, hpar⟩
      · exact he ▸ hPhiP.1.rooted.1
      · exact absurd (hpar.2.2.symm.trans hGp) (Option.some_ne_none _)
    have hqt : tr.time q < sp.ts s + 3 * sp.Δ := by
      rw [hsq] at hstamp
      have ht := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)
      change tr.time q < SA.freeze sp (s + 1) at ht
      simpa only [SA.freeze, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] using ht
    exact frame_relay_before hS hnr hy hz hq hp.1 hBq
      (by rw [hti, hts]; linarith only [hm, hΔ]) (by rw [hti, hts]; linarith only [hqt]) hipb hFB
  · intro v hv B hB hBr hFB
    by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
    · obtain ⟨P', hP', hPs', hsup⟩ := SA.cast_ready hr hy hc (by rw [hes]; exact hearly)
      rw [hes] at hPs' hsup
      obtain rfl := proposal_frame_unique hrun hnc hz hdesignated hactual hPs
        (by clear * -; omega) hy hc.1 hP' hPs'
      have hvs : v.slot + 1 = s + 1 := by
        obtain ⟨d, hd⟩ := hp.2.2
        have hpayeq : pay = SA.voteViewList (tr.projAC.state z ip) ellp.frame
            ((sp.slot (tr.time ip) : Int) - 1) ⊤ := by
          unfold SA.acProposal at hd
          split_ifs at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          exact hd.2.symm
        have hsi : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
        rw [hpayeq, hsi] at hv
        simp only [show ((s + 1 : Nat) : Int) - 1 = (s : Int) by clear * -; omega,
          SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
          List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
          Bool.and_eq_true, decide_eq_true_eq] at hv
        rw [SA.state_pool_slot sp hr hz ip s v hv.1]
      obtain ⟨B', hB', hBr', -⟩ := hsup v (by rw [SA.blockSupport, hpay]; exact hv) hvs
      rwa [hr.coherent.1 (hPhiP.2 hB) (hPhiY.2 hB') (hBr.trans hBr'.symm)]
    · exact frame_relay_before hS hnr hz hy hp.1 hc.1 hB
        (by linarith only [hm, hΔ, hts, hjlo]) (by rw [hti]; exact not_lt.1 hearly) hjb hFB

/-- At two cuts of the `FrameWindow` a viable head transfers whenever it is held in the
receiver's frame. This uses the common floor and kind-J root, not a settled
phase or equality of the frames. -/
theorem FrameWindow.viableHead_transfer {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y z : Fin sp.n} (hy : y ∈ H) (hz : z ∈ H) {i c : Nat}
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    {Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hv : Q ∈ (Node.frame (tr.state z c)).viableHeads)
    (hQ : Q ∈ (Node.frame (tr.state y i)).tree) :
    Q ∈ (Node.frame (tr.state y i)).viableHeads := by
  apply (floor_ancestor_mem_frame hrun hnc hf hy hz hv.1 _ _ hQ.1
    (Relation.ReflTransGen.refl)).2.2
  · rw [hframe.floor_eq y hy i hilo hihi, ← hframe.floor_eq z hz c hclo hchi]
    exact hv.2.2.2
  · intro hm hc
    have hk := (hframe.kind_iff y hy i hilo hihi).mp ⟨hm, hc⟩
    have hzk := (hframe.kind_iff z hz c hclo hchi).mpr hk
    have hroot : (tr.state z c).fg.fcRoot = (tr.state z c).fg.J := ite_eq_left hzk
    rw [hframe.root_eq y hy i hilo hihi hk,
      ← hframe.root_eq z hz c hclo hchi hk, ← hroot]
    exact hv.2.2.1.mono (fun B hB => ⟨z, hz, c, hB⟩)

/-- The full current frame has a viable head above its fork-choice root.
Kind J uses the justification cache; the other cases use the hmax cache.
Unlike a frozen voter domain, the proposal domain cannot lose this witness. -/
theorem full_frame_viable_witness (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    ∃ Q ∈ (Node.frame (tr.state y i)).tree,
      Q ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q := by
  classical
  have hr := Compose.fg_reachable hrun.toLocalRun hy i
  obtain ⟨_, hJt, _, ⟨B, hB, hBJ, hBh⟩, _, ⟨Q, hQ, hQh⟩, _⟩ :=
    Goldilocks.Store.cache_invariants _ _ _ _ hr
  by_cases hk : (tr.state y i).fg.hmax = (tr.state y i).fg.hj + 1 ∧
      ¬ (tr.state y i).fg.Contest
  · obtain ⟨E, hE, hEr, hh⟩ := J_entry_h hr hB
    have he : E = (tr.state y i).fg.J :=
      (Goldilocks.Store.accepted_tree _ _ _ _ hr).2.1.1 hE hJt (hEr.trans hBJ)
    rw [he, hBh] at hh
    have hheight : (tr.state y i).fg.headHeightFloor ≤
        ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h := by
      change (if _ then _ else _) ≤ _
      rw [ite_eq_right hk.2, hk.1]
      clear * - hh; omega
    obtain ⟨hQt, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hJt
      hheight (fun _ _ => Relation.ReflTransGen.refl) hJt Relation.ReflTransGen.refl
    exact ⟨_, hQt, hv, hroot⟩
  · obtain ⟨hQt, hroot, hv⟩ := floor_ancestor_mem_frame hrun hnc hf hy hy hQ
      ((Goldilocks.Store.headHeightFloor_bounds (tr.state y i).fg).2.trans_eq hQh.symm)
      (fun hm hc => (hk ⟨hm, hc⟩).elim) hQ Relation.ReflTransGen.refl
    exact ⟨Q, hQt, hv, hroot⟩

/-- The actual proposal parent is viable in the full current frame. The old
settled-phase supplier is unnecessary: the cache witness and current-frame
AncestorCandidate anchor suffice, including label-(p−1) optimistic locks. -/
theorem proposal_parent_viable_full_frame
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {y : Fin sp.n} (hy : y ∈ H) {i s : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hcall : ell.call = .proposal) (hti : tr.time i = sp.toParams.slotTime s)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 =
      some (d, pay)) : d.head ∈ ell.frame.viableHeads := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  obtain ⟨Q, hQ, hv, hroot⟩ := full_frame_viable_witness hrun hnc hf hy i
  rw [← Compose.frame_of_projAC hrun hy hc] at hQ hv hroot
  exact proposal_head_viable hac.localRun hy hc hcall hti hp
    ⟨(SA.frameIn_of_callAt hac.localRun hy hc).1.fcRoot_mem,
      Relation.ReflTransGen.refl, Q, hQ, hv, hroot⟩

/-- A non-proposal child in the voter's frozen viable domain reflects into
the proposer's full viable tree above the proposer root. The frozen arm uses
relay/Catch; the proposal arm uses the actual viable proposal parent. -/
theorem FrameWindow.frozen_competitor_reflect {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hpb : sp.ts (s + 1 : Nat) ≤ b)
    {X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hX : X ∈ ellp.frame.tree) (hrootX : ellp.frame.Anc ellp.frame.fcRoot X)
    (hBX : B.parent = some X.root) (hne : B ≠ P)
    (hB : B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1))) :
    B ∈ ellp.frame.viableTree ellp.frame.tree := by
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hPhip := SA.frameIn_of_callAt hr hz hcp
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := SA.ts_succ s
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2
      (by rw [← (SA.castAt_spec hr hy hc).2.1, hes])
  have hipl : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have hil : sp.ts s₀ ≤ tr.time i := hipl.trans (hti ▸ hlo)
  have hiph : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by rw [hti]; linarith only [sp.toParams.hΔ]
  have hvQ := proposal_parent_viable_full_frame hrun hnc hf hz hcp hcall
    (s := s + 1) (by rw [sp.slotTime_eq]; simpa [SAParams.ts] using hti) hpay
  have hQt := hPhip.1.viableHeads_subset hvQ
  obtain ⟨⟨hBt, -⟩, _, W, hWV, hvW, hBW⟩ := hB
  have hFB : Anc (tr.HonestBlocks H) ellp.frame.F B :=
    ((hPhip.1.rooted.2 X hX).mono hPhip.2).trans
      (.single ⟨hPhip.2 hX, hPhi.2 hBt, hBX⟩)
  obtain ⟨W', hW't, hW'v, hBW'⟩ : ∃ W' ∈ ellp.frame.tree,
      W' ∈ ellp.frame.viableHeads ∧ Anc (tr.HonestBlocks H) B W' := by
    rcases hWV.2 with hstamp | ⟨P', hP', hP's, hWP'⟩
    · have hFW := hFB.trans (hBW.mono hPhi.2)
      have hWp : W ∈ ellp.frame.tree := by
        rw [SA.readPoint_blockStamp_eq hr hy hc] at hstamp
        rcases stamp_origin hr hy i ell hc.1 W hWV.1 with hg | ⟨q, _, ellq, hcq, hWq, hsq⟩
        · obtain ⟨G, hGU, hGr, hGp⟩ := SA.genesis_mem_of_call sp hr hz ip ellp hcp
          obtain rfl : W = G := hr.coherent.1 (hPhi.2 hWV.1) hGU (hg.trans hGr.symm)
          rcases Relation.ReflTransGen.cases_tail hFW with he | ⟨c, _, hp⟩
          · exact he ▸ hPhip.1.rooted.1
          · exact absurd (hp.2.2.symm.trans hGp) (Option.some_ne_none _)
        have hqt : tr.time q < sp.ts s + 3 * sp.Δ := by
          rw [hsq] at hstamp
          have ht := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)
          change tr.time q < SA.freeze sp (s + 1) at ht
          simpa only [SA.freeze, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] using ht
        exact frame_relay_before hS hnr hy hz hcq hcp hWq
          (by rw [hti, hts]; linarith only [hm, hhigh, hlo])
          (by rw [hti, hts]; linarith only [hqt]) (hti ▸ hpb) hFW
      have hWv' := hvW
      rw [Compose.frame_of_projAC hrun hy hc.1] at hWv'
      have hWp' := hWp
      rw [Compose.frame_of_projAC hrun hz hcp] at hWp'
      have hv := hframe.viableHead_transfer hrun hnc hf hz hy hipl hiph hil hhigh hWv' hWp'
      rw [← Compose.frame_of_projAC hrun hz hcp] at hv
      exact ⟨W, hWp, hv, hBW.mono hPhi.2⟩
    · obtain rfl := proposal_frame_unique hrun hnc hz hdesignated hactual hPs
        (by clear * -; omega) hy hc.1 hP' hP's
      rcases Relation.ReflTransGen.cases_tail (hBW.trans hWP') with he | ⟨Y, hBY, hYP⟩
      · exact (hne he.symm).elim
      · obtain rfl : Y = d.head := hr.coherent.1 (hPhi.2 hYP.1) (hPhip.2 hQt)
          (Option.some.inj (hYP.2.2.symm.trans hparent))
        exact ⟨d.head, hQt, hvQ, Anc.mono hPhi.2 hBY⟩
  have hBp := SA.frame_mem_of_between sp hr.coherent hPhip.1 hPhip.2 hW't hBW' hFB
  exact ⟨hBp, hrootX.tail ⟨hX, hBp, hBX⟩, W', hW't, hW'v,
    SA.anc_tree_of_anc_U hr.coherent hPhip.1 hPhip.2 hBp hBW' hW't⟩

/-- The actual full-frame proposal walk stops at its duty head. This is the
finite walk supplied by acProposal, without any settled-phase interface. -/
theorem proposal_walk_end (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {z : Fin sp.n} (hz : z ∈ H) {ip : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)} (hcp : tr.projAC.CallAt z ip ellp)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hp : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) :
    d.start ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot d.start ∧
      SA.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) ((sp.slot (tr.time ip) : Int) - 1))
        (SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay)
          ((sp.slot (tr.time ip) : Int) - 1)) d.start d.head := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc).localRun
  have hPhi := (SA.frameIn_of_callAt hr hz hcp).1
  have key (A : SA.SAState sp.n) (V : SA.View sp.n) (σ : Int) :
      SA.getAnchor sp A ellp.frame (tr.time ip) ∈ ellp.frame.tree ∧
      ellp.frame.Anc ellp.frame.fcRoot (SA.getAnchor sp A ellp.frame (tr.time ip)) ∧
      SA.WalkEnd (sp := sp) (ellp.frame.viableTree ellp.frame.tree)
        (SA.goldfishScore sp ellp.frame V σ)
        (SA.goldfishEligible sp ellp.frame (tr.time ip) V σ)
        (SA.getAnchor sp A ellp.frame (tr.time ip))
        (SA.getHead sp A ellp.frame (tr.time ip) (ellp.frame.viableTree ellp.frame.tree) V σ) := by
    have hroot := SA.fcRoot_anc_getAnchor hPhi A (tr.time ip)
    have hstart : SA.getAnchor sp A ellp.frame (tr.time ip) ∈ ellp.frame.tree := by
      rcases eq_or_ne ellp.frame.fcRoot (SA.getAnchor sp A ellp.frame (tr.time ip)) with he | he
      · exact he ▸ hPhi.fcRoot_mem
      · exact (Anc.mem hroot he).2
    refine ⟨hstart, hroot, ?_⟩
    exact SA.walkEnd_ghost hPhi.coherent (fun X hX => hX.1)
      (hPhi.finite.subset fun X hX => hX.1)
      (Set.ncard_le_ncard (fun X hX => hX.1) hPhi.finite) _
  unfold SA.acProposal at hp
  split_ifs at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact key _ _ _

/-- Above both anchors, the actual proposal winner remains the voter's winner.
Finite view equality and reflected competitors replace the settled-phase
supplier. The path and frozen proposal are the geometry that head equality consumes. -/
theorem FrameWindow.proposal_suffix_before {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    {X C : SA.Blk sp.n (List (FG.Att sp.n))}
    (hstartX : ellp.frame.Anc d.start X) (hXQ : ellp.frame.Anc X d.head) (hne : X ≠ d.head)
    (hanchorX : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hC : SA.IsBest sp (SA.goldfishScore sp ellp.frame (SA.View.ofLists pay) s)
      {B | B ∈ ellp.frame.viableTree ellp.frame.tree ∧ B.parent = some X.root ∧
        SA.goldfishEligible sp ellp.frame (tr.time ip) (SA.View.ofLists pay) s B} C) :
    SA.IsBest sp (SA.goldfishScore sp ell.frame
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)
      {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some X.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B} C := by
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hPhip := SA.frameIn_of_callAt hr hz hcp
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2
      (by rw [← (SA.castAt_spec hr hy hc).2.1, hes])
  have hviable : ∀ X ∈ ellp.frame.tree, X ∈ ell.frame.viableHeads →
      X ∈ ellp.frame.viableHeads := by
    intro X hXt hXv
    have hiplo : sp.ts s₀ ≤ tr.time ip := by
      rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
    have hiphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
      rw [hti]; linarith only [sp.toParams.hΔ]
    rw [Compose.frame_of_projAC hrun hy hc.1] at hXv
    rw [Compose.frame_of_projAC hrun hz hcp] at hXt ⊢
    exact hframe.viableHead_transfer hrun hnc hf hz hy hiplo hiphi
      (hiplo.trans (hti ▸ hlo)) hhigh hXv hXt
  exact suffix_best_of_proposal_walk hr.coherent hPhip.1 hPhip.2 hPhi.1 hPhi.2
    (SA.proposal_slot (tr := tr.projAC) hti) (proposal_walk_end hrun hnc hz hcp hpay) hPs
    hparent hPv
    (proposal_views_agree_before hrun hnc hS hnr hm hz hdesignated hactual hPs
      ⟨hcp, hcall, d, hpay⟩ hti hpayload hy hc hes hPv.1.1 hib)
    (fun X B hXt hrootX hBX hne hB => hframe.frozen_competitor_reflect hrun hnc hS hnr hf hm
      hs₀ hz hdesignated hactual hPs hcp hcall hti hpay hparent hy hc hes hhigh (hlo.trans hib)
      hXt hrootX hBX hne hB)
    hviable hstartX hXQ hne hanchorX hC

/-- At the viable proposal parent above the voter's root, the voter takes P
and stops. Old competitors reflect to the stopped proposal walk, with the
same scores; no prior unanimity above the parent is assumed. -/
theorem FrameWindow.proposal_stop_before {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1) (hpH : P.proposer ∈ H)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    (hrootQ : Anc (tr.HonestBlocks H) ell.frame.fcRoot d.head) :
    (P ∈ {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B} ∧
      ∀ B ∈ {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some d.head.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B}, B = P) ∧
    ¬ ∃ C, SA.IsBest sp
      (SA.goldfishScore sp ell.frame (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)
      {B | B ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)) ∧
        B.parent = some P.root ∧ SA.goldfishEligible sp ell.frame (tr.time i)
          (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s B} C := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hPhip := SA.frameIn_of_callAt hr hz hcp
  have hslot : sp.slot (tr.time ip) = s + 1 := SA.proposal_slot (tr := tr.projAC) hti
  obtain ⟨hst, hroot, hw⟩ := proposal_walk_end hrun hnc hz hcp hpay
  have hvQ := proposal_parent_viable_full_frame hrun hnc hf hz hcp hcall
    (s := s + 1) (by rw [sp.slotTime_eq]; simpa [SAParams.ts] using hti) hpay
  have hQt := hPhip.1.viableHeads_subset hvQ
  have hQP : Anc (tr.HonestBlocks H) d.head P :=
    .single ⟨hPhip.2 hQt, hPhi.2 hPv.1.1, hparent⟩
  have hQy := SA.frame_mem_of_between sp hr.coherent hPhi.1 hPhi.2 hPv.1.1 hQP
    ((hPhi.1.F_anc_fcRoot.mono hPhi.2).trans hrootQ)
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time i :=
    (SA.ts_le_iff_le_slot sp (hr.time_nonneg i) _).2
      (by rw [← (SA.castAt_spec hr hy hc).2.1, hes])
  have hiplo : sp.ts s₀ ≤ tr.time ip := by
    rw [hti]; exact (SA.ts_le_iff sp).2 (by exact_mod_cast hs₀)
  have hiphi : tr.time ip ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hti]; linarith only [sp.toParams.hΔ]
  have hvQ' := hvQ
  have hQy' := hQy
  rw [Compose.frame_of_projAC hrun hz hcp] at hvQ'
  rw [Compose.frame_of_projAC hrun hy hc.1] at hQy'
  have hvQy := hframe.viableHead_transfer hrun hnc hf hy hz
    (hiplo.trans (hti ▸ hlo)) hhigh hiplo hiphi hvQ' hQy'
  rw [← Compose.frame_of_projAC hrun hy hc.1] at hvQy
  have hng : ∀ B ∈ ell.frame.tree, B.parent ≠ none → B.root ≠ sp.genesisRoot := by
    intro B hB hpar hg
    rw [Compose.honest_eq_genesis hrun hr.coherent (hPhi.2 hB) hg] at hpar
    exact hpar rfl
  have hv := proposal_views_agree_before hrun hnc hS hnr hm hz hdesignated hactual hPs
    ⟨hcp, hcall, d, hpay⟩ hti hpayload hy hc hes hPv.1.1 hib
  have hcore := SA.stop_core hac hy hc hes hPs hparent hpH hng hPv
  simp only [show ((s + 1 : Nat) : Int) - 1 = (s : Int) by clear * -; omega] at hcore
  apply hcore
  intro B hB hBQ hBs
  exact old_child_ineligible_of_views hPhip.1 hpay hslot hv.1 hv.2.1 hv.2.2
    ((SA.castAt_spec hr hy hc).2.1.symm.trans hes) hvQy
    (hframe.frozen_competitor_reflect hrun hnc hS hnr hf hm hs₀ hz hdesignated
      hactual hPs hcp hcall hti hpay hparent hy hc hes hhigh (hlo.trans hib)
      hQt (hroot.trans (hw.anc (fun X hX => hX.1) hst)) hBQ
      (fun he => by rw [he, hPs] at hBs; clear * - hBs; omega) hB) hB.1.1 hBQ hBs

/-- A voter that reaches the actual proposal-parent path has head P. All
suffix and stop obligations are discharged from finite `FrameWindow` data; reaching
the path is the remaining anchor-prefix obligation, not a head-equality premise. -/
theorem FrameWindow.vote_head_eq_of_path {s₀ s floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ)
      floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hS : SA.HealthyBaseUpTo tr.projAC H (tr.HonestBlocks H) proposer g b)
    (hnr : NoRestartAfter tr H (gbar g))
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    (hm : gbar g + 2 * sp.Δ ≤ sp.ts s) (hs₀ : s₀ ≤ s + 1)
    {z : Fin sp.n} (hz : z ∈ H) (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1) (hpH : P.proposer ∈ H)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hcp : tr.projAC.CallAt z ip ellp) (hcall : ellp.call = .proposal)
    (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay)) (hpayload : P.acPayload = pay) (hparent : P.parent = some d.head.root)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = s + 1)
    (hhigh : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ) (hib : tr.time i ≤ b)
    (hPv : P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
    {X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hstartX : ellp.frame.Anc d.start X) (hXQ : ellp.frame.Anc X d.head)
    (haX : ell.frame.Anc (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) X)
    (hXE : ell.frame.Anc X (SA.getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame (s + 1)))
      (SA.mergedVoteView sp e.readPoint ell.frame (s + 1)) s)) : e.msg.head = P.root := by
  have hr := hS.run.localRun
  have hPhi := SA.frameIn_of_callAt hr hy hc.1
  have hPhip := SA.frameIn_of_callAt hr hz hcp
  have hrootQ : Anc (tr.HonestBlocks H) ell.frame.fcRoot d.head :=
    (Anc.mono hPhi.2 ((SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)).trans haX)).trans
      (hXQ.mono hPhip.2)
  obtain ⟨hstepP, hstopP⟩ := hframe.proposal_stop_before hrun hnc hS hnr hf hm hs₀
    hz hdesignated hactual hPs hpH hcp hcall hti hpay hpayload hparent
    hy hc hes hhigh hib hPv hrootQ
  have heq := getHead_eq_of_proposal_path hPhip.1 hPhip.2 hPhi.1 hPhi.2
    (SA.proposal_slot (tr := tr.projAC) hti) (proposal_walk_end hrun hnc hz hcp hpay)
    (fun _ _ hSX hXQ' hne haX' hC => hframe.proposal_suffix_before hrun hnc hS hnr hf hm hs₀
      hz hdesignated hactual hPs hcp hcall hti hpay hpayload hparent hy hc hes hhigh hib hPv
      hSX hXQ' hne haX' hC)
    hstepP hstopP hstartX hXQ haX hXE
  have hspec := SA.castAt_head_of_viable hr hy hc (hes ▸ ⟨P, hPv⟩)
  rw [hes, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by clear * -; omega] at hspec
  exact hspec.trans (congrArg Block.root heq)

/-- The actual vote anchor is below P under the strict earlier-cut IH.
Stored lock images use regular/optimistic passage; current-slot images use
read-point provenance, never post-cast self-admission. -/
theorem FrameWindow.vote_anchor_below_of_earlier_heads {s₀ p floor : Nat}
    {kindJ : Prop} {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts p + sp.Δ)
      floor kindJ J)
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
    (hIH : ∀ x ∈ H, ∀ j < i, ∀ e', SA.VoteAt tr.projAC x j e' →
      e'.msg.slot = p → e'.msg.head = P.root) (hstock : sp.committeeSize = sp.n) :
    Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i)) P := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hPhi := SA.frameIn_of_callAt hac.localRun hy hc.1
  have hm₀ : gbar g ≤ sp.ts s₀ := by
    have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
    linarith only [hm, hΔ]
  have hPv := (hframe.proposal_viable_at_cast hrun hnc hsvc hawake hf hcatch hnr hm₀
    hsp hp0 hpb hz hdesignated hactual hPs hy hc hes hstock).1
  have hfP : Anc (tr.HonestBlocks H) ell.frame.fcRoot P :=
    Anc.mono hPhi.2 (hPhi.1.fcRoot_anc_viableHeads P hPv)
  have hlk : ∀ B ∈ SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i),
      Anc (tr.HonestBlocks H) B P := by
    intro B hB
    obtain ⟨l, hl, B₀, hB₀, hB₀r, hlive, rfl⟩ := SA.mem_liveLockBlocks_of_wf hPhi.1
      (SA.castAt_readPoint_locksWF hac.localRun hy hc) hB
    have hslot := (SA.castAt_spec hac.localRun hy hc).2.1
    have hB₀P := hframe.read_locks_below_of_earlier_heads hrun hnc hsvc hawake hf hcatch
      hnr hm hsp hp0 hpb hz hdesignated hactual hPs hy hc hes hmargin hIH hl
      (by rw [← hes, hslot]; exact hlive) hB₀ hB₀r hstock
    exact (Anc.mono hPhi.2 (SA.viableAncestor_anc hPhi.1 hB₀).2).trans hB₀P
  unfold SA.getAnchor
  rcases hD : SA.deepest ell.frame
      (SA.liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i) ∪ {ell.frame.fcRoot})
      with _ | D
  · exact hfP
  · rcases (SA.deepest_mem hD).1 with h | h
    · exact hlk D h
    · exact (Set.mem_singleton_iff.1 h) ▸ hfP

/-- The voter reaches another honest finalized tip when its anchor is below
that tip. The `FrameWindow` supplies the floor for every viable head; the witness is in
the actual frozen domain. This is the unequal-root prefix, without scores. -/
theorem FrameWindow.finalized_anc_head_at_cast {lo hi : Time} {floor : Nat}
    {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hrun : GoldilocksRun proposer dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {z y : Fin sp.n} (hz : z ∈ H) (hy : y ∈ H) {c i : Nat}
    (hclo : lo ≤ tr.time c) (hchi : tr.time c ≤ hi)
    (hilo : lo ≤ tr.time i) (hihi : tr.time i ≤ hi)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e)
    {Y : SA.Blk sp.n (List (FG.Att sp.n))}
    (hY : Y ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot)
    (hvY : Y ∈ ell.frame.viableHeads)
    (haF : Anc (tr.HonestBlocks H) (SA.getAnchor sp e.readPoint ell.frame (tr.time i))
      (tr.state z c).fg.F) :
    Anc (tr.HonestBlocks H) (tr.state z c).fg.F
      (SA.getHead sp e.readPoint ell.frame (tr.time i)
        (ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot))
        (SA.mergedVoteView sp e.readPoint ell.frame e.msg.slot) ((e.msg.slot : Int) - 1)) := by
  have hac := Compose.goldilocks_ac_projection sp ro dg H tr proposer hrun hnc
  have hPhi := SA.frameIn_of_callAt hac.localRun hy hc.1
  have hfloor : ∀ Q ∈ ell.frame.viableHeads,
      ell.frame.Anc (tr.state z c).fg.F Q := by
    intro Q hQ
    have hV := hQ
    rw [Compose.frame_of_projAC hrun hy hc.1] at hV
    have hFQ := hframe.finalized_below_viable hrun hnc hf hz hy hclo hchi hilo hihi hV
    have hFt := SA.frame_mem_of_between sp hac.localRun.coherent hPhi.1 hPhi.2
      (hPhi.1.viableHeads_subset hQ) hFQ
      (Anc.mono hPhi.2 (hPhi.1.F_anc_fcRoot.trans
        (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))) |>.trans haF)
    exact SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hFt hFQ
      (hPhi.1.viableHeads_subset hQ)
  have hFt := SA.mem_of_anc (hfloor Y hvY) (hPhi.1.viableHeads_subset hvY)
  have hat : SA.getAnchor sp e.readPoint ell.frame (tr.time i) ∈ ell.frame.tree := by
    by_cases he : ell.frame.fcRoot = SA.getAnchor sp e.readPoint ell.frame (tr.time i)
    · exact he ▸ hPhi.1.fcRoot_mem
    · exact (Anc.mem (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i)) he).2
  exact Anc.mono hPhi.2 (SA.finalized_floor_anc_getHead hPhi.1 (fun _ h => h.1)
    (SA.voterBlockTree_anc hac.localRun hy hc) hfloor hY hvY (hfloor Y hvY)
    e.readPoint (tr.time i) _ _ (SA.fcRoot_anc_getAnchor hPhi.1 e.readPoint (tr.time i))
    (SA.anc_tree_of_anc_U hac.localRun.coherent hPhi.1 hPhi.2 hat haF hFt))

end Consensus.Goldilocks.Healing

end
