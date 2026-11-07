module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularLaterRoot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularSlowBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowInduction
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RegularClassification
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Later-label propagation from a historical regular write -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The fast and slow next-vote bases propagate through independently honest later calls. -/
theorem regular_later_heads_at
    {g ΔF b : Time} {s₀ s N floor : Nat} {kindJ : Prop}
    {J D : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsN : s + 2 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (horigin : (∃ CV, SA.FastUpdateAt tr.projAC x c s D CV) ∨
      SA.SlowLockAt tr.projAC x c s D) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = r →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (SA.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) D d.head) := by
  have hΔ := sp.toParams.hΔ
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (SA.ts_le_iff sp).mpr (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := SA.ts_succ a
  have hsub {lo hi : Time} (hl : sp.ts s₀ ≤ lo) (hh : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow tr H lo hi floor kindJ J :=
    ⟨fun y i hy hlo hhi => hframe.floor_eq y i hy (hl.trans hlo) (hhi.trans hh),
     fun y i hy hlo hhi => hframe.kind_iff y i hy (hl.trans hlo) (hhi.trans hh),
     fun y i hy hlo hhi => hframe.root_eq y i hy (hl.trans hlo) (hhi.trans hh)⟩
  have h6 : sp.ts s + 6 * sp.Δ ≤ sp.ts N + sp.Δ := by
    have ht := hts hsN
    rw [show s + 2 = (s + 1) + 1 by omega, hstep, hstep] at ht
    linarith
  have hbase : ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
    rcases horigin with ⟨CV, hfast⟩ | hslow
    · exact regular_fast_next_votes_at (hsub le_rfl h6) hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ (hm.trans (hts hs₀)) (h6.trans hmb) hx hfast .refl
    · exact Growing.FrameWindow.regular_slow_next_votes_at (hsub le_rfl h6) hrun hnc hsvc
        hawake hf hcatch hnr hwarm hpos hs₀ hm (h6.trans hmb) hx hslow
  obtain ⟨C, CV, hres, hDC⟩ : ∃ C CV, SA.ResultAt tr.projAC x c s C CV ∧
      Anc (tr.HonestBlocksAt H) D C := by
    rcases horigin with ⟨CV, ell, C, hu, hconf, hsel, -⟩ | ⟨ell, C, hu, hconf, hsel⟩
    all_goals exact ⟨C, _, ⟨ell, hu, hconf, rfl⟩,
      ((SA.deepest_mem hsel).1.1.2.2).mono (frameIn_at hrun hnc hx hu.1).2⟩
  have hs₀s : s₀ ≤ s := by omega
  obtain ⟨z, q, hz, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before_at hrun hnc hsvc hawake hf hcatch hnr
      (hm.trans (hts hs₀s)) hx hres (by
        obtain ⟨ell', hu, -, -⟩ := hres
        exact hu.2.2.1.trans_le (h6.trans hmb))
  have hDQ := hDC.trans hCQ
  have hr := (acRun_upTo hrun hnc (hrun.time_nonneg q)).localRun
  have hc' := SA.upTo_castAt.mpr ⟨le_rfl, hc, he⟩
  have htq := SA.vote_time_le hr hz ⟨ell, hc'.1, he⟩
  have hslot := (SA.castAt_spec hr hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have hqt : sp.ts s₀ ≤ tr.time q :=
    (SA.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).mpr (by rw [hslot]; omega)
  have hqhi : tr.time q ≤ sp.ts N + sp.Δ := by have := hts (show s ≤ N by omega); linarith
  have hprev : sp.ts ((s - 1 : Nat) : Int) = sp.ts s - 4 * sp.Δ := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one, SA.ts_sub_one]
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := vote_head_classification_of_service_at hframe
    hrun hnc hsvc hawake hf hcatch hnr hz ⟨hc, he⟩ hqhi (hqhi.trans hmb)
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by rw [hes]; exact hm.trans (hts hs₀))
    (by
      rw [hes]; simp only [SA.freeze]
      rw [show (s : Int) - 1 = ((s - 1 : Nat) : Int) by omega]
      have := hm.trans (hts hs₀)
      linarith)
  have hPhi := frameIn_at hrun hnc hz hc
  have hcoh := honestBlocksAt_coherent hrun hnc
  have hEQ : Hd = Q := hcoh.1 (hPhi.2 hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | hj | ho
  · have hvQ := hv.2
    have hJQ : kindJ → Anc (tr.HonestBlocksAt H) J Q := by
      intro hk
      have hroot := (hPhi.1.fcRoot_anc_viableHeads Q hvQ).mono hPhi.2
      rw [frame_of_projAC_at hrun hz hc] at hroot
      change Anc (tr.HonestBlocksAt H) (tr.state z q).fg.fcRoot Q at hroot
      rwa [show (tr.state z q).fg.fcRoot = (tr.state z q).fg.J from
          ite_eq_left ((hframe.kind_iff z q hz hqt hqhi).mpr hk),
        hframe.root_eq z q hz hqt hqhi hk] at hroot
    by_cases hJD : kindJ → Anc (tr.HonestBlocksAt H) J D
    · apply Growing.later_heads_of_early_witness_at hrun hnc hsvc hawake hf hcatch hnr
        (by have := hts hs₀s; linarith) hmb (hsub (hts hs₀s) le_rfl) hz
        (by linarith) hc hHd ?_ hJD hDQ hbase
      rw [frame_of_projAC_at hrun hz hc] at hvQ
      rw [← hframe.floor_eq z q hz hqt hqhi]
      exact hvQ.2.2.2
    · push Not at hJD
      obtain ⟨hk, hn⟩ := hJD
      exact later_heads_of_common_root_at hframe hrun hnc hs₀s hk
        ((Anc.total hcoh hDQ (hJQ hk)).resolve_right hn)
  · exact later_heads_of_common_root_at hframe hrun hnc hs₀s hj.1 (hj.2 ▸ hDQ)
  · obtain ⟨hA, l, hl, hls, a, hai, D', CV', hza, hop, -, -, -, hQD⟩ := ho
    have hheads := optimistic_supporter_later_heads_at hframe hrun hnc hsvc hawake hf hcatch hnr
      (by have := hts hs₀s; linarith) hs₀s (by omega) hmb hz hza ⟨hc, he⟩ hes hA
      (hes ▸ hop) (hQD.mono hPhi.2)
    intro r hrlo hrN
    constructor
    · intro y i ev hy hv hesv
      obtain ⟨W, hW, hWr, hQW⟩ := (hheads r hrlo hrN).1 y i ev hy hv hesv
      exact ⟨W, hW, hWr, hDQ.trans hQW⟩
    · intro _ y i ell' hy hc' hcall hti d pay hd
      exact hDQ.trans ((hheads r hrlo hrN).2 y i ell' hy hc' hcall hti d pay hd)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
