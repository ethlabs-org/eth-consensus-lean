module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularClassification
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # P-U regular-later assembly

V-B8 remains unresolved. The result-supporter and classification suppliers live in
`RegularClassification` so that `RegularVotes` can consume them without a cycle.
The exact fast/slow signature handoff for `RegularVotes` is recorded in that supplier's
header comment. They are not active declarations here. The witness family belongs to
`WitnessFamily`; the direct caller must supply its source-window lower bound `halo`.
No reachable counterexample or run-level proof is claimed.
-/

namespace Consensus.Goldilocks.Healing.PU

open AC (ACParams ReplayOrder Payload gbar)
open _root_.Consensus.Goldilocks.Growing
open _root_.Consensus.Goldilocks.Healing.Growing

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- V-B8, interface only. No proof or reachable counterexample is claimed. -/
theorem regular_later_heads_at'
    {g ΔF b : Time} {s₀ s N M : Nat} {isTop : Prop}
    {J D : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts N + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Growing.GoldilocksRun' proposer dg H tr (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : Healing.Growing.ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hnr : Healing.Growing.NoRestartAfter tr H (gbar g))
    (hwarm : s₀ + sp.k ≤ s) (hpos : 0 < s) (hs₀ : s₀ ≤ s - 1)
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsN : s + 2 ≤ N)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {x : Fin sp.n} {c : Nat} (hx : x ∈ H (tr.time c))
    (horigin : (∃ CV, AC.FastUpdateAt tr.projAC x c s D CV) ∨
      AC.SlowLockAt tr.projAC x c s D) (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ r, s + 1 ≤ r → r ≤ N →
      (∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e → e.msg.slot = r →
        AC.VoteExtends (tr.HonestBlocksAt H) e.msg D) ∧
      (s + 2 ≤ r → ∀ y i ell, y ∈ H (tr.time i) → tr.projAC.CallAt y i ell →
        ell.call = .proposal → tr.time i = sp.ts r → ∀ d pay,
        (AC.acProposal sp (tr.projAC.state y i) ell.frame (tr.time i)).2 = some (d, pay) →
          Anc (tr.HonestBlocksAt H) D d.head) := by
  have hΔ := sp.toParams.hΔ
  have hts {a b : Nat} (hab : a ≤ b) : sp.ts a ≤ sp.ts b :=
    (AC.ts_le_iff sp).mpr (by exact_mod_cast hab)
  have hstep (a : Nat) : sp.ts (a + 1 : Nat) = sp.ts a + 4 * sp.Δ := AC.ts_succ a
  have hsub {lo hi : Time} (hl : sp.ts s₀ ≤ lo) (hh : hi ≤ sp.ts N + sp.Δ) :
      FrameWindow' tr H lo hi M isTop J := hframe.mono hl hh
  have h6 : sp.ts s + 6 * sp.Δ ≤ sp.ts N + sp.Δ := by
    have ht := hts hsN
    rw [show s + 2 = (s + 1) + 1 by omega, hstep, hstep] at ht
    linarith
  have hbase : ∀ y i e, y ∈ H (tr.time i) → AC.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
    rcases horigin with ⟨CV, hfast⟩ | hslow
    · exact regular_fast_next_votes_at' (hsub le_rfl h6) hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ (hm.trans (hts hs₀)) (h6.trans hmb) hx hfast .refl hK
    · exact regular_slow_next_votes_at' (hsub le_rfl h6) hrun hnc hsvc hawake hf hcatch hnr
        hwarm hpos hs₀ hm (h6.trans hmb) hx hslow hK
  have hAC := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  obtain ⟨C, CV, hres, hDC⟩ : ∃ C CV, AC.ResultAt tr.projAC x c s C CV ∧
      Anc (tr.HonestBlocksAt H) D C := by
    rcases horigin with ⟨CV, ell, C, hu, hconf, hsel, -⟩ | ⟨ell, C, hu, hconf, hsel⟩
    all_goals exact ⟨C, _, ⟨ell, hu, hconf, rfl⟩,
      ((AC.deepest_mem hsel).1.1.2.2).mono
        (AC.frameIn_of_callU (hAC.upTo (hrun.time_nonneg c)).localRun.toU hx
          ((Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hu.1⟩)).2⟩
  have hs₀s : s₀ ≤ s := by omega
  obtain ⟨z, q, hz, hqc, e, ⟨ell, hc, he⟩, -, hes, Q, hQU, hQr, hCQ⟩ :=
    result_honest_supporter_before_at' hrun hnc hsvc hawake hf hcatch hnr
      (hm.trans (hts hs₀s)) hx hres (by
        obtain ⟨ell', hu, -, -⟩ := hres
        exact hu.2.2.1.trans_le (h6.trans hmb)) hK
  have hDQ := hDC.trans hCQ
  have hr := (hAC.upTo (hrun.time_nonneg q)).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc, he⟩
  have htq := AC.vote_time_leU hr.toU hz ⟨ell, hc'.1, he⟩
  have hslot := (AC.castAt_specU hr.toU hz hc').2.1.symm.trans hes
  change sp.slot (tr.time q) = s at hslot
  change tr.time q ≤ sp.ts (sp.slot (tr.time q)) + sp.Δ at htq
  rw [hslot] at htq
  have hqt : sp.ts s ≤ tr.time q :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg q) _).mpr (by rw [hslot])
  have hqhi : tr.time q ≤ sp.ts N + sp.Δ := by
    have := hts (show s ≤ N by omega)
    linarith
  obtain ⟨Hd, hHd, hHdr, hclass⟩ := vote_head_classification_of_service_at' hframe
    hrun hnc hsvc hawake hf hcatch hnr hz ⟨hc, he⟩ hqhi (hqhi.trans hmb)
    (hes ▸ hwarm) (hes ▸ hpos) (hes ▸ hs₀) (by rw [hes]; exact hm.trans (hts hs₀))
    (by
      rw [hes]; simp only [AC.freeze]
      rw [show (s : Int) - 1 = ((s - 1 : Nat) : Int) by omega]
      have := hm.trans (hts hs₀)
      linarith) hK
  have hPhi := AC.frameIn_of_callU (hAC.upTo (hrun.time_nonneg q)).localRun.toU hz
    ((Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩)
  have hcoh := Coherence.honestBlocksAt_coherent' hrun hnc
  have hEQ : Hd = Q := hcoh.1 (hPhi.2 hHd) hQU (hHdr.trans hQr.symm)
  rw [hEQ] at hHd hclass
  rcases hclass with hv | ho
  · exact Shadow.PU.Growing.later_heads_of_early_witness_at' hrun hnc hsvc hawake hf
      hcatch hnr (by have := hts hs₀s; linarith) hmb (hsub (hts hs₀s) le_rfl)
      hz hqt (by linarith) hc hHd hv.2 hDQ hbase hK
  · obtain ⟨hA, l, hl, hls, a, hai, D', CV', hza, hop, -, -, -, hQD⟩ := ho
    have hheads := Shadow.PU.Growing.optimistic_supporter_later_heads_at' hframe hrun hnc
      hsvc hawake hf hcatch hnr (by have := hts hs₀s; linarith) hs₀s (by omega) hmb
      hz hza ⟨hc, he⟩ hes hA (hes ▸ hop) (hQD.mono hPhi.2) hK
    intro r hrlo hrN
    constructor
    · intro y i ev hy hv hesv
      obtain ⟨W, hW, hWr, hQW⟩ := (hheads r hrlo hrN).1 y i ev hy hv hesv
      exact ⟨W, hW, hWr, hDQ.trans hQW⟩
    · intro _ y i ell' hy hc' hcall hti d pay hd
      exact hDQ.trans ((hheads r hrlo hrN).2 y i ell' hy hc' hcall hti d pay hd)

end Consensus.Goldilocks.Healing.PU

end
