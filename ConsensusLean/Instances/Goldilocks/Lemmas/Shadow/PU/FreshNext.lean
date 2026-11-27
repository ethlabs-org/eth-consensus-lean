module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshNext
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FreshViable
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Next-slot extension over the stock shadow window -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

/-- The stock window supplies full-frame geometry for every honest next-slot shadow cast. -/
theorem unanimous_next_votes_at' {K : AC.CommitteeDict sp.n}
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
  refine Core.unanimous_next_votes_at hrun.toCore hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hK ?_
  intro y j ell e hy hc hs hjb
  have hΔ := sp.toParams.hΔ
  have hr := hrun.toCore.acRun_upTo hnc (hrun.time_nonneg j)
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j ell e := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hsl := (AC.castAt_specU hr.localRun.toU hy hc').2.1
  change e.msg.slot = sp.slot (tr.time j) at hsl
  have hlo : sp.ts (u + 1 : Nat) ≤ tr.time j :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega)
  have hhi : tr.time j ≤ sp.ts (u + 1 : Nat) + sp.Δ := by
    have ht := (Compose.cast_head_fcRoot hr.localRun hr.vstart hy hc').2
    rwa [hs] at ht
  obtain ⟨hvi, _, hv⟩ := proposal_viable_after_votes_at' hframe hrun hnc hsvc hf hnr
    (by linarith) hTb hz hdes hP hPs hy hc.1
    (by simp only [ACParams.ts] at hlo ⊢; push_cast at hlo; linarith) (by linarith)
  exact ⟨hvi.2.1.mono (fun Q hQ => hrun.toCore.upTo_subset (hrun.time_nonneg j)
    ((AC.frameIn_of_callAt hr.localRun hy hc'.1).2 hQ)), hv⟩

end Consensus.Goldilocks.Healing.Growing.Shadow

end
