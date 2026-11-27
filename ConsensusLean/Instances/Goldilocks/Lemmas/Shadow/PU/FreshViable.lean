module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.FollowCast
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Full-frame proposal viability and selection over the stock shadow window -/

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace' sp ro} {hold : Time}

/-- The stock-window cast supplier supplies the shadow call's viability witness. -/
theorem proposal_viable_after_votes_at'
    {ini : Fin sp.n → (goldilocksNode' sp ro).State}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u)
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp ro)} (hc : tr.projAC.CallAt y k ell)
    (hlo : sp.ts u + 2 * sp.Δ ≤ tr.time k)
    (hhi : tr.time k ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧ ell.frame.viableAncestor P = P ∧
      P ∈ ell.frame.viableHeads := by
  have hΔ := sp.toParams.hΔ
  have hshortT : sp.ts u + sp.Δ ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; linarith
  obtain ⟨hPt, hroot, hv⟩ := KernelProof.proposal_viable_at_call_at' hframe hrun hnc hsvc hf hnr
    hgu le_rfl hshortT hTb hz hdes hP hPs hy hc (by linarith) hhi
    (fun h => absurd h (by linarith))
  exact Core.proposal_viable_after_votes_at hrun.toCore hnc hy hc hPt hroot hv

/-- Actual shadow updates instantiate the shared unanimous-pool selection proof. -/
theorem unanimous_update_selection_at' {K : AC.CommitteeDict sp.n}
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun' proposer dg H tr
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
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode' sp ro)} (hu : AC.UpdateAt tr.projAC y k u ell)
    (hK : CommitteeHalfUpTo tr H K g b) :
    P ∈ ell.frame.viableTree ell.frame.tree ∧
      AC.getConfirmation sp (tr.projAC.state y k) ell.frame u = some P ∧
      AC.fastSelect sp (tr.projAC.state y k) ell.frame u P = some P ∧
      ell.frame.viableAncestor P = P := by
  have ht : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  obtain ⟨hvi, hva, _⟩ := proposal_viable_after_votes_at' hframe hrun hnc hsvc hf hnr
    (by linarith [sp.toParams.hΔ]) hTb hz hdes hP hPs hy hu.1
    (by rw [ht]; linarith [sp.toParams.hΔ]) (by rw [ht, hT])
  exact Core.unanimous_update_selection_at hframe hrun.toCore hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hy hu hK hvi hva

end Consensus.Goldilocks.Healing.Growing.Shadow

end
