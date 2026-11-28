module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.VoteReceipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run

public section

/-! # Vote domains from independently observed roots and seeds -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- An origin above the frame's finalized tip is held by every later-label honest voter. -/
theorem high_origin_held_at_vote_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x y : Fin sp.n} {r l k : Nat} {O : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g x r l O) (hrb : tr.time r ≤ b)
    (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) (hl : l < e.msg.slot)
    (hFO : Anc (tr.HonestBlocksAt H) ell.frame.F O) :
    O ∈ (tr.state y k).fg.tree := by
  obtain ⟨W, hW, hOW⟩ := high_origin_frozen_head_at hp ho hrb hy hc hl hFO
  have hWy := (frame_tree_subset_at hp.run hp.noColl hy hc.1).2 hW.1
  exact mem_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg k)
    (fun _ hq => hp.run.time_mono hq.le) hy hOW hWy

/-- A viable frozen descendant yields the target's viable vote-domain membership. -/
theorem vote_viable_of_root_at {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y k ell e) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hcomp : Compatible (tr.HonestBlocksAt H) ell.frame.F B)
    (hK2 : (∃ D ∈ AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot,
        Anc (tr.HonestBlocksAt H) B D ∧ (tr.state y k).fg.IsViable D) ∨
      Anc (tr.HonestBlocksAt H) B ell.frame.F) :
    B ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame e.msg.slot) ∨
      Anc (tr.HonestBlocksAt H) B ell.frame.F := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := (hac.upTo (hrun.time_nonneg k)).localRun
  have hc' := AC.upTo_castAt.mpr (And.intro le_rfl hc)
  obtain ⟨hPhi, hPhiTree⟩ := frame_tree_subset_at hrun hnc hy hc.1
  have hPhiU := Outcome.frame_tree_subset hrun hy hc.1
  have hfr := Outcome.frame_of_call hrun hy hc.1
  rcases hK2 with ⟨D, hD, hBD, hvD⟩ | h
  · rcases hcomp with hfB | hBf
    · have hDt : D ∈ ell.frame.tree := hD.1
      have hFB := hfB
      have hBt := AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hDt hBD hFB
      have hPhiBD := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hBt hBD hDt
      have hPhifB := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.rooted.1 hfB hBt
      refine Or.inl ⟨AC.voterBlockTree_ancU hr.toU hrun.vstart hy hc' D hD B hPhiBD,
        hPhifB, D, hD, ?_, hPhiBD⟩
      have hfD := hPhifB.trans hPhiBD
      rw [hfr] at hDt hfD ⊢
      exact ⟨hDt.1, hDt.2, hvD⟩
    · exact Or.inr hBf
  · exact Or.inr h

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
