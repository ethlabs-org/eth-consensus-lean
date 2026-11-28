module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.ParentStop
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SuffixTransfer
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AgreeSetting
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.BestChild
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.StopCore
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal viability and view selection

Viable proposals, reflected competitors and the stop-at-parent argument used by unanimity. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams Payload)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {K : AC.CommitteeDict sp.n} {g ΔF a : Time}

/-- Finite winner transport along the viable proposal chain. -/
theorem ResetPremisesUpTo.reset_winner_voter_tree {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u)
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocks H) C P)
    (haC : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u) := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  obtain ⟨hPhi, hPhiU⟩ := AC.frameIn_of_callAt hr hy hc.1
  have hfC := ((AC.fcRoot_anc_getAnchor hPhi e.readPoint (tr.time j)).mono hPhiU).trans haC
  have hFC := hfC
  have hCt := AC.frame_mem_of_between sp hr.coherent hPhi hPhiU hP.1.1 hCP hFC
  have hCP' := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hCt hCP hP.1.1
  have hfC' := AC.anc_tree_of_anc_U hr.coherent hPhi hPhiU hPhi.rooted.1 hfC hCt
  obtain ⟨W, hW, hWv, hPW⟩ := hP.2.2
  have hCs : C ∈ AC.voterBlockTree sp e.readPoint ell.frame u := by
    rw [← hes] at hP ⊢
    exact AC.voterBlockTree_ancU hr.toU hp.run.vstart hy hc P hP.1 C hCP'
  exact ⟨hCs, hfC', W, hW, hWv, hCP'.trans hPW⟩

/-- Any ancestor of a viable current proposal above the voter's anchor is in its viable tree.
This is the winner-domain transport used by suffix comparison. -/
theorem reset_winner_voter_tree
    (hp : ResetPremises tr H K proposer dg g ΔF a)
    {y : Fin sp.n} (hy : y ∈ H) {j u : Nat} {ell : ACLabel (goldilocksNode sp)}
    {e : AC.Em sp (List (FG.Att sp.n))} (hc : AC.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u)
    {P C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u))
    (hCP : Anc (tr.HonestBlocks H) C P)
    (haC : Anc (tr.HonestBlocks H) (AC.getAnchor sp e.readPoint ell.frame (tr.time j)) C) :
    C ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame u) :=
  (hp.toUpTo tr H le_rfl).reset_winner_voter_tree hy hc hes hP hCP haC

end Consensus.Goldilocks.Healing

end
