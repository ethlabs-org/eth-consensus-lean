module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.SlowCounted
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Opponents

public section

/-! # Result transfer to an ancestor at independently honest cuts -/

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {proposer : Nat → Fin sp.n}

/-- Counted supporters of a result also support its ancestor, even after the writer is lost. -/
theorem result_transfer_anc (hrun : ACRun proposer tr H U)
    {s : Nat} {X y : Fin sp.n} {i₀ i : Nat} {C D : Blk sp.n FGP}
    {CV : Set (Vote sp.n)} {ell : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hX : X ∈ H (tr.time i₀)) (hres : ResultAt tr X i₀ s C CV)
    (hDC : Anc U D C) (hy : y ∈ H (tr.time i)) (hc : CastAt tr y i ell e)
    (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV)
    (hviab : ViableAtVote ell e (s + 1) D)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ell.frame (tr.time i), Compatible U L D)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ell.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg D := by
  have hr := (hrun.upTo (hrun.localRun.time_nonneg i)).localRun
  have hc' := upTo_castAt.mpr ⟨le_rfl, hc⟩
  obtain ⟨_, _, _, hhead⟩ := castAt_spec hr hy hc'
  have hU := hrun.localRun.coherent
  obtain ⟨hPhi, hPhiU⟩ := frameIn_of_call hr hy hc'.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voteDomain_anc hr hy hc'
  rw [hs] at hdomA
  have hDt : D ∈ ell.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hPhi.fcRoot_mem
  have hcore := anc_getHead hU hPhi hPhiU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ell.frame (s + 1)) (s : Int)
    (fun B hB => voteDomain_subset_tree hB) hdomA hviab.voteDomain
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxD =>
      isBest_of_majority hPhi (merged_support_subset hr hy hc' (s + 1))
        (fun B hB => voteDomain_subset_tree hB.1)
        (by
          obtain ⟨ellX, hupd, _, rfl⟩ := hres
          exact counted_ancestor_supporters hrun hX hy hupd.1 hc hs hDC hcarry hviab hd)
        (merged_voters_subset hr hy hc' hd) (result_majority hres) hCx hp hCxD
  refine ⟨_, hPhiU ?_, hhead.symm, Anc.mono hPhiU hcore⟩
  by_cases he : D = getHead sp e.readPoint ell.frame (tr.time i)
      (ell.frame.viableTree (voteDomain sp e.readPoint ell.frame (s + 1)))
      (mergedVoteView sp e.readPoint ell.frame (s + 1)) (s : Int)
  · exact he ▸ hDt
  · exact (Anc.mem hcore he).2

end Consensus.Goldilocks.SA.Growing

end
