module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes

public section

/-! # Goldilocks SA: A1.8 for an ancestor of the result

A1.8 (`result_transfer`) with its hypotheses and conclusion about a block `D ⪯ C` of the result
`C` (T1 §4: a slow lock's block is on its result's path). The counted supporters of `C` support
`D`, and they are a strict majority of the writer's participants. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- **A1.8 for a block `D ⪯ C` of the result `C`.** -/
theorem result_transfer_anc {FGP : Type} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} (hrun : ACRun tr H U) {s : Nat}
    {X y : Fin sp.n} {i₀ i : Nat} {C D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hX : X ∈ H)
    (hres : ResultAt tr X i₀ s C CV) (hDC : Anc U D C) (hy : y ∈ H) (hc : CastAt tr y i ℓ e)
    (hs : e.msg.slot = s + 1) (hcarry : CarryAt tr U y i e s CV)
    (hviab : ViableAtVote ℓ e (s + 1) D)
    (hlocks : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), Compatible U L D)
    (hd : ∀ v ∈ (mergedVoteView sp e.readPoint ℓ.frame (s + 1)).votes, v.slot = s →
      v ∈ (tr.state X i₀).pool s ∨ v.val ∈ equivocators {w | w ∈ (tr.state X i₀).pool s}) :
    VoteExtends U e.msg D := by
  obtain ⟨-, -, -, hhead⟩ := castAt_spec hrun.localRun hy hc
  have hU := hrun.localRun.coherent
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hrun.localRun.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;>
      exact h.1
  have hσ : ((s + 1 : Nat) : Int) - 1 = (s : Int) := by push_cast; ring
  rw [hs, hσ] at hhead
  have hdomA := voterBlockTree_anc hrun.localRun hy hc
  rw [hs] at hdomA
  have hDt : D ∈ ℓ.frame.tree := by
    rcases hviab with h | h
    · exact h.1.1
    · exact mem_of_anc h hΦ.fcRoot_mem
  have hmaj := result_majority hres
  obtain ⟨ℓX, hupd, -, rfl⟩ := hres
  have hsupp := counted_supporters hrun hX hy hupd.1 hc hs hDC hcarry hviab hd
  have hcore := anc_getHead hU hΦ hΦU e.readPoint (tr.time i)
    (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int) (fun B hB => hB.1) hdomA hviab
    (fun L hL => hlocks L hL) fun X' Cx hCx hp hCxD =>
      isBest_of_majority hΦ (merged_support_subset hrun.localRun hy hc (s + 1))
        (fun B hB => hB.1.1) hsupp (merged_voters_subset hrun.localRun hy hc hd) hmaj hCx hp hCxD
  refine ⟨_, hΦU ?_, hhead.symm, Anc.mono hΦU hcore⟩
  by_cases he : D = getHead sp e.readPoint ℓ.frame (tr.time i)
      (ℓ.frame.viableTree (voterBlockTree sp e.readPoint ℓ.frame (s + 1)))
      (mergedVoteView sp e.readPoint ℓ.frame (s + 1)) (s : Int)
  · exact he ▸ hDt
  · exact (Anc.mem hcore he).2

end Consensus.Goldilocks.SA

end
