module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Emission
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Honest
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: an honest vote extends a lock it reads

consensus-lean#135 (WI-15/16), r14 s1 L1.2 (the intra-node part). The head walk starts at the
anchor, the deepest of the live lock blocks and `fc_root`. When a block `C` of that set is
compatible with every live lock block, the anchor extends `C` (it is at least as deep), so the
walk extends every ancestor of `C` (`anc_getHead_of_compat`). Unlike
`anc_getHead_of_liveLockBlock`, the live lock blocks need not lie on one chain. At an honest vote
the walk reads the emission's read point (`castAt_head_anc`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- **The walk extends a compatible anchor candidate.** If `C` is a live lock block or `fc_root`
and every live lock block is compatible with `C`, every head extends every ancestor of `C`. -/
theorem anc_getHead_of_compat {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {A : SAState sp.n}
    {t : Time} {C : Blk sp.n FGP} (hC : C ∈ liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot})
    (hcomp : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Compatible Φ.tree L C)
    {tree : Set (Blk sp.n FGP)} (htree : tree ⊆ Φ.tree) (V : View sp.n) (s : Int)
    {B : Blk sp.n FGP} (hBC : Φ.Anc B C) :
    Φ.Anc B (getHead sp A Φ t tree V s) := by
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.1 hX) ▸ hΦ.fcRoot_mem
  have hCt := hS hC
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨C, hC⟩
  have hA : getAnchor sp A Φ t = D := by unfold getAnchor; rw [hD]; rfl
  obtain ⟨hDS, hmax⟩ := deepest_mem hD
  have hDC : Compatible Φ.tree D C := by
    rcases hDS with hDl | hDf
    · exact hcomp D hDl
    · rw [Set.mem_singleton_iff.1 hDf]
      rcases hC with hCl | hCf
      · exact (liveLockBlock_candidate hΦ hCl).elim (fun h => Or.inl h.2.1) Or.inr
      · rw [Set.mem_singleton_iff.1 hCf]
        exact Or.inl Relation.ReflTransGen.refl
  have hCD : Φ.Anc C D := by
    refine hDC.elim (fun hDC' => ?_) id
    by_cases hne : D = C
    · exact hne ▸ Relation.ReflTransGen.refl
    · rcases hmax C hC (Ne.symm hne) with h | ⟨h, -⟩ <;>
        have := depth_lt_of_anc hΦ hDC' hne hCt <;> omega
  unfold getHead
  rw [hA]
  exact (hBC.trans hCD).trans (anc_ghost htree _ (hS hDS))

/-- **An honest vote extends a lock it reads.** At an honest vote, if `C` is a live lock block
of the read point or `fc_root`, compatible with every live lock block of the read point, the
vote's head is a block of the frame that extends every ancestor `B` of `C`. -/
theorem castAt_head_anc (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) {C : Blk sp.n FGP}
    (hC : C ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i) ∪ {ℓ.frame.fcRoot})
    (hcomp : ∀ L ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i),
      Compatible ℓ.frame.tree L C)
    {B : Blk sp.n FGP} (hBC : ℓ.frame.Anc B C) :
    ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc B Hd := by
  have hΦ : FrameOK ℓ.frame := by
    rcases hr.frameLaw y hy i ℓ hc.1 with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1.1
  have hT : ℓ.frame.viableTree (voteDomain sp e.readPoint ℓ.frame e.msg.slot) ⊆
      ℓ.frame.tree := fun X hX => voteDomain_subset_tree hX.1
  exact ⟨_, getHead_mem hΦ hT _ _ _ _, (castAt_spec hr hy hc).2.2.2.symm,
    anc_getHead_of_compat hΦ hC hcomp hT _ _ hBC⟩

end Consensus.Goldilocks.SA

end
