module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks SA: the vote-transfer core

The head walk of a vote (or a proposal) from the anchor `get_anchor` over the viable tree of a
domain extends a block `C` when `C` is in that viable tree or at or below `fc_root`, every live
lock block is compatible with `C`, and at every block on the way the child towards `C` is the
best eligible child (lock compatibility is read inside a coherent `U ⊇ Φ.tree`: the
`U`-ancestry between two blocks of a well-formed frame's tree is the tree's). The anchor (the
deepest of the live lock blocks and `fc_root`) is then compatible with `C`: if it extends `C`
the walk, which only descends, does too; otherwise the walk passes `C` (`anc_ghost_of_best`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- **The vote-transfer core.** -/
theorem anc_getHead {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time)
    (V : View sp.n) (σ : Int) {dom : Set (Blk sp.n FGP)} (hdom : dom ⊆ Φ.tree)
    (hdomA : ∀ B ∈ dom, ∀ X, Φ.Anc X B → X ∈ dom) {C : Blk sp.n FGP}
    (hviab : C ∈ Φ.viableTree dom ∨ Φ.Anc C Φ.fcRoot)
    (hlocks : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Compatible U L C)
    (hbest : ∀ X Cx : Blk sp.n FGP, Cx ∈ Φ.viableTree dom → Cx.parent = some X.root →
      Φ.Anc Cx C →
      IsBest sp (goldfishScore sp Φ V σ)
        {B | B ∈ Φ.viableTree dom ∧ B.parent = some X.root ∧ goldfishEligible sp Φ t V σ B}
        Cx) :
    Φ.Anc C (getHead sp A Φ t (Φ.viableTree dom) V σ) := by
  sorry

end Consensus.Goldilocks.SA

end
