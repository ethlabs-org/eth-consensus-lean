module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks SA: a lock below a viable head keeps its block

The AC part of the benign-contest lemma (workbench `fg-liveness/r14-end-to-end`,
`s4b-contest-benign.md`, Lemma B, step 4): a block of a well-formed frame that extends
`fc_root` and is an ancestor of a viable head is in the viable tree, so it is its own viable
ancestor, and `live_locks` keeps a lock on it in place. -/

namespace Consensus.Goldilocks.SA

variable {n : Nat} {FGP : Type}

/-- A block above `fc_root` that is an ancestor of a viable head is in the viable tree. -/
theorem mem_viableTree_of_anc_viableHead {Φ : Frm n FGP} {B W : Blk n FGP} (hB : B ∈ Φ.tree)
    (hfc : Φ.Anc Φ.fcRoot B) (hW : W ∈ Φ.tree) (hWv : W ∈ Φ.viableHeads) (hBW : Φ.Anc B W) :
    B ∈ Φ.viableTree Φ.tree :=
  ⟨hB, hfc, W, hW, hWv, hBW⟩

/-- **A lock below a viable head stays (r14 s4b, Lemma B).** In a well-formed frame, a block
above `fc_root` that is an ancestor of a viable head is its own viable ancestor. -/
theorem viableAncestor_of_anc_viableHead {Φ : Frm n FGP} (hΦ : FrameOK Φ) {B W : Blk n FGP}
    (hB : B ∈ Φ.tree) (hfc : Φ.Anc Φ.fcRoot B) (hW : W ∈ Φ.tree) (hWv : W ∈ Φ.viableHeads)
    (hBW : Φ.Anc B W) : Φ.viableAncestor B = B :=
  viableAncestor_self hΦ hB (Or.inl (mem_viableTree_of_anc_viableHead hB hfc hW hWv hBW))

end Consensus.Goldilocks.SA

end
