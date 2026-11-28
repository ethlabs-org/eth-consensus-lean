module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Viability
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Shadow P-U frame snapshots -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- Membership in the shadow viable tree is ancestor closure above F. -/
theorem mem_viableTree_iff {X : NodeBlock P ACP} :
    X ∈ st.toFrame.viableTree st.toFrame.tree ↔
      X ∈ st.tree ∧ st.Anc st.F X ∧
        ∃ W ∈ st.tree, st.Anc st.F W ∧ st.IsViable W ∧ st.Anc X W := by
  simp only [Frame.viableTree, Frame.Anc, Set.mem_ofPred_eq, toFrame_tree,
    toFrame_viableHeads, toFrame_fcRoot]
  constructor
  · rintro ⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hv⟩, hXW⟩
    exact ⟨hX, hFX, W, hW, hFW, hv, hXW.mono fun _ h => h.1⟩
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    exact ⟨⟨hX, hFX⟩, Anc.restrict .refl hFX, W, ⟨hW, hFW⟩,
      ⟨hW, hFW, hv⟩, Anc.restrict hFX hXW⟩

end Consensus.Goldilocks.Store

end
