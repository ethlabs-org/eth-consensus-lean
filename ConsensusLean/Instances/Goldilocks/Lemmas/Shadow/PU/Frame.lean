module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.CoreStock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Viability
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Cache
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Shadow P-U frame snapshots -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- The shadow frame keeps the same rooted tree and roots fork choice at F. -/
theorem frameOK_toFrame (hs : PUSnapshot st acp₀) : FrameOK st.toFrame := by
  constructor
  all_goals simp only [Frame.Rooted, Frame.Anc, toFrame_tree, toFrame_F,
    toFrame_fcRoot, toFrame_viableHeads]
  · exact hs.finite.subset fun _ h => h.1
  · exact hs.coherent.mono fun _ h => h.1
  · exact ⟨⟨hs.F_mem, .refl⟩, fun _ h => Anc.restrict .refl h.2⟩
  · exact ⟨hs.F_mem, .refl⟩
  · exact .refl
  · exact fun _ h => ⟨h.1, h.2.1⟩
  · exact fun _ h => Anc.restrict .refl h.2.1

/-- Top frames contain J as a viable head, including the genesis justification. -/
theorem J_mem_viableHeads (hs : PUSnapshot st acp₀) (htop : st.hmax = st.hj + 1) :
    st.J ∈ st.toFrame.viableHeads := by
  rw [toFrame_viableHeads]
  refine ⟨hs.J_mem, hs.F_J, ?_⟩
  rcases hs.J_entry with hg | ⟨hJh, _, _⟩
  · have hheight : (st.σ st.J.root).h = 1 := by rw [hg]; exact hs.genesis_height
    have hj := hs.J_height_le
    apply (st.isViable_iff _).2
    by_cases hh : st.hmax ≤ (st.σ st.J.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inr .refl⟩
  · exact (st.isViable_iff _).2 (Or.inr ⟨by omega, Or.inr .refl⟩)

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
