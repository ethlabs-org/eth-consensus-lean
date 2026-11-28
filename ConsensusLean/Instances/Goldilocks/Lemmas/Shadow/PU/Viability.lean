module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Safety

public section

/-! # Shadow P-U viability: store snapshots and height bridges -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
  {B : NodeBlock P ACP}

/-- In a top frame the lower-height viable arm extends the justified block. -/
theorem isViable_J_of_top (htop : st.hmax = st.hj + 1)
    (hB : (st.σ B.root).h + 1 = st.hmax) (hv : st.IsViable B) : st.Anc st.J B := by
  rcases (st.isViable_iff B).1 hv with hh | ⟨_, hgap | hJ⟩
  · omega
  · omega
  · exact hJ

/-- At the predecessor height, a block comparable with J is viable or strictly below J. -/
theorem isViable_or_lt_J_of_pred_le (hpred : st.hmax - 1 ≤ (st.σ B.root).h)
    (hcomp : Compatible st.tree st.J B) :
    st.IsViable B ∨ (st.Anc B st.J ∧ B ≠ st.J) := by
  by_cases hv : st.IsViable B
  · exact Or.inl hv
  right
  have hn : ¬ st.Anc st.J B := by
    intro hJ
    apply hv
    apply (st.isViable_iff B).2
    by_cases hh : st.hmax ≤ (st.σ B.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inr hJ⟩
  exact ⟨hcomp.resolve_left hn, fun he => hn (he ▸ .refl)⟩

end Consensus.Goldilocks.Store

end
