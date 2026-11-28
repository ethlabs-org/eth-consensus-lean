module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Frame.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame

public section

/-! # Shadow P-U viability: store snapshots and height bridges -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}
  {B : NodeBlock P ACP}

/-- The cache facts used by the snapshot lemmas, independent of the finality handler. -/
structure PUSnapshot (st : Store P ACP) (acp₀ : ACP) : Prop where
  finite : st.tree.Finite
  coherent : Coherent st.tree
  F_mem : st.F ∈ st.tree
  J_mem : st.J ∈ st.tree
  F_J : st.Anc st.F st.J
  hj_lt_hmax : st.hj < st.hmax
  height_bound : ∀ B ∈ st.tree, (st.σ B.root).h ≤ st.hmax
  max_attained : ∃ C ∈ st.tree, (st.σ C.root).h = st.hmax
  height_mono : ∀ {A B}, st.Anc A B → (st.σ A.root).h ≤ (st.σ B.root).h
  entry_at_height : ∀ {C}, C ∈ st.tree → ∀ {h}, 1 ≤ h → h ≤ (st.σ C.root).h →
    ∃ E ∈ st.tree, st.Anc E C ∧ (st.σ E.root).h = h ∧ (st.σ E.root).Th = E.root
  J_height_le : st.hj ≤ (st.σ st.J.root).h
  J_entry : st.J = P.genesisBlock acp₀ ∨
    ((st.σ st.J.root).h = st.hj ∧ (st.σ st.J.root).Th = st.J.root ∧
      ∃ W ∈ st.tree, st.Anc st.J W ∧ st.hj < (st.σ W.root).h)
  genesis_anc : ∀ B ∈ st.tree, st.Anc (P.genesisBlock acp₀) B
  genesis_height : (st.σ (P.genesisBlock acp₀).root).h = 1

/-- A block at the maximum height is viable without a root condition. -/
theorem isViable_of_hmax_le (h : st.hmax ≤ (st.σ B.root).h) : st.IsViable B :=
  (st.isViable_iff B).2 (Or.inl h)

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

/-- Existing viable heads remain viable under the shadow rule. -/
theorem isViable_of_entries_below (hs : PUSnapshot st acp₀) (hB : B ∈ st.tree) {hz : Nat}
    (hBh : hz + 1 ≤ (st.σ B.root).h)
    (hcross : ∀ E ∈ st.tree, ∀ C, (st.σ E.root).Th = E.root →
      hz + 1 ≤ (st.σ E.root).h → st.Anc E C →
      (st.σ E.root).h < (st.σ C.root).h → st.Anc E B) : st.IsViable B := by
  obtain ⟨C, hC, hCh⟩ := hs.max_attained
  have hpred : st.hmax - 1 ≤ (st.σ B.root).h := by
    by_contra hn
    obtain ⟨E, hE, hEC, hEh, hET⟩ := hs.entry_at_height hC
      (h := st.hmax - 1) (by omega) (by omega)
    have := hs.height_mono
      (hcross E hE C hET (by omega) hEC (by omega))
    omega
  by_cases hh : st.hmax ≤ (st.σ B.root).h
  · exact isViable_of_hmax_le hh
  apply (st.isViable_iff B).2
  refine Or.inr ⟨by omega, ?_⟩
  have hjm := hs.hj_lt_hmax
  by_cases hgap : st.hj + 1 < st.hmax
  · exact Or.inl hgap
  right
  rcases hs.J_entry with hg | ⟨hJh, hJT, W, hW, hJW, hWh⟩
  · rw [hg]
    exact hs.genesis_anc B hB
  · exact hcross _ hs.J_mem W hJT (by omega) hJW (by omega)

end Consensus.Goldilocks.Store

end
