module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Viability
import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Shadow P-U frame snapshots -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type} {acp₀ : ACP} {st : Store P ACP}

/-- The shadow frame keeps the same rooted tree and roots fork choice at F. -/
theorem frameOK_toFrame' (hs : PUSnapshot st acp₀) : FrameOK st.toFrame' := by
  constructor
  all_goals simp only [Frame.Rooted, Frame.Anc, toFrame'_tree, toFrame'_F,
    toFrame'_fcRoot, toFrame'_viableHeads]
  · exact hs.finite.subset fun _ h => h.1
  · exact hs.coherent.mono fun _ h => h.1
  · exact ⟨⟨hs.F_mem, .refl⟩, fun _ h => Anc.restrict .refl h.2⟩
  · exact ⟨hs.F_mem, .refl⟩
  · exact .refl
  · exact fun _ h => ⟨h.1, h.2.1⟩
  · exact fun _ h => Anc.restrict .refl h.2.1

/-- Top frames contain J as a viable head, including the genesis justification. -/
theorem J_mem_viableHeads' (hs : PUSnapshot st acp₀) (htop : st.hmax = st.hj + 1) :
    st.J ∈ st.toFrame'.viableHeads := by
  rw [toFrame'_viableHeads]
  refine ⟨hs.J_mem, hs.F_J, ?_⟩
  rcases hs.J_entry with hg | ⟨hJh, _, _⟩
  · have hheight : (st.σ st.J.root).h = 1 := by rw [hg]; exact hs.genesis_height
    have hj := hs.J_height_le
    apply (st.isViable'_iff _).2
    by_cases hh : st.hmax ≤ (st.σ st.J.root).h
    · exact Or.inl hh
    · exact Or.inr ⟨by omega, Or.inr .refl⟩
  · exact (st.isViable'_iff _).2 (Or.inr ⟨by omega, Or.inr .refl⟩)

/-- Membership in the shadow viable tree is ancestor closure above F. -/
theorem mem_viableTree'_iff {X : NodeBlock P ACP} :
    X ∈ st.toFrame'.viableTree st.toFrame'.tree ↔
      X ∈ st.tree ∧ st.Anc st.F X ∧
        ∃ W ∈ st.tree, st.Anc st.F W ∧ st.IsViable' W ∧ st.Anc X W := by
  simp only [Frame.viableTree, Frame.Anc, Set.mem_ofPred_eq, toFrame'_tree,
    toFrame'_viableHeads, toFrame'_fcRoot]
  constructor
  · rintro ⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hv⟩, hXW⟩
    exact ⟨hX, hFX, W, hW, hFW, hv, hXW.mono fun _ h => h.1⟩
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    exact ⟨⟨hX, hFX⟩, Anc.restrict .refl hFX, W, ⟨hW, hFW⟩,
      ⟨hW, hFW, hv⟩, Anc.restrict hFX hXW⟩

/-- Gap frames have exactly the stock viable tree. -/
theorem viableTree'_eq_of_gap (hs : PUSnapshot st acp₀)
    (hgap : st.hj + 1 < st.hmax) :
    st.toFrame'.viableTree st.toFrame'.tree = st.toFrame.viableTree st.toFrame.tree := by
  have htop : ¬ st.hmax = st.hj + 1 := by omega
  have hnc : ¬ st.Contest := fun h => htop h.1
  have hroot : st.fcRoot = st.F := by simp [fcRoot, htop]
  ext X
  rw [mem_viableTree'_iff]
  constructor
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    have hV := (isViable'_iff_of_not_contest hs hW hFW hnc).1 hv
    refine ⟨⟨hX, hFX⟩, ?_, W, ⟨hW, hFW⟩, ⟨hW, hFW, hV⟩,
      Anc.restrict hFX hXW⟩
    rw [show st.toFrame.fcRoot = st.F from hroot]
    exact Anc.restrict .refl hFX
  · rintro ⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hrW, hv⟩, hXW⟩
    exact ⟨hX, hFX, W, hW, hFW, isViable_imp_isViable' hs hW hFW hrW hv,
      hXW.mono fun _ h => h.1⟩

/-- In a clean top frame only the F-to-J path is added to the viable tree. -/
theorem viableTree'_eq_union_of_top_clean (hs : PUSnapshot st acp₀)
    (htop : st.hmax = st.hj + 1) (hnc : ¬ st.Contest) :
    st.toFrame'.viableTree st.toFrame'.tree =
      st.toFrame.viableTree st.toFrame.tree ∪ {X | st.Anc st.F X ∧ st.Anc X st.J} := by
  have hroot : st.fcRoot = st.J := by simp [fcRoot, htop, hnc]
  ext X
  rw [mem_viableTree'_iff]
  constructor
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    obtain ⟨hJW, hv⟩ := (isViable'_iff_of_not_contest hs hW hFW hnc).1 hv
    rw [hroot] at hJW
    rcases Anc.total hs.coherent hXW hJW with hXJ | hJX
    · exact Or.inr ⟨hFX, hXJ⟩
    · left
      refine ⟨⟨hX, hFX⟩, ?_, W, ⟨hW, hFW⟩, ⟨hW, hFW, ?_, hv⟩,
        Anc.restrict hFX hXW⟩
      · rw [show st.toFrame.fcRoot = st.J from hroot]
        exact Anc.restrict hs.F_J hJX
      · rwa [hroot]
  · rintro (⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hJW, hv⟩, hXW⟩ | ⟨hFX, hXJ⟩)
    · exact ⟨hX, hFX, W, hW, hFW, isViable_imp_isViable' hs hW hFW hJW hv,
        hXW.mono fun _ h => h.1⟩
    · have hX : X ∈ st.tree := by
        by_cases he : X = st.J
        · exact he ▸ hs.J_mem
        · exact (Anc.mem hXJ he).1
      have hJ := J_mem_viableHeads' hs htop
      rw [toFrame'_viableHeads] at hJ
      exact ⟨hX, hFX, st.J, hs.J_mem, hs.F_J, hJ.2.2, hXJ⟩

/-- In contests the new part is precisely the ancestor closure of the added J-side heads
outside the stock viable tree. -/
theorem viableTree'_eq_union_of_contest (hs : PUSnapshot st acp₀) (hc : st.Contest) :
    st.toFrame'.viableTree st.toFrame'.tree = st.toFrame.viableTree st.toFrame.tree ∪
      ({X | X ∈ st.tree ∧ st.Anc st.F X ∧ ∃ W ∈ st.tree,
        st.Anc st.F W ∧ st.Anc st.J W ∧ (st.σ W.root).h + 1 = st.hmax ∧ st.Anc X W} \
        st.toFrame.viableTree st.toFrame.tree) := by
  have hroot : st.fcRoot = st.F := by simp [fcRoot, hc]
  ext X
  rw [mem_viableTree'_iff]
  constructor
  · rintro ⟨hX, hFX, W, hW, hFW, hv, hXW⟩
    by_cases hold : X ∈ st.toFrame.viableTree st.toFrame.tree
    · exact Or.inl hold
    right
    refine ⟨?_, hold⟩
    rcases (st.isViable'_iff W).1 hv with hh | ⟨hh, hgap | hJW⟩
    · apply False.elim
      apply hold
      refine ⟨⟨hX, hFX⟩, ?_, W, ⟨hW, hFW⟩, ⟨hW, hFW, ?_, ?_⟩,
        Anc.restrict hFX hXW⟩
      · rw [show st.toFrame.fcRoot = st.F from hroot]
        exact Anc.restrict .refl hFX
      · rw [hroot]; exact hFW
      · simpa [IsViable, headHeightFloor, hc] using hh
    · have := hc.1
      omega
    · exact ⟨hX, hFX, W, hW, hFW, hJW, hh, hXW⟩
  · rintro (⟨⟨hX, hFX⟩, _, W, _, ⟨hW, hFW, hRW, hv⟩, hXW⟩ |
      ⟨⟨hX, hFX, W, hW, hFW, hJW, hh, hXW⟩, _⟩)
    · exact ⟨hX, hFX, W, hW, hFW, isViable_imp_isViable' hs hW hFW hRW hv,
        hXW.mono fun _ h => h.1⟩
    · exact ⟨hX, hFX, W, hW, hFW,
        (st.isViable'_iff W).2 (Or.inr ⟨hh, Or.inr hJW⟩), hXW⟩

end Consensus.Goldilocks.Store

end
