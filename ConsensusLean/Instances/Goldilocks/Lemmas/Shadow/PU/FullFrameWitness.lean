module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Safety
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ACProjection

public section

/-! # The full P-U frame has a viable witness

Moved from `Leaves` so that suppliers upstream of `ReportFollow` (`FollowWrite`) can read it. -/

namespace Consensus.Goldilocks.Healing

variable {P : Params} {ACP : Type} {st : Store P ACP}

private theorem full_frame_viable_witness_of_max {acp₀ : ACP}
    (hr : st.Reachable acp₀)
    (hF : ∀ Q ∈ st.tree, (st.σ Q.root).h = st.hmax → st.Anc st.F Q) :
    ∃ Q ∈ st.toFrame.tree, Q ∈ st.toFrame.viableHeads ∧
      st.toFrame.Anc st.toFrame.fcRoot Q := by
  obtain ⟨_, _, _, _, _, ⟨Q, hQ, hheight⟩, _⟩ := Store.cache_invariants' hr
  have hFQ := hF Q hQ hheight
  refine ⟨Q, ?_, ?_, ?_⟩
  · rw [Store.toFrame_tree]
    exact ⟨hQ, hFQ⟩
  · rw [Store.toFrame_viableHeads]
    exact ⟨hQ, hFQ, (Store.isViable_iff _ _).2 (Or.inl hheight.ge)⟩
  · change Anc st.toFrame.tree st.toFrame.fcRoot Q
    rw [Store.toFrame_tree, Store.toFrame_fcRoot]
    exact Anc.restrict .refl hFQ

end Consensus.Goldilocks.Healing

namespace Consensus.Goldilocks.Healing.Growing.Shadow

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The full P-U frame has a viable maximum-height witness above its finalized root. -/
theorem full_frame_viable_witness_at {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {ini}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {i : Nat}
    (hy : y ∈ H (tr.time i))
    (hf : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    ∃ Q ∈ (Node.frame (tr.state y i)).tree,
      Q ∈ (Node.frame (tr.state y i)).viableHeads ∧
      (Node.frame (tr.state y i)).Anc (Node.frame (tr.state y i)).fcRoot Q := by
  have ht := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := Compose.Growing.reachable_at' hrun ht hy hle
  have hu := Store.finalitySpec_updateFinality (P := sp.toParams)
    (ACP := Payload sp.n)
  simp only [Node.frame_eq]
  apply full_frame_viable_witness_of_max hr
  intro Q hQ hheight
  exact Store.F_anc_of_hmax_le_of_safe_with hu hr.reachableWith hr.reachableWith
    (Store.accepted_tree_with hu hr.reachableWith).2.1 subset_rfl subset_rfl hf
    (held_atts_safe_at hrun hnc ht hle hy ht hle hy le_rfl le_rfl) hQ hheight.ge

end Consensus.Goldilocks.Healing.Growing.Shadow

end
