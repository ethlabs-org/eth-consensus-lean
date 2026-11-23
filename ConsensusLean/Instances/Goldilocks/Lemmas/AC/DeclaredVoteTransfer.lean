module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Views

public section

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {A : SAState sp.n} {Φ : Frm sp.n FGP} {s : Nat}

/-- Each effective previous-slot entry is backed in the reader's actual pool. -/
theorem merged_declared_backing {v : Vote sp.n} (hs : v.slot = s)
    (hv : v ∈ (mergedVoteView sp A Φ (s + 1)).votes) :
    v ∈ A.pool s ∨ v.val ∈ equivocators {w | w ∈ A.pool s} := by
  rcases hv with base | ⟨_, _, _, _, _, backed⟩
  · left
    simpa [SAState.poolAt] using (List.mem_filter.mp base).1
  · simpa [ShouldCountDeclaredVote, SAState.poolAt, hs] using backed

/-- Without fixing the entry slot, the frozen case uses the pool's slot invariant. -/
theorem merged_declared_backing_at_vote_slot {v : Vote sp.n}
    (hpool : ∀ k, ∀ w ∈ A.pool k, w.slot = k) (hv : v ∈ (mergedVoteView sp A Φ s).votes) :
    v ∈ A.pool v.slot ∨ v.val ∈ equivocators {w | w ∈ A.pool v.slot} := by
  rcases hv with base | ⟨_, _, _, _, _, backed⟩
  · left
    have h := (List.mem_filter.mp base).1
    change v ∈ A.poolAt ((s : Int) - 1) at h
    unfold SAState.poolAt at h
    split_ifs at h with neg
    · simp at h
    · simpa only [hpool _ v h] using h
  · simpa [ShouldCountDeclaredVote, SAState.poolAt] using backed

/-- Transfer the two authentic witnesses, not the declared-only head. -/
theorem merged_declared_at_writer {P : Set (Vote sp.n)}
    (relay : ∀ v ∈ A.pool s, v ∈ P ∨ v.val ∈ equivocators P) {v : Vote sp.n}
    (hs : v.slot = s) (hv : v ∈ (mergedVoteView sp A Φ (s + 1)).votes) :
    v ∈ P ∨ v.val ∈ equivocators P := by
  rcases merged_declared_backing hs hv with h | ⟨u, hu, w, hw, ne, eu, ew⟩
  · exact relay v h
  · right
    rcases relay u hu with h | h
    · rcases relay w hw with h' | h'
      · exact ⟨u, h, w, h', ne, eu, ew⟩
      · exact ew ▸ h'
    · exact eu ▸ h

end Consensus.Goldilocks.SA

end
