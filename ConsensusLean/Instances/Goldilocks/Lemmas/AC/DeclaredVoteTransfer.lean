module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Views
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.DeclaredVotes

public section

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type} {A : ACState sp.n} {Φ : Frm sp.n FGP} {s : Nat}

/-- A merged entry is a held previous-slot vote or backed in the pool of its own slot. -/
private theorem merged_declared_cases {v : Vote sp.n} (hv : v ∈ (mergedVoteView sp A Φ s).votes) :
    v ∈ A.poolAt ((s : Int) - 1) ∨ v ∈ A.pool v.slot ∨
      v.val ∈ equivocators {w | w ∈ A.pool v.slot} := by
  rcases hv with base | ⟨_, _, _, _, backed⟩
  · exact .inl (List.mem_filter.mp base).1
  · simpa [ShouldCountDeclaredVote, ACState.poolAt] using Or.inr backed

/-- Each effective previous-slot entry is backed in the reader's actual pool. -/
theorem merged_declared_backing {v : Vote sp.n} (hs : v.slot = s)
    (hv : v ∈ (mergedVoteView sp A Φ (s + 1)).votes) :
    v ∈ A.pool s ∨ v.val ∈ equivocators {w | w ∈ A.pool s} := by
  subst hs
  simpa [ACState.poolAt] using merged_declared_cases hv

/-- Without fixing the entry slot, the frozen case uses the pool's slot invariant. -/
theorem merged_declared_backing_at_vote_slot {v : Vote sp.n}
    (hpool : ∀ k, ∀ w ∈ A.pool k, w.slot = k) (hv : v ∈ (mergedVoteView sp A Φ s).votes) :
    v ∈ A.pool v.slot ∨ v.val ∈ equivocators {w | w ∈ A.pool v.slot} := by
  rcases merged_declared_cases hv with h | h
  · unfold ACState.poolAt at h
    split_ifs at h
    · simp at h
    · simpa only [hpool _ v h] using Or.inl h
  · exact h

/-- Transfer the two authentic witnesses, not the declared-only head. -/
theorem merged_declared_at_writer {P : Set (Vote sp.n)}
    (relay : ∀ v ∈ A.pool s, v ∈ P ∨ v.val ∈ equivocators P) {v : Vote sp.n}
    (hs : v.slot = s) (hv : v ∈ (mergedVoteView sp A Φ (s + 1)).votes) :
    v ∈ P ∨ v.val ∈ equivocators P :=
  backed_trans (P := {w | w ∈ A.pool s}) relay (merged_declared_backing hs hv)

end Consensus.Goldilocks.AC

end
