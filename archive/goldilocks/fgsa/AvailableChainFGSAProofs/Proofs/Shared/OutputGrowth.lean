module
public import AvailableChainGeneric.Proofs.Pure.BlockOrder
public import AvailableChainModel.Objects.Time

public section

namespace AvailableChain.FGSA.Run

/-- Plan A4/C1; DC Generic/Lemmas.lean:60 liveFrom_of_includedFrom:
one selected proposal serves both getters. A common deadline output orders the trigger output and B;
the no-future pair excludes the reverse order and equality. -/
theorem jointGrowthAt_of_inclusion {Getter Reader : Type}
    (O : Getter → Reader → Time → Block) (selected : Getter → Prop)
    (honest : Reader → Prop) (proposalTime : Slot → Time)
    (actualProposal : Slot → Block → Prop) (s : Slot) (B : Block) (t D : Time)
    (hfuture : t < proposalTime s) (hprop : actualProposal s B)
    (hmono : ∀ g x, selected g → honest x → Block.Preceq (O g x t) (O g x D))
    (hincl : ∀ g x, selected g → honest x → Block.Preceq B (O g x D))
    (hnoFuture : ∀ g x, selected g → honest x → ¬ Block.Preceq B (O g x t)) :
    t < proposalTime s ∧ actualProposal s B ∧
      ∀ g, selected g →
        (∀ x, honest x → Block.Prec (O g x t) B) ∧
        (∀ x, honest x → Block.Preceq B (O g x D)) := by
  refine ⟨hfuture, hprop, ?_⟩
  intro g hg
  refine ⟨?_, fun x hx => hincl g x hg hx⟩
  intro x hx
  have hn := hnoFuture g x hg hx
  have hle : Block.Preceq (O g x t) B := by
    rcases Gen.Pure.block_preceq_total_of_common (hmono g x hg hx) (hincl g x hg hx)
      with h | h
    · exact h
    · exact (hn h).elim
  have hne : O g x t ≠ B := by
    intro he
    apply hn
    rw [he]
    exact Gen.Pure.block_preceq_refl B
  change (!decide (O g x t = B) && Block.preceq (O g x t) B) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hne, hle⟩

end AvailableChain.FGSA.Run
end
