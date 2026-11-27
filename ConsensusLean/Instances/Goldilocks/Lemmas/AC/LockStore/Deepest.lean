module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Existence of a deepest block in a finite frame -/

namespace Consensus.Goldilocks.AC

variable {sp : ACParams} {FGP : Type}

/-- A nonempty set of blocks of a well-formed frame's tree has a deepest block. -/
theorem exists_deepest {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    (hS : S ⊆ Φ.tree) (hne : S.Nonempty) : ∃ D, deepest Φ S = some D := by
  have hfin : S.Finite := hΦ.finite.subset hS
  obtain ⟨D, hD, hmax⟩ := hfin.exists_maximalFor (depth Φ) S hne
  obtain ⟨D', ⟨hD'S, hD'd⟩, hmin⟩ :=
    (hfin.subset (Set.sep_subset S fun C => depth Φ C = depth Φ D)).exists_minimalFor
      Block.root _ ⟨D, hD, rfl⟩
  have h : ∃ D, IsDeepest Φ S D := by
    refine ⟨D', hD'S, fun C hC hne => ?_⟩
    rcases lt_or_ge (depth Φ C) (depth Φ D') with h | h
    · exact Or.inl h
    have hCd : depth Φ C = depth Φ D' := le_antisymm (hD'd ▸ hmax hC (hD'd ▸ h)) h
    refine Or.inr ⟨hCd, lt_of_le_of_ne ?_ fun hr => hne (hΦ.coherent.1 (hS hC) (hS hD'S) hr.symm)⟩
    exact le_of_not_gt fun hlt => (hmin ⟨hC, hCd.trans hD'd⟩ hlt.le).not_gt hlt
  unfold deepest
  split_ifs
  exact ⟨_, rfl⟩

end Consensus.Goldilocks.AC

end
