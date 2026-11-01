module
public import AvailableChainFGSA.Model.Objects

public section

namespace AvailableChain.FGSA

variable {n : Nat}

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Erasure keeps the stored root. -/
@[simp] theorem named_erase_root (N : NamedProposal n) : N.erase.root = N.root := by
  cases N <;> rfl

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Erasure keeps the slot. -/
@[simp] theorem named_erase_slot (N : NamedProposal n) : N.erase.slot = N.slot := by
  cases N <;> rfl

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Erasure keeps the parent geometry. -/
@[simp] theorem named_erase_parent (N : NamedProposal n) : N.erase.parent = N.parent.erase := by
  cases N <;> rfl

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Only named genesis erases to genesis. -/
@[simp] theorem named_erase_eq_genesis (N : NamedProposal n) :
    N.erase = .genesis ↔ N = .genesis := by
  cases N <;> simp [NamedProposal.erase]

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.preceq] Reflexive full named ancestry. -/
theorem named_preceq_refl (N : NamedProposal n) : NamedProposal.Preceq N N := by
  cases N <;> simp [NamedProposal.Preceq, NamedProposal.preceq]

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.preceq] Named ancestry composes. -/
theorem named_preceq_trans {A B C : NamedProposal n}
    (hAB : NamedProposal.Preceq A B) (hBC : NamedProposal.Preceq B C) :
    NamedProposal.Preceq A C := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [NamedProposal.Preceq, NamedProposal.preceq] using hBC
      simpa [h] using hAB
  | node P s r x raw sup rows ih =>
      simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC ⊢
      rcases hBC with rfl | h
      · simpa only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
          decide_eq_true_eq] using hAB
      · exact Or.inr (ih h)

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Named ancestry preserves geometry. -/
theorem named_preceq_erase {A B : NamedProposal n} (h : NamedProposal.Preceq A B) :
    Block.Preceq A.erase B.erase := by
  induction B with
  | genesis =>
      have he : A = .genesis := by simpa [NamedProposal.Preceq, NamedProposal.preceq] using h
      subst A
      rfl
  | node P s r x raw sup rows ih =>
      simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      simp only [NamedProposal.erase, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq]
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (ih h)

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks.erase] Lift an erased ancestor without injectivity. -/
theorem named_erase_ancestor {N : NamedProposal n} {b : Block}
    (h : Block.Preceq b N.erase) :
    ∃ A, NamedProposal.Preceq A N ∧ A.erase = b := by
  induction N with
  | genesis =>
      have he : b = .genesis := by simpa [NamedProposal.erase, Block.Preceq, Block.preceq] using h
      exact ⟨.genesis, named_preceq_refl _, he.symm⟩
  | node P s r x raw sup rows ih =>
      simp only [NamedProposal.erase, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with he | h
      · exact ⟨.node P s r x raw sup rows, named_preceq_refl _, he.symm⟩
      · obtain ⟨A, hA, he⟩ := ih h
        refine ⟨A, ?_, he⟩
        simp only [NamedProposal.Preceq, NamedProposal.preceq, Bool.or_eq_true,
          decide_eq_true_eq]
        exact Or.inr hA

/-- [ROOT-DIGEST-2 W1; DC NamedBlocks] Named construction retains the geometric constructor. -/
theorem namedProposal_erase (p : Params) (P : NamedProposal p.n) (s : Slot) (app : Nat)
    (raw support : List (HeadWire p.n)) (rows : List (RowWire p.n)) :
    (namedProposal p P s app raw support rows).erase =
      proposalBlock p P.erase s app raw support rows := by
  simp [namedProposal, proposalBlock, NamedProposal.erase]

end AvailableChain.FGSA
end
