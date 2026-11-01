module
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks

public section

/-! C6 LockRetention: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def LockOrConflict (row : Block × Nat × Time) (st : State n) : Prop :=
  row ∈ st.base.obligations ∨ ∃ C ∈ st.pcs, Block.compatible C.target row.1 = false
private theorem install_lock_or_conflict (st : State n) (row : Block × Nat × Time)
    (C : PC n) (h : LockOrConflict row st) : LockOrConflict row (installPC st C) := by
  rcases h with hrow | ⟨D, hD, hconf⟩
  · rw [installPC_def]
    split
    · exact Or.inl hrow
    · by_cases hc : Block.compatible C.target row.1 = true
      · exact Or.inl (deleteConflictingLeases_keep _ C row hrow hc)
      · exact Or.inr ⟨C, List.mem_append_right _ (List.mem_singleton_self _),
          Bool.eq_false_iff.mpr hc⟩
  · exact Or.inr ⟨D, installPC_pcs_mono st C hD, hconf⟩
/-- Collection keeps a lock when no resulting PC conflicts with its target. -/
theorem pcsa_collect_keep_lock (st : State n) (row : Block × Nat × Time)
    (hr : row ∈ st.base.obligations)
    (hcompat : ∀ C ∈ (collectPCs st).pcs, Block.Compatible C.target row.1) :
    row ∈ (collectPCs st).base.obligations := by
  have hinv : LockOrConflict row (collectPCs st) := by
    apply collectPCs_invariant (LockOrConflict row)
    · intro acc C ha _
      exact install_lock_or_conflict acc row C ha
    · exact Or.inl hr
  rcases hinv with hrow | ⟨C, hC, hc⟩
  · exact hrow
  · have ht := hcompat C hC
    rw [ht] at hc
    cases hc
/-- A lock write retains the target of every existing row. -/
theorem pcsa_write_lock_keep_target (st : State n) (b : Block) (g : Nat)
    (deadline : Time) (rank : Option PCRank) (row : Block × Nat × Time)
    (hr : row ∈ st.base.obligations) :
    ∃ row' ∈ (writeLease st b g deadline rank).base.obligations, row'.1 = row.1 := by
  change ∃ row' ∈ st.base.obligations.filter _ ++ [_], row'.1 = row.1
  by_cases he : row.1 = b ∧ row.2.1 = g
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), he.1.symm⟩
  · refine ⟨row, List.mem_append_left _ (List.mem_filter.mpr ⟨hr, ?_⟩), rfl⟩
    have hn : (row.1 == b && row.2.1 == g) = false :=
      Bool.eq_false_iff.mpr (fun hh => he
        ⟨beq_iff_eq.mp (Bool.and_eq_true_iff.mp hh).1,
          beq_iff_eq.mp (Bool.and_eq_true_iff.mp hh).2⟩)
    change (!(row.1 == b && row.2.1 == g)) = true
    rw [hn]
    rfl
end AvailableChain.PCSA

end
