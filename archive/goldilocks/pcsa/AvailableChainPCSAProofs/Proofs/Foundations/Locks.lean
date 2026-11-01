module
public import AvailableChainPCSA.Model.PC

public section

/-! Rank-stamped lock writes and deletion (pcsa34-r4.3 §3.7). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- Deletion keeps exactly the rows that pass the rank and conflict test. -/
theorem mem_deleteConflictingLeases (st : State n) (c : PC n) (row : Block × Nat × Time) :
    row ∈ (deleteConflictingLeases st c).base.obligations ↔
      row ∈ st.base.obligations ∧
        (rankAtLeast c (leaseRank st row.1) = false ∨ Block.compatible c.target row.1 = true) := by
  simp [deleteConflictingLeases_def, Bool.not_and]

/-- Deletion cannot add a lock. -/
theorem deleteConflictingLeases_subset (st : State n) (c : PC n) :
    (deleteConflictingLeases st c).base.obligations ⊆ st.base.obligations := by
  intro row h
  exact ((mem_deleteConflictingLeases st c row).mp h).1

/-- A compatible lock survives PC admission's deletion step. -/
theorem deleteConflictingLeases_keep (st : State n) (c : PC n) (row : Block × Nat × Time)
    (h : row ∈ st.base.obligations) (hc : Block.compatible c.target row.1 = true) :
    row ∈ (deleteConflictingLeases st c).base.obligations :=
  (mem_deleteConflictingLeases st c row).mpr ⟨h, Or.inr hc⟩

/-- Deletion preserves rank metadata, including metadata for removed locks. -/
theorem deleteConflictingLeases_rank (st : State n) (c : PC n) (b : Block) :
    leaseRank (deleteConflictingLeases st c) b = leaseRank st b := rfl

/-- Each write replaces the target's rank stamp. -/
theorem writeLease_rank (st : State n) (b : Block) (g : Nat) (deadline : Time)
    (ρ : Option PCRank) : leaseRank (writeLease st b g deadline ρ) b = ρ := by
  simp only [leaseRank_def, writeLease_def]
  have hn : st.leaseRanks.find? (fun _ => false) = none :=
    List.find?_eq_none.mpr (by simp)
  simpa using congrArg (fun x => (x.getD (b, ρ)).2) hn

/-- A lock write preserves the PC state, time, tree, and FG state. -/
theorem writeLease_frame (st : State n) (b : Block) (g : Nat) (deadline : Time)
    (ρ : Option PCRank) :
    (writeLease st b g deadline ρ).pcs = st.pcs ∧
    (writeLease st b g deadline ρ).pcStamps = st.pcStamps ∧
    (writeLease st b g deadline ρ).pcSnapshot = st.pcSnapshot ∧
    (writeLease st b g deadline ρ).base.now = st.base.now ∧
    (writeLease st b g deadline ρ).base.blocks = st.base.blocks ∧
    (writeLease st b g deadline ρ).fg = st.fg := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A write is allowed exactly when every PC fails to veto it. -/
theorem leaseWriteOK_iff (cs : List (PC n)) (ρ : Option PCRank) (b : Block) :
    leaseWriteOK cs ρ b = true ↔
      ∀ c ∈ cs, rankAtLeast c ρ = true → Block.compatible c.target b = true := by
  simp [leaseWriteOK_def, List.any_eq_false]

end AvailableChain.PCSA
end
