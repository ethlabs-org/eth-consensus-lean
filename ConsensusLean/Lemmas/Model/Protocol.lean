module
public import ConsensusLean.Spec.Model.Protocol

public section

/-! Proofs about `Protocol.lean` definitions (moved from it). -/

namespace Consensus.Model

namespace SelSpec

variable {n : Nat}

/-- Every specification admits some selection. -/
theorem admits_exists (s : SelSpec n) : ∃ S, s.Admits S := by
  cases s with
  | fixed T => exact ⟨T, rfl⟩
  | sized m =>
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := min m n)
      (by simp [Finset.card_univ, Fintype.card_fin])
    exact ⟨S, hS⟩

end SelSpec

end Consensus.Model

end
