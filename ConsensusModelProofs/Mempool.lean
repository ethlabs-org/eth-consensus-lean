module
public import ConsensusModel.System

@[expose] public section

/-! # Mempool facts

A transaction held by a node before a deadline is in its mempool at the
deadline: the mempool is cumulative and survives restarts. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

omit [DecidableEq V] in
/-- A transaction held by `v` before `p` is in `v`'s mempool at `p`. -/
theorem txHeld_mem_mempool (rho : Run F E) {x : Tx} {v : V} {p : Time}
    (hs : rho.TxHeld v x p) : x ∈ mempool rho.inbox v p := by
  obtain ⟨τ, hτ, hτp, hx⟩ := hs
  dsimp only [Time] at *
  rw [mempool, ite_eq_right (not_lt.mpr (le_trans hτ hτp.le))]
  apply List.mem_flatMap.mpr
  refine ⟨τ, ?_, hx⟩
  rw [List.bind_eq_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨τ.toNat, List.mem_range.mpr ?_, ?_⟩
  · have := Int.toNat_le_toNat hτp.le; omega
  · change τ ∈ [(τ.toNat : Int)]
    simp [Int.toNat_of_nonneg hτ]

end Run
end Consensus.Model
end
