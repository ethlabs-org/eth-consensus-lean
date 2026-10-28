module
public import ConsensusModel.System

@[expose] public section

/-! # Mempool facts

A transaction held by a node at a deadline (L0 `CommLog.TxHeld` of the run's
log: in its inbox at some time in `[0, d]`) is in its mempool at every tick
strictly after the deadline: the mempool is cumulative and survives restarts.
(Receipt at the deadline is processed at the next tick.) -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

/-- A transaction held by `v` at `d` is in `v`'s mempool at every `p > d`. -/
theorem txHeld_mem_mempool (rho : Run F E) {x : Tx} {v : V} {d p : Time}
    (hs : CommLog.TxHeld rho.log v x d) (hdp : d < p) : x ∈ mempool rho.inbox v p := by
  obtain ⟨τ, hτ, hτd, hx⟩ := hs
  have hτp : τ < p := lt_of_le_of_lt hτd hdp
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
