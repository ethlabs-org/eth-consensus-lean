module
public import ConsensusLean.Spec.Model.System
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
public import ConsensusLean.Lemmas.Model.Protocol

public section

/-! # Mempool facts

A transaction held by a node at a deadline (L0 `CommLog.TxHeld` of the run's
log: in its inbox at some time in `[0, d]`) is in its mempool at every tick
strictly after the deadline: the mempool is cumulative (all arrivals at
times up to the tick) and survives restarts. `inbox v τ` is what arrives at
`τ`; arrivals are handled at the delivery, but ticks come before deliveries
within a time, so an arrival at the deadline is first used by a tick at a
later time. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

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
