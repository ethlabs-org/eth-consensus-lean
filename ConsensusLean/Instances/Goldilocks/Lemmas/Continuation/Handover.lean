module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation

public section

/-! # The hand-over regime (generic facts)

Facts about `System.Handover` that the continuation proof reads: a hand-over at or after the
horizon is the healthy regime (`Handover.healthy`). -/

namespace Consensus

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog : Type}

omit [DecidableEq V] in
/-- A hand-over at or after the horizon is the healthy regime: faults only grow, so the fault
bound at `T` bounds the faults at the horizon, and the awake window `[max g 0, horizon]` lies in
`[max g 0, T]`. -/
theorem Handover.healthy {K : Contract Prog} {g T : Time} {r : S.Run}
    (h : S.Handover K g T r) (hT : (S.pt r).horizon ≤ T) : S.Healthy K g r := by
  obtain ⟨hnet, ⟨hf, haw⟩, hΔ, -, -⟩ := h
  unfold System.Healthy
  refine ⟨hnet, ⟨lt_of_le_of_lt ?_ hf, fun v t hg ht => haw v t hg (ht.trans hT)⟩, hΔ⟩
  exact_mod_cast Finset.card_le_card ((S.pt r).faultyAt_mono hT)

end System

end Consensus

end
