module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Run

public section

/-! # Goldilocks runs: the event order (F.5 (run)) and joining (F.4) -/

namespace Consensus.Goldilocks.Compose

/-- **F.5 (run).** -/
theorem event_order : EventOrder := by
  intro P A dg H sg tr h
  refine ⟨fun i j hij => h.time_mono hij, h.phase_order, fun y hy j t ht k hk => ?_,
    h.block_unforgeable, fun y hy i a ha haH => ?_, h.msg_unforgeable, h.finite⟩
  · exact (ht.2.1 k hk).2.2.2.2
  · refine h.att_unforgeable y hy i a ?_ haH
    rcases ha with ha | ⟨B, hB, haB⟩
    · exact Or.inl ha
    · exact Or.inr ⟨B, ⟨true, hB⟩, haB⟩

/-- **F.4.** -/
theorem ready_implies_joined : ReadyImpliesJoined := by
  sorry

end Consensus.Goldilocks.Compose

end
