module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Interface

public section

/-! # Goldilocks Compose/AnyAC: one node composed with any AC (C0.1–C0.5)

The node statements over the configurations one honest node reaches. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- **C0.2, the restart half.** -/
theorem restart_keeps_fg : RestartKeepsFG (A := A) self := by
  sorry

/-- **C0.4.** -/
theorem tick_order : TickOrder dg self := by
  sorry

/-- **C0.5 (c), signing.** -/
theorem signed_only_in_ticks : SignedOnlyInTicks dg self := by
  sorry

/-- **C0.5, the cut law.** -/
theorem exec_is_cut_chain : ExecIsCutChain dg self := by
  sorry

/-- **C0.5 (a), (b).** -/
theorem ac_states_reachable : ACStatesReachable dg self := by
  sorry

/-- **C0.5 (c), the FG.** -/
theorem fg_states_reachable : FGStatesReachable dg self := by
  sorry

/-- **C0.5 (c), the record.** -/
theorem record_is_client_run : RecordIsClientRun dg self := by
  sorry

/-- **C0.5 (c), the sources.** -/
theorem sources_held : SourcesHeld dg self := by
  sorry

/-- **C0.2.** -/
theorem finalized_monotone : FinalizedMonotone dg self := by
  sorry

/-- **C0.1.** -/
theorem three_tips : ThreeTips dg self := by
  sorry

/-- **C0.3.** -/
theorem honest_block_accepted : HonestBlockAccepted dg self := by
  sorry

end Consensus.Goldilocks.Compose

end
