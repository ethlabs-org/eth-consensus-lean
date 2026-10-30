module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Goldilocks runs: the run statements of milestone Persist, part 1 -/

namespace Consensus.Goldilocks.Compose

/-- **Persist, part 1: the run statements.** -/
theorem run_statements : RunStatements where
  eventOrder := event_order
  readyImpliesJoined := ready_implies_joined
  acProjection := ac_projection
  fgProjection := fg_projection
  goldilocksACProjection := goldilocks_ac_projection
  groupStatesReachable := group_states_reachable
  syncProjection := sync_projection
  joinedProjection := joined_projection

end Consensus.Goldilocks.Compose

end
