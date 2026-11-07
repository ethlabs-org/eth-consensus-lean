module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Joined
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Outputs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Sync

public section

/-! # Growing Compose: run projections, persistence and always rows -/

namespace Consensus.Goldilocks.Compose.Growing

/-- The growing run projections, without rebuilding static cache or service invariants. -/
structure RunStatements : Prop where
  acProjection : ACProjection
  fgProjection : FGProjection
  goldilocksACProjection : GoldilocksACProjection
  joinedProjection : JoinedProjection
  syncProjection : SyncProjection

/-- All A3 run projections. -/
theorem run_statements : RunStatements where
  acProjection := ac_projection
  fgProjection := fg_projection
  goldilocksACProjection := goldilocks_ac_projection
  joinedProjection := joined_projection
  syncProjection := sync_projection

/-- C1.1 and its recent-source corollary, with honesty and fault counts at their own cuts. -/
structure PersistStatements : Prop where
  honestFastConfirmationsPersist : HonestFastConfirmationsPersist
  recentSourceNextVote : RecentSourceNextVote

/-- All A3 persistence statements. -/
theorem persist_statements : PersistStatements where
  honestFastConfirmationsPersist := honest_fast_confirmations_persist
  recentSourceNextVote := recent_source_next_vote

end Consensus.Goldilocks.Compose.Growing

namespace Consensus.Goldilocks.Regimes.Growing

/-- The six regime rows that hold independently of a liveness regime. -/
structure AlwaysStatements : Prop where
  outputsNested : OutputsNested
  finalizedMonotone : FinalizedMonotone
  outputsValid : OutputsValid
  finalAccountable : FinalAccountable
  nonFraming : NonFraming
  finalizedSafe : FinalizedSafe

/-- All six growing always rows. -/
theorem always_statements : AlwaysStatements where
  outputsNested := outputs_nested
  finalizedMonotone := finalized_monotone
  outputsValid := outputs_valid
  finalAccountable := final_accountable
  nonFraming := non_framing
  finalizedSafe := finalized_safe

end Consensus.Goldilocks.Regimes.Growing

end
