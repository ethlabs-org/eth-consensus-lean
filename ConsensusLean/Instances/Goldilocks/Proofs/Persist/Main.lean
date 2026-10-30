module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction

public section

/-! # Goldilocks milestone Persist, part 2

`PersistStatements` (C1.1 and its corollary) from `Lemmas/Compose/Persist/`. -/

namespace Consensus.Goldilocks.Compose

/-- **Persist, part 2.** -/
theorem persist_statements : PersistStatements where
  honestFastConfirmationsPersist := honest_fast_confirmations_persist
  recentSourceNextVote := recent_source_next_vote

end Consensus.Goldilocks.Compose

end
