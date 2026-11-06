module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction

public section

/-! # Goldilocks milestone Persist, part 2

`PersistStatements` (C1.1 and its corollary) from `Lemmas/Compose/Persist/`. The bundle is proof
packaging for milestone lemmas, pinned by `ConsensusLeanTest/MilestoneAxioms.lean`, not separate
`Challenge` roots. `Challenge` certifies the obligations endpoint and the headline correctness
statement, together with the four generic review statements; see `docs/decisions.md`,
"Trusted surface and Challenge scope". -/

namespace Consensus.Goldilocks.Compose

/-- The statements of milestone Persist, part 2. -/
structure PersistStatements : Prop where
  honestFastConfirmationsPersist : HonestFastConfirmationsPersist
  recentSourceNextVote : RecentSourceNextVote

/-- **Persist, part 2.** -/
theorem persist_statements : PersistStatements where
  honestFastConfirmationsPersist := honest_fast_confirmations_persist
  recentSourceNextVote := recent_source_next_vote

end Consensus.Goldilocks.Compose

end
