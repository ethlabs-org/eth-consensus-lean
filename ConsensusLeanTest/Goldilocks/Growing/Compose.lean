module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Compose.Main

public section

/-! # Growing Compose milestone contracts and axiom pins -/

namespace Consensus.Goldilocks.Compose.Growing.Test

/-- Every run projection is proved without unfinished dependencies. -/
theorem run_contract : RunStatements := run_statements

/-- Persistence and its corollary discharge the authoritative growing contracts. -/
theorem persist_contract : PersistStatements := persist_statements

/-- The six always rows discharge the authoritative growing contracts. -/
theorem always_contract : Regimes.Growing.AlwaysStatements := Regimes.Growing.always_statements

set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.Compose.Growing.Test.run_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_contract

/-- info: 'Consensus.Goldilocks.Compose.Growing.Test.persist_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms persist_contract

/-- info: 'Consensus.Goldilocks.Compose.Growing.Test.always_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms always_contract

end Consensus.Goldilocks.Compose.Growing.Test

end
