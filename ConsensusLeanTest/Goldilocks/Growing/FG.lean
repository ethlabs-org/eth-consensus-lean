module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.FGStore.Main

public section

/-! # Dynamic FG milestone contracts and axiom pins -/

namespace Consensus.Goldilocks.Store.Growing.Test

/-- The trace bundle proves the authoritative dynamic statement. -/
theorem trace_contract : FGStoreTrace := fg_store_trace

/-- The service bundle proves all four authoritative dynamic service statements. -/
theorem service_contract : FGStoreService := fg_store_service

/-- info: 'Consensus.Goldilocks.Store.Growing.Test.trace_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_contract

/-- info: 'Consensus.Goldilocks.Store.Growing.Test.service_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms service_contract

end Consensus.Goldilocks.Store.Growing.Test

end
