module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Continuation
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Realizable
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Safe
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Live
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Obligations.Main

public section

/-! # Goldilocks continuation after healing (entry module)

`goldilocks_continues`: the side property `GoldilocksContinues`, continuation after healing under
corruption growth. Its three fields are `continued_safe_growing` (module `Safe`),
`continued_live_growing` (module `Live`) and `continues_realizable` (module `Realizable`); the
first two from Goldilocks correctness, discharged by `goldilocks_correct`. -/

namespace Consensus.Goldilocks

/-- **Goldilocks continues after healing under corruption growth.** -/
theorem goldilocks_continues : GoldilocksContinues := fun S A V _ _ =>
  ⟨continued_safe_growing Growing.goldilocks_correct S A V,
    continued_live_growing Growing.goldilocks_correct S A V, continues_realizable S A V⟩

end Consensus.Goldilocks

end
