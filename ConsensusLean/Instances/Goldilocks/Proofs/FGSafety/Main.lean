module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Accountable
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Client
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Finality

public section

/-! # Goldilocks milestone M₁: FG safety

`FGSafety` from the claim groups of `Lemmas/FGChain/`: quorum intersection (G1.1), the
chain-state invariants and the facts about one block (G0.2, G0.7 (c), G0.9), finality before
the gate (G0.8), the client (G0.5, G0.10) and accountable safety (G1.3). -/

namespace Consensus.Goldilocks.FG

/-- **Milestone M₁ (FG safety).** -/
theorem fg_safety : FGSafety := fun gp =>
  { quorumIntersection := quorum_intersection gp
    chainInvariants := chain_invariants gp
    heightStep := height_step gp
    gatedConsumption := gated_consumption gp
    finalityBeforeGate := finality_before_gate gp
    retention := retention gp
    retentionThroughAppend := retention_through_append gp
    aggregation := aggregation gp
    clientSafety := client_safety gp
    accountableSafety := accountable_safety gp }

end Consensus.Goldilocks.FG

end
