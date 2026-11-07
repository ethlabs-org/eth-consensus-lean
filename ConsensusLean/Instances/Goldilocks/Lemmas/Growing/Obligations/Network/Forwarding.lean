module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Pending

public section

/-! # Forwarding at acceptance under growing faults

`forwardAtAcceptance_at`: every acceptance of the canonical growing trace by a node honest at its
cut has an actual, exactly decoded same-event forwarding publication (the growing form of
`Obligations/ForwardingDecode.forwardAtAcceptance`). Open: the decoding invariants of
`ForwardingDecode` are to be carried over with honesty at each event. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every acceptance by a node honest at its cut has an actual, exactly decoded same-event
forwarding publication. -/
theorem forwardAtAcceptance_at (hv : rho.ExecutionValid) :
    ForwardAtAcceptanceAt S rho hn (simTraceAt S rho hn) (cutMap S rho hn)
      (publisherExecution S rho) := by
  sorry

end Consensus.Goldilocks.Obligations.Growing

end
