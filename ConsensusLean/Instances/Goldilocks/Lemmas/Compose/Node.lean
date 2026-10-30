module
public import ConsensusLean.Instances.Goldilocks.Statements.Compose.Node
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Reach

public section

/-! # Goldilocks Compose/AnyAC: one node composed with any AC (C0.1–C0.5)

The node statements over the configurations one honest node reaches. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)

/-- **C0.3.** -/
theorem honest_block_accepted : HonestBlockAccepted dg self := by
  sorry

/-- **C0.5 (b), the AC sees only accepted blocks** (goldilocks#36). Open: by cases on the event;
for a delivery from `Node.onBlock`, for a tick from the proposal step (`Node.proposeBlock`)
with the earlier tick cuts as the prefix chain. -/
theorem ac_sees_accepted_blocks : ACSeesAcceptedBlocks dg self := by
  sorry

end Consensus.Goldilocks.Compose

end
