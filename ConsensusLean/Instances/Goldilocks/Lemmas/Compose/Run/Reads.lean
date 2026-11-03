module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks runs: reads between AC calls

The confirmed output and the head read the AC state `𝒜` and the frame `fg_to_ac(Σ)`, and the
frame reads only the tree and the finality caches of `Σ`, not its pool. Of the FG cuts,
`fg_on_attestation` changes only the pool, `fg_attest` only the record, and a refused
`fg_on_block` nothing; an accepted `fg_on_block` is followed in its event by its `ac_on_block`
(`accept_next`, at a position `≠ 0`, `accept_next_pos`). So at a point between two events of an
honest node (cut `j` is not a later cut of an event of the node), its AC state and frame are those
after its last AC call before `j` (with that call's frame), or the initial ones when it has made
none (`read_between_calls`; the mapping's "Reads between AC calls", consensus-lean#91). -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

end Consensus.Goldilocks.Compose

end
