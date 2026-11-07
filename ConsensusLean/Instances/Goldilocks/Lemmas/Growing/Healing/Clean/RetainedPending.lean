module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LeftEntry
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.LowFinalized
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HeldRoots
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FloorSource

public section

/-! # Frozen growing interface of the retained-origin transports

The growing forms of the retention transports of `Healing/Retention/{Boot,Prefix,Finality}`
that the clean cluster and its consumers read, frozen under their final names (static name +
`_at`). Each node is honest at its own cut; a reader of a held state is honest at an observation
time `t` after the state's cuts. Beyond the static statements, they add only the fault-count
bounds `≤ b`, because growing faults are counted only through the horizon:

* `low_finalized_below_origin_at` (`left_entry_origin_at` is proved in `Clean/LeftEntry`);
* `high_J_root_of_held_at_call_before_at`, `low_root_of_held_seed_at_call_at`;
* `high_floor_signed_source_of_row_bound_at`;
* `half_committee_at`: the voters of slot `m` honest at a later observation `t ≤ b` are half
  the committee.

Each theorem here is an open `sorry`; this module is deleted when the proofs land. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
