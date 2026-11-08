module
public import ConsensusLeanTest.Goldilocks.Runs.SAHealing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SettledGenesis

@[expose] public section

/-! # Inclusion from a synchronous start, on a live run

(a) `syncStart_vote_head`: the one-validator standalone run of `SAHealing` is healthy from `0`,
so `ac_healing_of_sync_start` applies at every slot `p ≥ 2` with its premises discharged
(`StandaloneRun` at `g = 0`, an honest proposer, its actual proposal), and its unanimity
conclusion fixes the head of the run's actual slot-`p` vote. -/

namespace Consensus.Goldilocks.SA.Test.SyncStart

open Consensus.Goldilocks.SA.Test.SAHealing

/-- **Inclusion from a synchronous start is not vacuous**: at every slot `p ≥ 2` of the live
standalone run, the slot has an actual vote, and it heads the slot's proposal. -/
theorem syncStart_vote_head {p : Nat} (hp : 2 ≤ p) :
    ∃ i e, VoteAt run v0 i e ∧ e.msg.slot = p ∧ e.msg.head = (block p).root := by
  obtain ⟨i, e, hv, hs⟩ := vote_each_slot (by omega : 0 < p)
  exact ⟨i, e, hv, hs, (ac_healing_of_sync_start standaloneRun le_rfl hp (Set.mem_univ _)
    (honestProposal (by omega))).1 v0 (Set.mem_univ _) i e hv hs⟩

end Consensus.Goldilocks.SA.Test.SyncStart

end
