module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealACAt

@[expose] public section

/-! # Tier A heal profile of the slow-only lock rule (statement)

The **slow-only lock rule** is the evidence-release SA with two changes:
* the confirmation update writes no fast lock;
* there is no optimistic confirmation.

So every lock is a slow lock: on the deepest unvetoed block of the update's path that the saved
results of the previous `k − 1` slots extend, with expiry `s + k`, and with evidence release's
weight (the maximum over its `k` formation slots). The rest is evidence release's SA: the 6Δ
confirmation and its veto, the fork choice, the vote, and the parent's unlock followed by
evidence release. Its writes are the write mode `WriteMode.slowOnly sp.k false`.

`HealProfileACSlowOnly` is the Tier A Slice 0 heal profile at that mode, with the free static
bound `acFree0` (`8k + 4` at `2·fcap < n`, `⊤` elsewhere).

**What it is about.** The statement is about the parent SA's handlers at the mode, for every
unlock oracle. The rule's own runs enter it as follows:
* the evidence-release SA at a write mode is `evidenceReleaseSAM`;
* at mode `m`, its runs, forgotten, are runs at mode `m` with the unlock given by its oracle
  (`localRunU_projTraceM`);
* `standaloneRunU_of_er` turns H.1's premises read on the forgotten trace into the incident's
  `StandaloneRunU`;
* the H.1 instance on the rule's own runs is `ac_healing_tight_er` at this mode.

**Scope.**
* The committee of every slot is all `n` validators: the fast test, the optimistic test and the
  unlock read `n`.
* The fast increment `c` (`2 ≤ c`) is vacuous at this mode. `c` is read only by `fastExpiry`, and
  no lock written at this mode takes a fast expiry. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

/-- **The Tier A heal profile of the slow-only lock rule**: at every SA parameter set, the Tier A
Slice 0 heal profile at the write mode `WriteMode.slowOnly sp.k false` holds with `acFree0`
(`8k + 4` at `2·fcap < n`, `⊤` elsewhere). That mode writes no fast lock at the update, has no
optimistic confirmation, and writes slow locks of width `k`. -/
def HealProfileACSlowOnly : Prop :=
  ∀ sp : SAParams, HealProfileACAt sp (WriteMode.slowOnly sp.k false) (acFree0 sp)

end Consensus.Goldilocks.Comparison

end
