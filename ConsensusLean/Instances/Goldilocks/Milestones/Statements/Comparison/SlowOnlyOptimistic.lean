module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.HealACAt

@[expose] public section

/-! # Tier A heal profile of the slow-only lock rule with the locked optimistic read (statement)

This rule is the slow-only lock rule plus the parent's optimistic confirmation with its lock:
* the confirmation update writes no fast lock;
* its slow lock is of width `k`;
* the optimistic confirmation of the current slot runs as the parent's: three quarters of the
  committee, a fast lock with the chained fast expiry `fastExpiry` and evidence release's weight
  (the optimistic test's count), and the record.

Its release is evidence release: the parent's unlock, then the release against the lock's weight.
There are no pre-confirmation certificates and no release outside the unlock. Its writes are the
write mode `WriteMode.slowOnly sp.k true`.

`HealProfileACSlowOnlyOptimistic` is the Tier A Slice 0 heal profile at that mode, with the free
static bound `acFree0` (`8k + 4` at `2·fcap < n`, `⊤` elsewhere).

**What it is about.** The statement is about the parent SA's handlers at the mode, for every
unlock oracle. The rule's own runs, those of `evidenceReleaseSAM` at this mode, enter it as for
the slow-only rule:
* `localRunU_projTraceM`: they project to runs at the mode with the unlock given;
* `standaloneRunU_of_er`: it supplies the incident's `StandaloneRunU`;
* `ac_healing_tight_er` at this mode: it is the H.1 instance on the rule's own runs.

A rule with a different release needs its own lawful unlock stage before its runs are covered.

**Scope.**
* The committee of every slot is all `n` validators: the optimistic test reads `3n/4`.
* The fast increment `c` (`2 ≤ c`) is live at this mode, because the optimistic lock's expiry is
  `fastExpiry`. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

/-- **The Tier A heal profile of the slow-only lock rule with the locked optimistic read**: at
every SA parameter set, the Tier A Slice 0 heal profile at the write mode
`WriteMode.slowOnly sp.k true` holds with `acFree0` (`8k + 4` at `2·fcap < n`, `⊤` elsewhere).
That mode writes no fast lock at the update, runs the optimistic confirmation with its lock, and
writes slow locks of width `k`. -/
def HealProfileACSlowOnlyOptimistic : Prop :=
  ∀ sp : SAParams, HealProfileACAt sp (WriteMode.slowOnly sp.k true) (acFree0 sp)

end Consensus.Goldilocks.Comparison

end
