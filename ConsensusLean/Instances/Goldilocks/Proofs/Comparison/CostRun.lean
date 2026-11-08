module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.CostRun
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.TickOnce

public section

/-! # Cost at Tier A on node runs (proof)

* `tickOnceRun`: one AC tick per honest node and time on the AC projection of every node run
  (`acTick_unique`). -/

namespace Consensus.Goldilocks.Comparison

theorem tickOnceRun : TickOnceRun :=
  fun _ _ _ _ _ _ _ h => Compose.acTick_unique h

end Consensus.Goldilocks.Comparison

end
