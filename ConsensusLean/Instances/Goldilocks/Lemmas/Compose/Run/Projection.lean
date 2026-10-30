module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers

public section

/-! # Goldilocks runs: the projections onto the component traces (C0.5) -/

namespace Consensus.Goldilocks.Compose

/-- **C0.5, the AC projection.** -/
theorem ac_projection : ACProjection := by
  sorry

/-- **C0.5 (c), the FG projection.** -/
theorem fg_projection : FGProjection := by
  sorry

/-- **The honest-object facts of the Goldilocks run's AC projection.** -/
theorem goldilocks_ac_projection : GoldilocksACProjection := by
  sorry

/-- **`Sync` projects.** -/
theorem sync_projection : SyncProjection := by
  sorry

/-- **Joining and participation project.** -/
theorem joined_projection : JoinedProjection := by
  sorry

end Consensus.Goldilocks.Compose

end
