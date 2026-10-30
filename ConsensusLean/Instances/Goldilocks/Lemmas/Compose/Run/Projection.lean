module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection

public section

/-! # Goldilocks runs: the projections onto the component traces (C0.5)

`ac_projection` and `fg_projection` are in `Run/ACProjection` and `Run/FGProjection`. -/

namespace Consensus.Goldilocks.Compose

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
