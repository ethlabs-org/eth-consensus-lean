module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- Joining projects independently of honesty; honesty is needed only for the state test. -/
theorem joined_projection : JoinedProjection := by
  intro sp ro dg H tr proposer h
  have joined := Compose.projAC_joinedAt_iff h.time_nonneg
  refine ⟨fun y t hy => ⟨joined y t, fun i hc hn hit => ?_⟩, fun t d => ?_⟩
  · have ht : 0 ≤ t := hit ▸ h.time_nonneg i
    have hr := (Compose.joined_projection sp ro dg (H t) (tr.upTo t) proposer
      (h.upTo ht) y hy t).2.1 i ((RunTrace.upTo_isCall _).mpr ⟨hit.le, hc⟩)
      (fun hr => hn ((RunTrace.upTo_restartAt _).mp hr).2) hit
    have hj : (tr.upTo t).JoinedAt y t ↔ tr.JoinedAt y t := by
      simp only [RunTrace.JoinedAt, RunTrace.upTo_restartAt, and_imp]
      exact ⟨fun hj k hk hkt => hj k hkt hk hkt, fun hj k _ hk hkt => hj k hk hkt⟩
    rw [RunTrace.upTo_state_of_le h.time_mono hit.le] at hr
    exact hj.symm.trans hr
  · congr 1
    ext y
    exact Iff.rfl.and (Iff.rfl.and (joined y t))

end Consensus.Goldilocks.Compose.Growing

end
