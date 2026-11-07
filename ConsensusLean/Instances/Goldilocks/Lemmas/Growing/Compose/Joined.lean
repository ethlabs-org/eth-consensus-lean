module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- Joining projects independently of honesty; honesty is needed only for the state test. -/
theorem joined_projection : JoinedProjection := by
  intro sp ro dg H tr proposer h
  have joined (y : Fin sp.n) (t : Time) : tr.JoinedAt y t ↔ SA.JoinedAt tr.projAC y t := by
    unfold RunTrace.JoinedAt SA.JoinedAt
    refine forall_congr' fun k => ?_
    rw [Compose.projAC_restartAt]
    refine imp_congr_right fun _ => imp_congr_right fun _ => ?_
    -- The arithmetic conversion is independent of the retained cohort.
    have hΔ := sp.toParams.hΔ
    change (0 < sp.toParams.slotOf t ∧
      tr.time k ≤ sp.toParams.slotTime (sp.toParams.slotOf t - 1)) ↔
        tr.time k ≤ sp.ts ((sp.slot t : Int) - 1)
    rcases Nat.eq_zero_or_pos (sp.toParams.slotOf t) with hz | hp
    · simp only [SA.SAParams.slot, hz, lt_irrefl, false_and, false_iff, not_le,
        SA.SAParams.ts]
      push_cast
      have := h.time_nonneg k
      linarith
    · rw [sp.slotTime_eq]
      simp only [hp, true_and, SA.SAParams.ts, SA.SAParams.slot]
      push_cast [Nat.one_le_iff_ne_zero.mpr hp.ne']
      rfl
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
