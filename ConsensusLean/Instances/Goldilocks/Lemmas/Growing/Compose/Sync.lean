module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Growing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- Service projects with sender and reader honest at their own cuts. -/
theorem sync_projection : SyncProjection := by
  intro P A dg H sg tr proposer ΔF a b ini h hs
  have state {y i} (hy : y ∈ H (tr.time i)) : tr.projAC.state y i = (tr.state y i).ac := by
    have hp := Compose.projAC_state (h.upTo (h.time_nonneg i)) hy i
    simpa only [RunTrace.upTo_projAC,
      Trace.upTo_state tr.projAC y (i := i) (fun k hk => h.time_mono hk.le),
      RunTrace.upTo_state_of_le h.time_mono le_rfl] using hp
  refine ⟨fun x i m hx hsa hai hib y j ℓ hy hc hdl => ?_,
    fun x i B hx hacc hai hib y j ℓ hy hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, Compose.projAC_callAt.mp hc₀, by
      rw [state hx] at hm
      exact hm⟩
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x i m hx hsa' ⟨hai, hib⟩ y j hy
      ⟨_, Compose.projAC_callAt.mp hc⟩ (by rw [← Compose.projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [Compose.projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', Compose.projAC_callAt.mpr hc', Or.inl hm'⟩,
      ⟨ℓ', Compose.projAC_callAt.mpr hc', Or.inr hm'⟩]
  · apply h.acRelayAt (σ := tr.time i) hx hacc hy hc hanc
    intro k hki hx' hk hj hF
    rw [← hki]
    exact hs.relay x k B hx' hk ⟨hki ▸ hai, hki ▸ hib⟩ y j hy hj
      (by rw [hki, ← Compose.projAC_deadline]; exact hdl) hF

end Consensus.Goldilocks.Compose.Growing

end
