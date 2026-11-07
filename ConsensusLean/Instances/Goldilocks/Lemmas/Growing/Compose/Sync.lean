module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.Run.Growing
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Retention
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Projection

public section

namespace Consensus.Goldilocks.Compose.Growing

/-- Service projects with sender and reader honest at their own cuts. -/
theorem sync_projection : SyncProjection := by
  intro P A dg H sg tr proposer ΔF a b h hs
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
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := Compose.projAC_callAt.mp hc
    have hc₀' : (tr.upTo (tr.time i)).CallAt x i (.ac ℓ₀) :=
      (Trace.upTo_callAt _).mpr ⟨le_rfl, Compose.projAC_callAt.mp hc₀⟩
    obtain ⟨i', rfl, hi', hti⟩ :=
      Compose.acBlock_prev (h.upTo (h.time_nonneg i)) hx hc₀' hb
    change tr.time i' = tr.time (i' + 1) at hti
    have hi' := ((Trace.upTo_callAt _).mp hi').2
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.cutLaw y j _ hc hy).1]
      rfl
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x i' B (hti ▸ hx) hi'
      ⟨hti ▸ hai, hti ▸ hib⟩ y j hy ⟨_, hc⟩
      (by rw [hti, ← Compose.projAC_deadline]; exact hdl) (hfr ▸ hanc)
    have hk' : (tr.upTo (tr.time j)).CallAt y k (.fg (.block B true)) :=
      (Trace.upTo_callAt _).mpr ⟨h.time_mono hkj, hk⟩
    obtain ⟨ℓ', hc', hb', htk⟩ :=
      Compose.accept_next (h.upTo (h.time_nonneg j)) hy hk'
    change tr.time (k + 1) = tr.time k at htk
    have hc' := ((Trace.upTo_callAt _).mp hc').2
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', Compose.projAC_callAt.mpr hc', hb'⟩, ?_⟩
    change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (tr.time (i' + 1))
    rw [Compose.projAC_deadline, htk, ← hti]
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

end Consensus.Goldilocks.Compose.Growing

end
