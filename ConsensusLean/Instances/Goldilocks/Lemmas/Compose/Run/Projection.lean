module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.ACProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection

public section

/-! # Goldilocks runs: the projections onto the component traces (C0.5)

`ac_projection` and `fg_projection` are in `Run/ACProjection` and `Run/FGProjection`. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

/-- A restart of the AC projection is a restart of the run. -/
theorem projAC_restartAt {y : Fin P.n} {k : Nat} : tr.projAC.RestartAt y k ↔ tr.RestartAt y k :=
  ⟨fun ⟨ℓ, hc, hr⟩ => ⟨ℓ, projAC_callAt.1 hc, hr⟩, fun ⟨ℓ, hc, hr⟩ => ⟨ℓ, projAC_callAt.2 hc, hr⟩⟩

/-- The AC projection's latest wakes are the run's. -/
theorem projAC_lastWake (y : Fin P.n) : tr.projAC.lastWake y = tr.lastWake y := by
  funext k
  induction k with
  | zero =>
    simp only [ACTrace.lastWake, RunTrace.lastWake]
    by_cases hr : tr.RestartAt y 0
    · simp only [projAC_restartAt.2 hr, hr, ↓reduceIte]
      rfl
    · simp [hr, mt projAC_restartAt.1 hr]
  | succ k ih =>
    simp only [ACTrace.lastWake, RunTrace.lastWake, ih]
    by_cases hr : tr.RestartAt y (k + 1)
    · simp only [projAC_restartAt.2 hr, hr, ↓reduceIte]
      rfl
    · simp [hr, mt projAC_restartAt.1 hr]

/-- The AC projection's deadlines are the run's with `Δ`. -/
theorem projAC_deadline (y : Fin P.n) (k : Nat) (τ : Time) :
    tr.projAC.deadline y k τ = tr.deadline y k τ P.Δ := by
  simp only [ACTrace.deadline, RunTrace.deadline, projAC_lastWake]

/-- **The honest-object facts of the Goldilocks run's AC projection.** -/
theorem goldilocks_ac_projection : GoldilocksACProjection := by
  sorry

/-- **`Sync` projects**: a send or admission of the AC projection is the run's, and its
processing is the run's; an `ac_on_block(B)` follows the FG acceptance of `B` at its time, whose
relay is an acceptance of `B`, followed at once by the AC call of `B` (not a restart, so with the
same deadline). -/
theorem sync_projection : SyncProjection := by
  intro P A dg H sg tr ΔF a b h hs
  refine ⟨fun x hx i m hsa hai hib y hy j ℓ hc hdl => ?_,
    fun x hx i B hacc hai hib y hy j ℓ hc hdl hanc => ?_⟩
  · obtain ⟨ℓ₀, hc₀, hm⟩ := hsa
    have hsa' : tr.SendOrAdmitAt x i m := ⟨ℓ₀, projAC_callAt.1 hc₀, by
      rw [projAC_state h hx] at hm
      exact hm⟩
    obtain ⟨k, hkj, htk, hp, hlt⟩ := hs.message x hx i m hsa' ⟨hai, hib⟩ y hy j
      ⟨_, projAC_callAt.1 hc⟩ (by rw [← projAC_deadline]; exact hdl)
    refine ⟨k, hkj, htk, ?_, by rw [projAC_deadline]; exact hlt⟩
    rcases hp with ⟨ℓ', hc', hm'⟩ | ⟨ℓ', hc', hm'⟩
    exacts [⟨ℓ', projAC_callAt.2 hc', Or.inl hm'⟩, ⟨ℓ', projAC_callAt.2 hc', Or.inr hm'⟩]
  · obtain ⟨ℓ₀, hc₀, hb⟩ := hacc
    have hc := projAC_callAt.1 hc
    obtain ⟨i', rfl, hi', hti⟩ := acBlock_prev h hx (projAC_callAt.1 hc₀) hb
    have hfr : ℓ.frame.F = (tr.state y j).fg.F := by
      rw [(h.cutLaw y hy j _ hc).1]
      rfl
    obtain ⟨k, hkj, hk, hlt⟩ := hs.relay x hx i' B hi' ⟨hti ▸ hai, hti ▸ hib⟩ y hy j ⟨_, hc⟩
      (by rw [hti, ← projAC_deadline]; exact hdl) (hfr ▸ hanc)
    obtain ⟨ℓ', hc', hb', htk⟩ := accept_next h hy hk
    have hkj' : k + 1 ≤ j := by
      rcases Nat.lt_or_eq_of_le hkj with hlt' | rfl
      · omega
      · cases Option.some.inj (hk.2.symm.trans hc.2)
    have hnr : ¬ tr.RestartAt y (k + 1) := fun ⟨ℓr, hcr, hr⟩ => by
      cases Option.some.inj (hc'.2.symm.trans hcr.2)
      rw [hb'] at hr
      cases hr
    refine ⟨k + 1, hkj', ⟨ℓ', projAC_callAt.2 hc', hb'⟩, ?_⟩
    change tr.time (k + 1) < tr.projAC.deadline y (k + 1) (tr.time (i' + 1))
    rw [projAC_deadline, htk, ← hti]
    simp only [RunTrace.deadline, RunTrace.lastWake, hnr, ite_false] at hlt ⊢
    exact hlt

/-- **Joining and participation project.** -/
theorem joined_projection : JoinedProjection := by
  sorry

end Consensus.Goldilocks.Compose

end
