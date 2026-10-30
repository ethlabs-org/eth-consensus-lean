module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # Goldilocks runs: the event order (F.5 (run)) and joining (F.4)

F.4: a node awake on `[max(0, t − c − 1), t]` with `c + 1 ≥ 8Δ` restarted, if ever by `t`, after
a sleep before that window; the window holds the public time `t_{slot(t)−1}`, where the node
ticks, so the restart (which follows the sleep with no call between) is not after it. -/

namespace Consensus.Goldilocks.Compose

open SA

/-- **F.5 (run).** -/
theorem event_order : EventOrder := by
  intro P A dg H sg tr h
  refine ⟨fun i j hij => h.time_mono hij, h.phase_order, fun y hy j t x ht k hk => ?_,
    h.block_unforgeable, fun y hy i a ha haH => ?_, h.msg_unforgeable, h.finite⟩
  · exact (ht.2.1 k hk).2.2.2.2
  · refine h.att_unforgeable y hy i a ?_ haH
    rcases ha with ha | ⟨B, hB, haB⟩
    · exact Or.inl ha
    · exact Or.inr ⟨B, ⟨true, hB⟩, haB⟩

/-- **F.4.** -/
theorem ready_implies_joined : ReadyImpliesJoined := by
  intro sp ro dg H tr hrun y hy t c ht hc hawake
  have h := hrun.toLocalRun
  have hΔ := sp.toParams.hΔ
  have hm : max 0 (t - c - 1) ≤ t := max_le ht (by linarith)
  refine ⟨hawake t hm le_rfl, fun k hk hkt => ?_⟩
  obtain ⟨u, hu, huk, hs, hb⟩ := h.sleep_of_restart y hy k hk
  -- the sleep is before the window, so the window starts after `8Δ`
  have hum : u < max 0 (t - c - 1) := by
    by_contra hle
    exact hs (hawake u (not_lt.1 hle) (by linarith))
  have hmax : max 0 (t - c - 1) = t - c - 1 := max_eq_right (by
    rcases lt_max_iff.1 hum with h0 | h1 <;> linarith)
  rw [hmax] at hum
  have hsl : 2 ≤ sp.slot t := by
    have := (ts_le_iff_le_slot sp ht 2).1 (by simp only [SAParams.ts]; linarith)
    exact_mod_cast this
  refine ⟨by change 0 < sp.slot t; omega, ?_⟩
  -- `t_{slot(t) − 1}` is a public time of the window, so the restart is not after it
  have hup : t < sp.ts ((sp.slot t : Int) + 1) := by
    by_contra hle
    have := (ts_le_iff_le_slot sp ht _).1 (not_lt.1 hle)
    omega
  have hS : sp.toParams.slotTime (sp.toParams.slotOf t - 1) =
      4 * sp.Δ * ((sp.slot t : Int) - 1) := by
    rw [sp.slotTime_eq]
    push_cast [show 1 ≤ sp.slot t by omega]
    rfl
  have hSt : sp.toParams.slotTime (sp.toParams.slotOf t - 1) ≤ t := by
    have := (ts_le_iff_le_slot sp ht ((sp.slot t : Int) - 1)).2 (by omega)
    rw [hS]; exact this
  have hSw : t - c - 1 < sp.toParams.slotTime (sp.toParams.slotOf t - 1) := by
    simp only [SAParams.ts] at hup
    rw [hS]
    change t - c - 1 < 4 * sp.toParams.Δ * ((sp.slot t : Int) - 1)
    change t < 4 * sp.toParams.Δ * ((sp.slot t : Int) + 1) at hup
    nlinarith
  by_contra hgt
  push Not at hgt
  obtain ⟨j, x, hj⟩ := h.tick_of_awake y hy _ (by linarith)
    (sp.toParams.slotTime_public _) (hawake _ (by rw [hmax]; exact hSw.le) hSt)
  obtain ⟨hjc, hjt⟩ := group_call hj
  have hjk : j < k := by
    by_contra hkj
    have := h.time_mono (not_lt.1 hkj)
    linarith
  have := hb j hjk hjc
  linarith

end Consensus.Goldilocks.Compose

end
