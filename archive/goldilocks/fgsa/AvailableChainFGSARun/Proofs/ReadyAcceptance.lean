module
public import AvailableChainFGSARun.Proofs.Acceptance
public import AvailableChainFGSARun.Proofs.Reachable
public import AvailableChainGeneric.Proofs.V2.Duty.Receipt
public import AvailableChainKitV2.DutySleep

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- On a valid NoRestart run, an awake receiver was awake at each earlier horizon time. -/
theorem fgsa_awake_before_noRestart (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    (hNR : V2.D.NoRestart rho) (w : V) (hw : w ∈ rho.honest)
    (t : Time) (ht : t ≤ rho.horizon) (ha : E.awake w t = true)
    (u : Time) (hu : 0 ≤ u) (hut : u ≤ t) : E.awake w u = true := by
  by_cases h : E.awake w u = true
  · exact h
  have hf : E.awake w u = false := Bool.eq_false_iff.mpr h
  obtain ⟨wake, hUw, hwt, hWake⟩ := V2.D.Engine.wake_between hut hf ha
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hV.wake_restart w hw wake (lt_of_le_of_lt hu hUw) (hwt.trans ht) hWake)
  exact (hNR j w wake hj).elim

/-- History is current processing when the local run has no restart. -/
theorem fgsa_historySafeAt_noRestart (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hNR : V2.D.NoRestart rho) (w : V) (o : Obj p) (a : Time) :
    Gen.V2.Duty.HistorySafeAt E rho w o a := by
  rintro ⟨k, hk, hp⟩
  change (fgsa p c).processed (V2.D.Run.stateBefore E rho (V2.D.Run.actionCut rho a) w) o =
    true
  exact (fgsaHooks p c).processed_stable E rho hS w o k _ hk (hNR.restartFree w k _) hp

/-- The P2 service core gives a current receipt for a ready NoRestart receiver. -/
theorem fgsa_processed_by_deadline_ready (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hV : V2.D.ExecutionValid E rho)
    (hNR : V2.D.NoRestart rho) (dl : Time → Time) (cut : Time) (o : Obj p)
    (t : Time) (w : V)
    (hD : Gen.V2.Duty.DeliveryWithinOn E rho (fun o => ¬ isRowObject o) dl cut)
    (hQ : ¬ isRowObject o) (hT : Gen.V2.Duty.Trigger E rho o t)
    (hw : w ∈ rho.honest) (ht0 : 0 ≤ t) (htH : t ≤ rho.horizon)
    (hcut : dl t ≤ cut) (hlt : t < dl t) (hhor : dl t ≤ rho.horizon)
    (hAwake : V2.D.AwakeOn E w t (dl t))
    (hAct : fgsaAdmissionTime p o ≤ Gen.V2.Duty.pubFloor E t)
    (hDeps : ∀ j t', t ≤ t' → t' < dl t → V2.D.Run.handlesAt E rho j w o t' →
      (fgsa p c).wellFormed o = true ∧
        (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j w) o = true)
    (hNX : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho (dl t) w) o = false) :
    (fgsa p c).processed (V2.D.Run.stateBeforeTime E rho (dl t) w) o = true := by
  have hS := hV.toScheduleWellFormed
  have hReady : Gen.V2.Duty.ReadyTrigger E rho o t w t (dl t) := by
    rcases hT with ⟨v, hv, he⟩ | ⟨v, hv, i, he⟩
    · exact ⟨v, hv, Or.inl he, hAwake⟩
    · exact ⟨v, hv, Or.inr ⟨i, he⟩, hAwake⟩
  have hService := Gen.V2.Duty.service_of_readyTrigger hD hQ hReady hw (le_refl t) ht0
    hlt hcut hhor hNX
  apply Gen.V2.Duty.processed_by_deadline_of_service E rho (fgsaTimely p)
    (fgsaAcceptanceInv p) w o t (dl t) hS hlt hService
    (fgsa_historySafeAt_noRestart E rho hS hNR w o t)
    (hNR.restartFree w _ _) (fgsaHooks p c) (fgsaAcceptance p c) ?_ hNX
  intro j t' htt htd hh
  have hdeps := hDeps j t' htt htd hh
  refine ⟨cstoreInv_stateBefore E rho j w, hdeps.1, hdeps.2, ?_⟩
  let floor := Gen.V2.Duty.pubFloor E t
  have hf0 : 0 ≤ floor :=
    mul_nonneg (Int.ediv_nonneg ht0 (le_of_lt E.Δ_pos)) (le_of_lt E.Δ_pos)
  have hft : floor ≤ t := Gen.V2.Duty.pubFloor_le E t
  have hpub : V2.PublicTime E floor := by
    refine ⟨(t / E.Δ).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (Int.ediv_nonneg ht0 (le_of_lt E.Δ_pos))]
    rfl
  have ha := fgsa_awake_before_noRestart E rho hV hNR w hw t htH
    (hAwake t (le_refl t) hlt) floor hf0 hft
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
    (hS.tick_total w hw floor hpub hf0 (hft.trans htH) ha)
  obtain ⟨parent, he, _⟩ := hh
  have hkj := V2.D.Engine.tick_index_lt_delivery E rho hS hk he (hft.trans htt)
  have hm := V2.D.Engine.stateBefore_now_mono_noRestart (fgsaClock p c) E rho hS hNR
    (Nat.succ_le_of_lt hkj) w
  rw [(V2.D.Run.step_tick_eq E rho hk).1, V2.D.Engine.ClockLaws.now_tick,
    fgsa_clock_now p c (V2.D.Run.stateBefore E rho j w)] at hm
  exact hAct.trans hm

end AvailableChain.FGSA.Run
end
