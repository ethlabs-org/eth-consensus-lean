module
public import AvailableChainFGCompose.Statements.ResetCut
public import AvailableChainFGCompose.Proofs.Restart
public import AvailableChainKitFG.StoreBounds

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable (T : FGTiming) (L : FGTimingLaws T) (Jst : Time)

include L in
private theorem d6_action_period (r : Nat) :
    T.action r = (r : Time) * period T + 6 * T.delta := by
  rw [L.action_eq, L.gate_eq, L.proposal_eq]
  unfold period
  push_cast
  ring

include L in
/-- The supplied round size makes the period at least eight deltas. -/
theorem reset_period_lower : 8 * T.delta ≤ period T := by
  have hR : (2 : Time) ≤ T.roundSlots := by exact_mod_cast L.rounds
  unfold period
  nlinarith [L.delta_pos]

include L in
/-- The mathematical clock reaches every recovery start. -/
theorem reset_action_exists : ∃ r, Jst ≤ T.action r := by
  refine ⟨Jst.toNat + 1, ?_⟩
  rw [d6_action_period T L]
  have hP : 1 ≤ period T := by
    have hd : 1 ≤ T.delta := L.delta_pos
    have hp := reset_period_lower T L
    linarith
  have hn := Int.natCast_nonneg Jst.toNat
  have ht := Int.self_le_toNat Jst
  push_cast
  nlinarith [L.delta_pos]

theorem reset_rG_after : Jst ≤ T.action (resetFirstRound T L Jst) := by
  unfold resetFirstRound
  exact Nat.find_spec (p := fun r => Jst ≤ T.action r) _

theorem reset_rG_first (r : Nat) (hr : Jst ≤ T.action r) :
    resetFirstRound T L Jst ≤ r := Nat.find_min' _ hr

theorem reset_cut : resetCutTime T L Jst = T.action (resetFirstRound T L Jst + 2) := rfl

/-- The nonnegative recovery start gives the first action's strict upper bound. -/
theorem reset_first_action_upper (hstart : 0 ≤ Jst) :
    T.action (resetFirstRound T L Jst) < Jst + period T := by
  by_cases hz : resetFirstRound T L Jst = 0
  · rw [hz, d6_action_period T L]
    have hp := reset_period_lower T L
    simp only [Nat.cast_zero, zero_mul, zero_add]
    linarith [L.delta_pos]
  · have hpred : T.action (resetFirstRound T L Jst - 1) < Jst := by
      by_contra hn
      have hm := reset_rG_first T L Jst (resetFirstRound T L Jst - 1) (le_of_not_gt hn)
      omega
    rw [d6_action_period T L] at hpred ⊢
    have hn : 1 ≤ resetFirstRound T L Jst := by omega
    push_cast [hn] at hpred
    linarith

theorem reset_cut_lower : Jst + 2 * period T ≤ resetCutTime T L Jst := by
  have ha := reset_rG_after T L Jst
  rw [d6_action_period T L] at ha
  rw [reset_cut, d6_action_period T L]
  push_cast
  linarith

theorem reset_cut_upper (hstart : 0 ≤ Jst) :
    resetCutTime T L Jst < Jst + 3 * period T := by
  have ha := reset_first_action_upper T L Jst hstart
  rw [d6_action_period T L] at ha
  rw [reset_cut, d6_action_period T L]
  push_cast
  linarith

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGObservationReads R)
variable (entry : Wire → Option (Height × BlockId))

theorem reset_frontier :
    resetCutFrontier R E rho T L Jst = honestFrontier R E rho (resetCutTime T L Jst) := rfl

/-- The time read includes all simultaneous ticks, deliveries, and restarts. -/
theorem reset_inclusive_frontier (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    honestFrontier R E rho t = frontierAtIdx R E rho (timeIdx rho t) := by
  unfold honestFrontier frontierAtIdx timeIdx
  rw [V2.D.Engine.readAt_eq_stateBefore hs t]

omit [DecidableEq V] in
/-- The cut has a last same-time event exactly when that time occurs in the run. -/
theorem reset_inclusive_start_iff (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    (∃ start ev, rho.events[start]? = some ev ∧ ev.time = t ∧
      timeIdx rho t = start + 1) ↔ ∃ ev ∈ rho.events, ev.time = t := by
  constructor
  · rintro ⟨start, ev, he, ht, _⟩
    exact ⟨ev, List.mem_of_getElem? he, ht⟩
  · rintro ⟨ev, hev, ht⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hev
    have hjn : j < timeIdx rho t :=
      (V2.D.Engine.index_lt_read_length_iff hs t hj).mpr ht.le
    have hn : timeIdx rho t ≤ rho.events.length := List.length_filter_le _ _
    have hslt : timeIdx rho t - 1 < rho.events.length := by omega
    have hlast := List.getElem?_eq_getElem hslt
    let last := rho.events[timeIdx rho t - 1]
    have hle : last.time ≤ t :=
      (V2.D.Engine.index_lt_read_length_iff hs t hlast).mp
        (show timeIdx rho t - 1 < timeIdx rho t by omega)
    have hge : t ≤ last.time := by
      by_cases heq : j = timeIdx rho t - 1
      · subst j
        have he : ev = last := Option.some.inj (hj.symm.trans hlast)
        exact ht ▸ he ▸ le_rfl
      · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
        have hk := (List.pairwise_iff_getElem.mp hs.sorted) j
          (timeIdx rho t - 1) hjl hslt (by omega)
        rw [hje] at hk
        exact ht ▸ V2.D.Engine.time_le_of_key_le _ _ hk
    exact ⟨timeIdx rho t - 1, last, hlast, le_antisymm hle hge, by omega⟩

/-- Source membership and the b2 store bound apply at the actual inclusive time cut. -/
theorem reset_row_cap (CL : FGCoreLaws R) (K : FGTreeKeepLaws R)
    (storeInv : ∀ i x, FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j x r a h e}, HonestRowAt S E rho T j x r a →
      entry a = some (h, e) → ∃ C,
        actionSourceFG R E rho T x r = some (some C) ∧ h = (O.height C).h)
    {j r h : Nat} {y : V} {a : Wire} {e : BlockId} {t u : Time}
    (ha : HonestRowAt S E rho T j y r a) (hj : rho.events[j]? = some (.tick y t))
    (htu : t ≤ u) (he : entry a = some (h, e)) : h ≤ honestFrontier R E rho u := by
  obtain ⟨C, hC, hh⟩ := emittedName ha he
  obtain ⟨nd, hnd, hsource⟩ := Option.map_eq_some_iff.mp hC
  obtain ⟨i, hi, hclock⟩ := postClock_tick E rho hnd
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ha.2.1
  have hij : i = j := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hie, hje])
  subst i
  have hheld : C ∈ TFAt R E rho j y := by
    have hm := CL.source_mem nd C hsource
    rw [← hclock, CL.clock_fg] at hm
    exact hm
  have hidx : j ≤ timeIdx rho u :=
    (V2.D.Engine.index_lt_read_length_iff hs u hj).mpr htu |>.le
  have hcut := tf_cumulative_all R E rho CL K hidx y hheld
  have hheight := store_height_le O.height O.finality _ (storeInv (timeIdx rho u) y) hcut
  rw [reset_inclusive_frontier R E rho hs u]
  exact hh.trans_le (hheight.trans (Finset.le_sup
    (f := fun x => (R.core (V2.D.Run.stateBefore E rho (timeIdx rho u) x)).fg.h_max) ha.1))

omit [DecidableEq V] in
/-- An old row acts five deltas after its vote and strictly before the cut. -/
theorem reset_old_row_before_cut {r : Nat}
    (hold : T.vote (r * T.roundSlots) < Jst) : T.action r < resetCutTime T L Jst := by
  have ht : T.action r = T.vote (r * T.roundSlots) + 5 * T.delta := by
    rw [L.action_eq, L.gate_eq, L.vote_eq]
    ring
  rw [ht]
  have hp := reset_period_lower T L
  have hc := reset_cut_lower T L Jst
  linarith [L.delta_pos]

/-- All old-row heights are bounded, also when the honest set is empty. -/
theorem reset_old_height_sup_le (CL : FGCoreLaws R) (K : FGTreeKeepLaws R)
    (storeInv : ∀ i x, FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j x r a h e}, HonestRowAt S E rho T j x r a →
      entry a = some (h, e) → ∃ C,
        actionSourceFG R E rho T x r = some (some C) ∧ h = (O.height C).h) :
    sSup (oldRowHeights S E rho T entry Jst) ≤ resetCutFrontier R E rho T L Jst := by
  apply csSup_le'
  rintro h ⟨j, y, r, a, e, ha, he, hold⟩
  exact reset_row_cap T R S E rho O entry CL K storeInv hs emittedName ha ha.2.1
    (reset_old_row_before_cut T L Jst hold).le he

/-- Height one needs an honest holder. Schedule alone does not supply one. -/
theorem reset_mu_le_iff (Ef : Electorate (Fin n)) (HL : FGHeightLaws Ef O.height)
    (CL : FGCoreLaws R) (K : FGTreeKeepLaws R)
    (storeInv : ∀ i x, FGStoreInvariant O.height O.finality
      (R.core (V2.D.Run.stateBefore E rho i x)).fg)
    (hs : V2.D.ScheduleWellFormed E rho)
    (emittedName : ∀ {j x r a h e}, HonestRowAt S E rho T j x r a →
      entry a = some (h, e) → ∃ C,
        actionSourceFG R E rho T x r = some (some C) ∧ h = (O.height C).h) :
    muOf S E rho T entry Jst ≤ resetCutFrontier R E rho T L Jst ↔ rho.honest.Nonempty := by
  constructor
  · intro h
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hm : resetCutFrontier R E rho T L Jst = 0 := by
      unfold resetCutFrontier honestFrontier
      rw [he]
      exact Finset.sup_empty
    have h1 : 1 ≤ muOf S E rho T entry Jst := Nat.le_max_left _ _
    omega
  · rintro ⟨x, hx⟩
    unfold muOf
    apply max_le
    · rw [reset_frontier, reset_inclusive_frontier R E rho hs]
      have hg := (storeInv (timeIdx rho (resetCutTime T L Jst)) x).gen
      exact (HL.one_le_h .genesis).trans
        ((store_height_le O.height O.finality _
          (storeInv (timeIdx rho (resetCutTime T L Jst)) x) hg).trans
          (Finset.le_sup (f := fun x =>
            (R.core (V2.D.Run.stateBefore E rho (timeIdx rho (resetCutTime T L Jst)) x)).fg.h_max)
            hx))
    · exact reset_old_height_sup_le T L Jst R S E rho O entry CL K storeInv hs emittedName

end AvailableChain.FGCompose
end
