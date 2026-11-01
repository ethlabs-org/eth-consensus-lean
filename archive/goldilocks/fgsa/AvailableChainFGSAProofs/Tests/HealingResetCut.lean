module
public import AvailableChainFGSAProofs.Proofs.Healing.ResetCut -- shake: keep (RS-0 tests)
public import AvailableChainFGSAProofs.Proofs.Foundations.Sources -- shake: keep (INLINE producer)

set_option linter.privateModule false

public section

/-! S5 RS-0 C5. Test GST on the action grid and between actions, R = 2
and R = 3, all simultaneous ticks, the closed row cap, and both STOP gaps.
The Foundations input is discharged by its named producer. No reset row
or reset arrival witness is constructed. -/

namespace AvailableChain.FGSA.Run.Tests.HealingResetCut
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

-- GST exactly on an action: the first round is that round, and the lower
-- cut bound is attained. This also tests rG = 0.
example (r : Nat) (hGST : recoveryStart p E = p.actionTime r) :
    resetFirstRound p E = r ∧ resetCutTime p E = recoveryStart p E + 2 * P p := by
  have hr : resetFirstRound p E = r := by
    apply le_antisymm
    · exact reset_rG_first p E r (by rw [hGST])
    · have ha := reset_rG_after p E
      rw [hGST, actionTime_periodW, actionTime_periodW] at ha
      have hp : 0 < P p := by
        have h := reset_period_lower p
        linarith [p.deltaPos]
      have hh : (r : Time) ≤ resetFirstRound p E := by nlinarith
      exact_mod_cast hh
  refine ⟨hr, ?_⟩
  rw [reset_cut, hr, hGST, actionTime_periodW, actionTime_periodW]
  push_cast
  ring

-- GST strictly between consecutive actions: the next round is selected.
example (r : Nat) (hlo : p.actionTime r < recoveryStart p E)
    (hhi : recoveryStart p E < p.actionTime (r + 1)) : resetFirstRound p E = r + 1 := by
  have hu := reset_rG_first p E (r + 1) hhi.le
  have ha := reset_rG_after p E
  rw [actionTime_periodW] at ha hlo
  have hp : 0 < P p := by
    have h := reset_period_lower p
    linarith [p.deltaPos]
  have hl : (r : Time) < resetFirstRound p E := by nlinarith
  have hl' : r < resetFirstRound p E := by exact_mod_cast hl
  omega

-- R = 2 gives P = 8Δ. At Δ = 1 and GST = 10 the cut bounds are [34, 42).
example (hR : p.R = 2) (hΔ : p.Δ = 1) (hGST : E.t_GST = 10) :
    34 ≤ resetCutTime p E ∧ resetCutTime p E < 42 := by
  have hp : P p = 8 := by simp [P, hR, hΔ]
  have hl := reset_cut_lower p E
  have hu := reset_cut_upper p E
  norm_num [recoveryStart, tauC, firstUpdateLabel, slotStartZ, hGST, hp, hΔ] at hl hu
  exact ⟨hl, hu⟩

-- R = 3 gives P = 12Δ. At Δ = 1 and GST = 10 the cut bounds are [42, 54).
example (hR : p.R = 3) (hΔ : p.Δ = 1) (hGST : E.t_GST = 10) :
    42 ≤ resetCutTime p E ∧ resetCutTime p E < 54 := by
  have hp : P p = 12 := by simp [P, hR, hΔ]
  have hl := reset_cut_lower p E
  have hu := reset_cut_upper p E
  norm_num [recoveryStart, tauC, firstUpdateLabel, slotStartZ, hGST, hp, hΔ] at hl hu
  exact ⟨hl, hu⟩

-- Two actual ticks at u₀ are both included. The last event is selected by
-- index, so the assertion also includes deliveries at the same time.
example (hs : V2.D.ScheduleWellFormed E rho) {j k : Nat} {x y : V}
    (hj : rho.events[j]? = some (.tick x (resetCutTime p E)))
    (hk : rho.events[k]? = some (.tick y (resetCutTime p E))) :
    ∃ start ev, rho.events[start]? = some ev ∧ ev.time = resetCutTime p E ∧
      timeIdx rho (resetCutTime p E) = start + 1 ∧ j ≤ start ∧ k ≤ start ∧
      resetCutFrontier p c E rho = frontierAtIdx p c E rho (start + 1) := by
  obtain ⟨start, ev, he, ht, hi⟩ :=
    (reset_inclusive_start_iff p c E rho hs (resetCutTime p E)).mpr
      ⟨_, List.mem_of_getElem? hj, rfl⟩
  have hjlt := (V2.D.Engine.index_lt_read_length_iff hs (resetCutTime p E) hj).mpr le_rfl
  have hklt := (V2.D.Engine.index_lt_read_length_iff hs (resetCutTime p E) hk).mpr le_rfl
  change j < timeIdx rho (resetCutTime p E) at hjlt
  change k < timeIdx rho (resetCutTime p E) at hklt
  refine ⟨start, ev, he, ht, hi, by omega, by omega, ?_⟩
  rw [reset_frontier, reset_inclusive_frontier p c E rho hs, hi]

-- C2 has the frozen rowCap binders, including equality at the cut.
example (hs : V2.D.ScheduleWellFormed E rho) :
    ∀ j y r a h e t, HonestRowAt p c E rho j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ resetCutTime p E →
      namedEntry a.payload.height_pair = some (h, e) → h ≤ resetCutFrontier p c E rho := by
  intro j y r a h e t ha hj ht he
  rw [reset_frontier]
  exact reset_row_cap p c E rho hs (emittedName_window p c E rho hs) ha hj ht he

-- C3 isolates the exact missing fact. No extra assumption closes the item.
example (hs : V2.D.ScheduleWellFormed E rho) :
    muOf p c E rho ≤ resetCutFrontier p c E rho ↔ rho.honest.Nonempty :=
  reset_mu_le_iff p c E rho hs (emittedName_window p c E rho hs)

-- The supplied schedule and execution conditions permit this empty run.
private def emptyRun (x : V) : V2.D.Run V (fgsa p c) where
  honest := ∅
  horizon := 0
  events := []
  seatOf := fun _ _ => x
  input := rho.input

private theorem empty_valid (x : V) : V2.D.ExecutionValid E (emptyRun p c rho x) where
  horizon_nonneg := le_rfl
  sorted := by simp [emptyRun]
  nodup := List.nodup_nil
  in_horizon := by simp [emptyRun]
  honest_only := by simp [emptyRun]
  tick_awake := by simp [emptyRun]
  deliver_awake := by simp [emptyRun]
  restart_awake := by simp [emptyRun]
  wake_restart := by simp [emptyRun]
  tick_public := by simp [emptyRun]
  tick_total := by simp [emptyRun]
  wire := by simp [emptyRun]
  deps := by simp [emptyRun]
  fresh := by simp [emptyRun]
  unforgeable := by simp [V2.D.Run.processes, emptyRun]
  carried := by simp [V2.D.Run.processes, emptyRun]

example (x : V) : V2.D.ExecutionValid E (emptyRun p c rho x) ∧
    V2.D.NoRestart (emptyRun p c rho x) ∧ RMono p c E (emptyRun p c rho x) := by
  refine ⟨empty_valid p c E rho x, ?_, ?_⟩
  · simp [V2.D.NoRestart, emptyRun]
  · simp [RMono, emptyRun]

-- C1 STOP: no index start can have timeIdx u₀ = start + 1 in this run.
example (x : V) :
    ¬ ∃ start, timeIdx (emptyRun p c rho x) (resetCutTime p E) = start + 1 := by
  simp [timeIdx, emptyRun]

-- C3 STOP: the frozen μ is one and the frozen M is zero in this run.
example (x : V) : muOf p c E (emptyRun p c rho x) = 1 ∧
    resetCutFrontier p c E (emptyRun p c rho x) = 0 := by
  have he : oldRowHeights p c E (emptyRun p c rho x) = ∅ := by
    ext h
    simp [oldRowHeights, HonestRowAt, emptyRun]
  constructor
  · rw [muOf_def, he, csSup_empty]
    rfl
  · rw [reset_frontier]
    simp [honestFrontier, emptyRun]

-- C1 also fails with an honest node: this valid run ends at time zero.
private def shortRun (x : V) : V2.D.Run V (fgsa p c) where
  honest := {x}
  horizon := 0
  events := [.tick x 0]
  seatOf := fun _ _ => x
  input := rho.input

omit [DecidableEq V] in
private theorem short_no_delivery (x : V) {i : Nat} {v : V} {o : Obj p} {t : Time} :
    (shortRun p c rho x).events[i]? ≠ some (.deliver v o t) := by
  intro hi
  have hm := List.mem_of_getElem? hi
  simp [shortRun] at hm

private theorem short_valid (x : V) (hawake : E.awake x 0 = true) :
    V2.D.ExecutionValid E (shortRun p c rho x) where
  horizon_nonneg := le_rfl
  sorted := by simp [shortRun]
  nodup := by simp [shortRun]
  in_horizon := by simp [shortRun, V2.Event.time]
  honest_only := by simp [shortRun, V2.Event.node]
  tick_awake := by
    intro v t h
    have he : v = x ∧ t = 0 := by simpa [shortRun] using h
    simpa only [he.1, he.2] using hawake
  deliver_awake := by simp [shortRun]
  restart_awake := by simp [shortRun]
  wake_restart := by
    intro v hv t ht hh _
    change t ≤ 0 at hh
    exact ((not_lt.mpr hh) ht).elim
  tick_public := by
    intro v t h
    have ht : t = 0 := by simpa only [V2.Event.time] using (congrArg V2.Event.time
      (show (.tick v t : V2.Event V (Obj p)) = .tick x 0 by simpa [shortRun] using h))
    exact ⟨0, by simp [ht]⟩
  tick_total := by
    intro v hv t _ hn hh
    have hvx : v = x := by simpa [shortRun] using hv
    have ht : t = 0 := le_antisymm hh hn
    simp [shortRun, hvx, ht]
  wire := by intro i v o t hi; exact (short_no_delivery p c rho x hi).elim
  deps := by intro i v o t hi; exact (short_no_delivery p c rho x hi).elim
  fresh := by intro i v o t hi; exact (short_no_delivery p c rho x hi).elim
  unforgeable := by
    rintro v o t ⟨i, hi⟩
    exact (short_no_delivery p c rho x hi).elim
  carried := by
    rintro v o t ⟨i, hi⟩
    exact (short_no_delivery p c rho x hi).elim

example (x : V) (hawake : E.awake x 0 = true) : V2.D.ExecutionValid E (shortRun p c rho x) ∧
    (shortRun p c rho x).honest.Nonempty ∧
    ¬ ∃ ev ∈ (shortRun p c rho x).events, ev.time = resetCutTime p E := by
  have hcut : 0 < resetCutTime p E := by
    have hl := reset_cut_lower p E
    have hp := reset_period_lower p
    linarith [p.deltaPos, E.t_GST_nonneg, healing_recovery_start_lower (p := p) E]
  refine ⟨short_valid p c E rho x hawake, by simp [shortRun], ?_⟩
  simpa [shortRun, V2.Event.time] using (ne_of_gt hcut).symm

-- A run that ends before u₀ cannot supply the frozen start event,
-- regardless of how many honest nodes it has.
example (hs : V2.D.ScheduleWellFormed E rho) (hEnd : rho.horizon < resetCutTime p E) :
    ¬ ∃ start ev, rho.events[start]? = some ev ∧ ev.time = resetCutTime p E ∧
      timeIdx rho (resetCutTime p E) = start + 1 := by
  intro h
  obtain ⟨ev, hm, ht⟩ := (reset_inclusive_start_iff p c E rho hs (resetCutTime p E)).mp h
  have he := (hs.in_horizon ev hm).2
  rw [ht] at he
  exact (not_le.mpr hEnd) he

end AvailableChain.FGSA.Run.Tests.HealingResetCut
end
