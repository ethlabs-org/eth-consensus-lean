module
public import AvailableChainPCSAProofs.Proofs.Outage.ArmSources
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

/-! Schedule facts of the persistence induction (pcsa34-r4.3 §1.2, §5.4.1):
slot-time order, ticks of honest nodes at public times, and the stores read
at a tick, after the ticks of a time, and at a time. -/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-! ### Slot times -/

/-- An early time at or before a vote time is of an earlier slot. -/
theorem pcsa_early_le_vote_lt (j' j : Slot)
    (h : SA.earlyTime p.toParams j' ≤ SA.voteTime p.toParams j) : j' < j := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (j' : Int) + 2 * p.Δ ≤ 4 * p.Δ * (j : Int) + p.Δ at h
  by_contra hn
  have hj : (j : Int) ≤ j' := by exact_mod_cast Nat.le_of_not_lt hn
  nlinarith

/-- The freeze of the previous slot is before the vote time. -/
theorem pcsa_freeze_pred_lt_vote (j : Slot) (hj : 0 < j) :
    SA.freezeTime p.toParams (j - 1) < SA.voteTime p.toParams j := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, (Nat.sub_add_cancel hj).symm⟩
  rw [Nat.add_sub_cancel]
  change 4 * p.Δ * (j' : Int) + 3 * p.Δ < 4 * p.Δ * ((j' + 1 : Nat) : Int) + p.Δ
  push_cast
  nlinarith

/-- Freeze times increase with the slot. -/
theorem pcsa_freeze_mono {a b : Slot} (h : a ≤ b) :
    SA.freezeTime p.toParams a ≤ SA.freezeTime p.toParams b := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 4 * p.Δ * (a : Int) + 3 * p.Δ ≤ 4 * p.Δ * (b : Int) + 3 * p.Δ
  have : (a : Int) ≤ b := by exact_mod_cast h
  nlinarith

/-- Freeze times are positive. -/
theorem pcsa_freeze_pos (s : Slot) : 0 < SA.freezeTime p.toParams s := by
  have hΔ : (0 : Int) < p.Δ := p.deltaPos
  change 0 < 4 * p.Δ * (s : Int) + 3 * p.Δ
  positivity

omit [DecidableEq V] in
/-- A freeze time is public. -/
theorem pcsa_freeze_public (E : Generic.Env V) (hΔ : E.Δ = p.Δ) (s : Slot) :
    V2.PublicTime E (SA.freezeTime p.toParams s) := by
  refine ⟨4 * s + 3, ?_⟩
  rw [hΔ]
  change 4 * p.Δ * (s : Int) + 3 * p.Δ = ((4 * s + 3 : Nat) : Int) * p.Δ
  push_cast
  ring

/-! ### Ticks -/

omit [DecidableEq V] in
/-- An honest node ticks at every public time in the run. -/
theorem pcsa_tick_exists (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (y : V) (hy : y ∈ rho.honest) (t : Time)
    (hp : V2.PublicTime E t) (h0 : 0 ≤ t) (hh : t ≤ rho.horizon) :
    ∃ k : Nat, rho.events[k]? = some (V2.Event.tick y t) :=
  List.mem_iff_getElem?.mp (hs.tick_total y hy t hp h0 hh)

omit [DecidableEq V] in
/-- A tick event is in the horizon. -/
theorem pcsa_tick_le_horizon (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) : t ≤ rho.horizon :=
  (hs.in_horizon _ (List.mem_of_getElem? hk)).2

omit [DecidableEq V] in
/-- An event of an earlier time has an earlier index. -/
theorem pcsa_index_lt_of_time_lt (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k k' : Nat} {e e' : V2.Event V (Obj p)}
    (hk : rho.events[k]? = some e) (hk' : rho.events[k']? = some e')
    (h : e.time < e'.time) : k < k' := by
  by_contra hn
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  obtain ⟨hkl', hke'⟩ := List.getElem?_eq_some_iff.mp hk'
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hn) with hlt | heq
  · have hkey := (List.pairwise_iff_getElem.mp hs.sorted) k' k hkl' hkl hlt
    rw [hke', hke] at hkey
    exact absurd (V2.D.Engine.time_le_of_key_le _ _ hkey) (not_le.mpr h)
  · subst heq
    rw [hk] at hk'
    cases Option.some.inj hk'
    exact lt_irrefl _ h

/-! ### Stores -/

/-- The store after the ticks of `t` is the clock at the node's tick. -/
theorem pcsa_storeAfterTicks_tick (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) {k : Nat} {y : V} {t : Time}
    (hk : rho.events[k]? = some (.tick y t)) :
    storeAfterTicks p c E rho y t = clock p (V2.D.Run.stateBefore E rho k y).st t ∧
      storeAfterTicks p c E rho y t = (V2.D.Run.stateBefore E rho (k + 1) y).st := by
  have h1 : storeAfterTicks p c E rho y t = (V2.D.tick E rho
      (V2.D.Run.stateBefore E rho k y) y t).1.st := by
    change (FGSA.Run.afterTicks E rho t y).st = _
    rw [FGSA.Run.afterTicks_node E rho hs hk]
  refine ⟨h1.trans (pcsa_tick_st E rho _ _ _), h1.trans ?_⟩
  rw [(V2.D.Run.step_tick_eq E rho hk).1]

/-- The store read at a time is an indexed state whose index grows with the time. -/
theorem pcsa_storeAt_index (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) (y : V) (t : Time) :
    storeAt p c E rho y t = (V2.D.Run.stateBefore E rho
      (rho.events.filter (fun e => decide (e.time ≤ t))).length y).st := by
  rw [storeAt_def, V2.D.Engine.readAt_eq_stateBefore hs]

omit [DecidableEq V] in
/-- The read index grows with the time. -/
theorem pcsa_storeAt_index_mono (rho : V2.D.Run V (pcsaWith m p c)) {t t' : Time}
    (h : t ≤ t') : (rho.events.filter (fun e => decide (e.time ≤ t))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ t'))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true ((of_decide_eq_true he).trans h)

omit [DecidableEq V] in
/-- Every event of the run is at a time at most the horizon. -/
theorem pcsa_events_le_horizon (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))
    (hs : V2.D.ScheduleWellFormed E rho) :
    ∀ (j : Nat), ∀ k < j, ∀ e, rho.events[k]? = some e → e.time ≤ rho.horizon :=
  fun _ _ _ e he => (hs.in_horizon e (List.mem_of_getElem? he)).2

end AvailableChain.PCSA.Run
end
