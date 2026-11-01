module
public import AvailableChainGridCO.Proofs.History
public import AvailableChainKit.Engine.Execution

@[expose] public section

namespace AvailableChain.GridCO

set_option linter.unusedSectionVars false
variable [LeasePolicy]
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

section Schedule
variable {V : Type} [DecidableEq V] {p : Params} {E : Env V}
  {rho : Run V (gridCO p)}

-- Retain the established Grid CO and SA proof interface.
theorem stateBefore_succ_event {i : Nat} {e : Event V (gridCO p).Object}
    (hi : rho.events[i]? = some e) :
    Run.stateBefore (gridCO p) rho (i + 1) =
      World.step (Run.stateBefore (gridCO p) rho i) e :=
  Engine.stateBefore_succ_event hi

omit [DecidableEq V] in
theorem eventIndex_lt_of_time_lt (hs : ScheduleWellFormed E rho)
    {i j : Nat} {e f : Event V (gridCO p).Object}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some f)
    (ht : e.time < f.time) : i < j :=
  Engine.eventIndex_lt_of_time_lt hs hi hj ht

theorem readAt_eq_stateBefore (hs : ScheduleWellFormed E rho) (t : Time) :
    Run.readAt (gridCO p) rho t = Run.stateBefore (gridCO p) rho
      (rho.events.filter (fun e => decide (e.time ≤ t))).length :=
  Engine.readAt_eq_stateBefore hs t

omit [DecidableEq V] in
theorem index_lt_read_length_iff (hs : ScheduleWellFormed E rho)
    (t : Time) {i : Nat} {e : Event V (gridCO p).Object}
    (hi : rho.events[i]? = some e) :
    i < (rho.events.filter (fun f => decide (f.time ≤ t))).length ↔ e.time ≤ t :=
  Engine.index_lt_read_length_iff hs t hi

omit [DecidableEq V] in
theorem read_length_mono (a b : Time) (hab : a ≤ b) :
    (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ b))).length :=
  Engine.read_length_mono a b hab

theorem stateBefore_eq_of_other_nodes (v : V) {m : Nat} (n : Nat) (hm : m ≤ n)
    (h : ∀ j e, m ≤ j → j < n → rho.events[j]? = some e → e.node ≠ v) :
    Run.stateBefore (gridCO p) rho n v = Run.stateBefore (gridCO p) rho m v :=
  Engine.stateBefore_eq_of_other_nodes v n hm h

theorem stateBefore_tick_eq_stateBeforeTime (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    Run.stateBefore (gridCO p) rho i v = Run.stateBeforeTime (gridCO p) rho t v :=
  Engine.stateBefore_tick_eq_stateBeforeTime hs hi

/-- The public-time record equals its value just after the unique local
clock tick; equal-time deliveries leave that record unchanged. -/
theorem read_stable_eq_clock (hs : ScheduleWellFormed E rho)
    {v : V} {t : Time} (htick : Event.tick v t ∈ rho.events) :
    stable (Run.readAt (gridCO p) rho t v) =
      stable (clock p (Run.stateBeforeTime (gridCO p) rho t v) t) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  have hprefix : rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time ≤ t))).length :=
    filter_eq_take hs _ (by
      intro e f hk hf
      exact decide_eq_true (le_trans (time_le_of_key_le _ _ hk) (of_decide_eq_true hf)))
  let k := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hik : i < k := by
    by_contra hc
    have hf := filter_false_of_index_ge hs (fun e => decide (e.time ≤ t))
      (by
        intro e f hk hf
        exact decide_eq_true (le_trans (time_le_of_key_le _ _ hk) (of_decide_eq_true hf)))
      (show k ≤ i by omega) hi
    simp [Event.time] at hf
  have hstep : Run.stateBefore (gridCO p) rho (i + 1) v =
      clock p (Run.stateBeforeTime (gridCO p) rho t v) t := by
    unfold Run.stateBefore
    rw [List.take_add_one, List.foldl_append, hi]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil, World.step,
      Function.update_self]
    exact congrArg (fun st => clock p st t) (stateBefore_tick_eq_stateBeforeTime hs hi)
  have hstay : ∀ j, i + 1 ≤ j → j ≤ k →
      (Run.stateBefore (gridCO p) rho j v).stableRecord =
        (Run.stateBefore (gridCO p) rho (i + 1) v).stableRecord := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
        intro hj hjk
        by_cases hij : i + 1 ≤ j
        · rw [← ih hij (by omega)]
          unfold Run.stateBefore
          rw [List.take_add_one, List.foldl_append]
          cases he : rho.events[j]? with
          | none => simp
          | some e =>
              simp only [Option.toList, List.foldl_cons, List.foldl_nil]
              cases e with
              | deliver u o t' =>
                  by_cases hv : v = u
                  · subst v; simpa [World.step] using! process_stable p _ o
                  · simp [World.step, hv]
              | tick u t' =>
                  have hne : u ≠ v := by
                    intro huv
                    subst u
                    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
                    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
                    have hk : (Event.tick v t : Event V (gridCO p).Object).key ≤
                        (Event.tick v t' : Event V (gridCO p).Object).key := by
                      simpa [hie, hje] using
                        (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl (by omega)
                    have hlow := time_le_of_key_le _ _ hk
                    have hm : Event.tick v t' ∈
                        rho.events.filter (fun e => decide (e.time ≤ t)) := by
                      rw [hprefix]
                      exact List.mem_of_getElem? (by
                        rw [List.getElem?_take_of_lt (show j < k by omega)]
                        exact he)
                    have hu := of_decide_eq_true (List.mem_filter.mp hm).2
                    have htt : t' = t := le_antisymm hu hlow
                    have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, htt])
                    omega
                  simp [World.step, Ne.symm hne]
        · have : j + 1 = i + 1 := by omega
          rw [this]
  change ((rho.events.filter _).foldl World.step World.init v).stableRecord = _
  rw [hprefix]
  exact (hstay k (by omega) (le_refl _)).trans (congrArg State.stableRecord hstep)

end Schedule
end AvailableChain.GridCO
end
