module
public import AvailableChainKit.Engine.Execution

@[expose] public section
namespace AvailableChain.Engine

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Local clock laws shared by the Grid CO, SA, and SA-PC engines. -/
structure ClockLaws {n : Nat} (P : ProtocolSpec n) where
  now : P.State → Time
  init : now P.init = 0
  clock : ∀ st t, now (P.clock st t) = t
  process : ∀ st o, now (P.process st o) = now st

private theorem key_time_le {V O : Type} (e f : Event V O)
    (h : e.key ≤ f.key) : e.time ≤ f.time := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- A stored clock value is zero or comes from an earlier local tick. -/
theorem stateBefore_now_source {V : Type} [DecidableEq V]
    {n : Nat} {P : ProtocolSpec n} (C : ClockLaws P)
    (rho : Run V P) (i : Nat) (v : V) :
    C.now (Run.stateBefore P rho i v) = 0 ∨
      ∃ j < i, rho.events[j]? =
        some (.tick v (C.now (Run.stateBefore P rho i v))) := by
  induction i with
  | zero => exact Or.inl C.init
  | succ i ih =>
      cases hi : rho.events[i]? with
      | none =>
          have he : Run.stateBefore P rho (i + 1) =
              Run.stateBefore P rho i := by
            simp [Run.stateBefore, List.take_add_one, hi]
          rw [he]
          exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick u t =>
              by_cases hv : v = u
              · subst u
                simp only [World.step, Function.update_self]
                right
                exact ⟨i, by omega, by simpa [C.clock] using hi⟩
              · simp only [World.step, Function.update_of_ne hv]
                exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)
          | deliver u o t =>
              by_cases hv : v = u
              · subst u
                simp only [World.step, Function.update_self]
                simp only [C.process]
                exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)
              · simp only [World.step, Function.update_of_ne hv]
                exact ih.imp_right (fun ⟨j, hj, he⟩ => ⟨j, by omega, he⟩)

/-- No reader's clock can exceed the next event time. -/
theorem stateBefore_now_le_event {V : Type} [DecidableEq V]
    {n : Nat} {P : ProtocolSpec n} (C : ClockLaws P)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object}
    (hi : rho.events[i]? = some e) (v : V) :
    C.now (Run.stateBefore P rho i v) ≤ e.time := by
  rcases stateBefore_now_source C rho i v with hz | ⟨j, hj, ht⟩
  · rw [hz]
    exact (hs.in_horizon e (List.mem_of_getElem? hi)).1
  · obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ht
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hj
    rw [hje, hie] at hk
    exact key_time_le _ _ hk

/-- Local clock values increase along a valid event list. -/
theorem stateBefore_now_mono {V : Type} [DecidableEq V]
    {n : Nat} {P : ProtocolSpec n} (C : ClockLaws P)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    {i j : Nat} (hij : i ≤ j) (v : V) :
    C.now (Run.stateBefore P rho i v) ≤
      C.now (Run.stateBefore P rho j v) := by
  induction j with
  | zero => simp [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with he | hlt
      · subst i; exact le_refl _
      · apply le_trans (ih (by omega))
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step, C.clock] using!
                    stateBefore_now_le_event C E rho hs hj v
                · simp [World.step, hv]
            | deliver u o t =>
                by_cases hv : v = u
                · subst u; simp [World.step, C.process]
                · simp [World.step, hv]

/-- A local tick at or before a delivery precedes that delivery in the list.
This includes equal times, because ticks have the earlier event phase. -/
theorem tick_index_lt_delivery {V : Type} {n : Nat} {P : ProtocolSpec n}
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    {i j : Nat} {v w : V} {o : P.Object} {a t : Time}
    (hi : rho.events[i]? = some (.tick v a))
    (hj : rho.events[j]? = some (.deliver w o t)) (hat : a ≤ t) : i < j := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  by_contra hn
  rcases Nat.lt_or_ge j i with hji | hij
  · have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    have hbad : t < a := by
      simpa [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] using hk
    exact (not_lt.mpr hat) hbad
  · have he : i = j := by omega
    subst j
    simp [hi] at hj

/-- A delivery after a required local public tick has a clock at least
that tick time, including for a sleeping reader. -/
theorem delivery_now_ge_public {V : Type} [DecidableEq V]
    {n : Nat} {P : ProtocolSpec n} (C : ClockLaws P)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {o : P.Object} {a t : Time}
    (hi : rho.events[i]? = some (.deliver v o t))
    (ha : PublicTime E a) (ha0 : 0 ≤ a) (hat : a ≤ t) :
    a ≤ C.now (Run.stateBefore P rho i v) := by
  have hm := List.mem_of_getElem? hi
  have hv := hs.honest_only _ hm
  have ht := (hs.in_horizon _ hm).2
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
    (hs.tick_total v hv a ha ha0 (hat.trans ht))
  have hji := tick_index_lt_delivery E rho hs hj hi hat
  have hb := stateBefore_now_mono C E rho hs (Nat.succ_le_of_lt hji) v
  rw [stateBefore_succ_event hj] at hb
  simpa [World.step, C.clock] using hb

/-- A local invariant can use the fact that a valid clock tick never
moves backwards. Receipt preservation needs no extra time premise. -/
theorem stateBefore_invariant {V : Type} [DecidableEq V]
    {n : Nat} {P : ProtocolSpec n} (C : ClockLaws P)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (Q : P.State → Prop) (hinit : Q P.init)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o)) (i : Nat) (v : V) :
    Q (Run.stateBefore P rho i v) := by
  induction i with
  | zero => exact hinit
  | succ i ih =>
      cases hi : rho.events[i]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick u t =>
              by_cases hv : v = u
              · subst u
                simpa only [World.step, Function.update_self] using
                  hclock _ t (stateBefore_now_le_event C E rho hs hi v) ih
              · simpa [World.step, hv] using ih
          | deliver u o t =>
              by_cases hv : v = u
              · subst u
                simpa only [World.step, Function.update_self] using hprocess _ o ih
              · simpa [World.step, hv] using ih

/-- A state property that `process` keeps, and that `clock` keeps when the
tick does not move backwards, holds for the rest of a valid run. This is
the run-indexed form of `stateBefore_stable`. -/
theorem stateBefore_stable_clock {V : Type} [DecidableEq V]
    {n : Nat} {P : ProtocolSpec n} (C : ClockLaws P)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (Q : P.State → Prop)
    (hclock : ∀ st t, C.now st ≤ t → Q st → Q (P.clock st t))
    (hprocess : ∀ st o, Q st → Q (P.process st o))
    {i j : Nat} (hij : i ≤ j) (v : V)
    (hi : Q (Run.stateBefore P rho i v)) : Q (Run.stateBefore P rho j v) := by
  induction j with
  | zero => rwa [Nat.le_zero.mp hij] at hi
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact hi
      · have hj := ih (by omega)
        cases he : rho.events[j]? with
        | none => simpa [Run.stateBefore, List.take_add_one, he] using hj
        | some e =>
            rw [stateBefore_succ_event he]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  simpa only [World.step, Function.update_self] using
                    hclock _ t (stateBefore_now_le_event C E rho hs he v) hj
                · simpa [World.step, hv] using hj
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa only [World.step, Function.update_self] using hprocess _ o hj
                · simpa [World.step, hv] using hj

/-- A stored row whose only source is a local clock has a prior tick
with that source property. This includes immutable saves and freezes. -/
theorem clock_field_origin {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {α : Type} (field : P.State → List α) (hinit : field P.init = [])
    (hprocess : ∀ st o, field (P.process st o) = field st)
    (Q : P.State → Time → α → Prop)
    (hclock : ∀ st t row, row ∈ field (P.clock st t) → row ∈ field st ∨ Q st t row)
    (rho : Run V P) (index : Nat) (v : V) (row : α)
    (hm : row ∈ field (Run.stateBefore P rho index v)) :
    ∃ j < index, ∃ t, rho.events[j]? = some (.tick v t) ∧
      Q (Run.stateBefore P rho j v) t row := by
  induction index with
  | zero => simp only [Run.stateBefore, List.take_zero, List.foldl_nil, World.init,
      hinit, List.not_mem_nil] at hm
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none =>
          have hold : row ∈ field (Run.stateBefore P rho index v) := by
            simpa [Run.stateBefore, List.take_add_one, hi] using hm
          obtain ⟨j, hj, rest⟩ := ih hold
          exact ⟨j, by omega, rest⟩
      | some e =>
          rw [stateBefore_succ_event hi] at hm
          cases e with
          | tick u t =>
              by_cases hv : v = u
              · subst u
                rcases hclock (Run.stateBefore P rho index v) t row
                    (by simpa only [World.step, Function.update_self] using hm) with hold | hnew
                · obtain ⟨j, hj, rest⟩ := ih hold
                  exact ⟨j, by omega, rest⟩
                · exact ⟨index, by omega, t, hi, hnew⟩
              · obtain ⟨j, hj, rest⟩ := ih (by simpa [World.step, hv] using hm)
                exact ⟨j, by omega, rest⟩
          | deliver u o t =>
              have hold : row ∈ field (Run.stateBefore P rho index v) := by
                by_cases hv : v = u
                · subst u; simpa [World.step, hprocess] using hm
                · simpa [World.step, hv] using hm
              obtain ⟨j, hj, rest⟩ := ih hold
              exact ⟨j, by omega, rest⟩

/-- A field that only grows by append retains its first matching row. -/
theorem stateBefore_field_prefix {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {α : Type} (field : P.State → List α)
    (hclock : ∀ st t, field st <+: field (P.clock st t))
    (hprocess : ∀ st o, field st <+: field (P.process st o))
    (rho : Run V P) {i j : Nat} (hij : i ≤ j) (v : V) :
    field (Run.stateBefore P rho i v) <+: field (Run.stateBefore P rho j v) := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact List.prefix_refl _
      · apply (ih (by omega)).trans
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  simpa only [World.step, Function.update_self] using
                    hclock (Run.stateBefore P rho j v) t
                · simp [World.step, hv]
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa only [World.step, Function.update_self] using
                    hprocess (Run.stateBefore P rho j v) o
                · simp [World.step, hv]

end AvailableChain.Engine
end
