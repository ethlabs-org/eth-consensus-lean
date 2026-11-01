module
public import AvailableChainKit.Engine.Execution

@[expose] public section
namespace AvailableChain.Engine
open AvailableChain.Generic AvailableChain.Statements.Generic

variable {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}

/-- A finite run prefix, including every event at the cutoff. -/
def runPrefix (rho : Run V P) (cut : Time) : Run V P :=
  { rho with horizon := cut
             events := rho.events.take
               (rho.events.filter (fun e => decide (e.time ≤ cut))).length }

variable {E : Env V} {rho : Run V P}

omit [DecidableEq V] in
theorem runPrefix_events (hs : ScheduleWellFormed E rho) (cut : Time) :
    (runPrefix rho cut).events = rho.events.filter (fun e => decide (e.time ≤ cut)) := by
  exact (filter_eq_take hs _ (by
    intro a b hab hb
    have ht : a.time ≤ b.time := by
      rcases Prod.Lex.toLex_le_toLex.mp hab with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    simpa only [decide_eq_true_eq] using ht.trans (of_decide_eq_true hb))).symm

omit [DecidableEq V] in
/-- Event indices below the cutoff remain unchanged. -/
theorem runPrefix_event_iff (hs : ScheduleWellFormed E rho) (cut : Time)
    (i : Nat) (e : Event V P.Object) :
    (runPrefix rho cut).events[i]? = some e ↔
      rho.events[i]? = some e ∧ e.time ≤ cut := by
  simp only [runPrefix, List.getElem?_take]
  split
  · rename_i hi
    exact ⟨fun he => ⟨he, (index_lt_read_length_iff hs cut he).mp hi⟩,
      fun h => h.1⟩
  · rename_i hi
    constructor
    · intro h; cases h
    · intro ⟨he, ht⟩
      exact (hi ((index_lt_read_length_iff hs cut he).mpr ht)).elim

theorem runPrefix_stateBefore (cut : Time) (i : Nat)
    (hi : i ≤ (rho.events.filter (fun e => decide (e.time ≤ cut))).length) :
    Run.stateBefore P (runPrefix rho cut) i = Run.stateBefore P rho i := by
  simp only [Run.stateBefore, runPrefix, List.take_take, Nat.min_eq_left hi]

theorem runPrefix_readAt (hs : ScheduleWellFormed E rho) (cut t : Time)
    (ht : t ≤ cut) : Run.readAt P (runPrefix rho cut) t = Run.readAt P rho t := by
  simp only [Run.readAt, runPrefix_events hs, List.filter_filter]
  congr 2
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, h.trans ht⟩⟩

theorem runPrefix_stateBeforeTime (hs : ScheduleWellFormed E rho) (cut t : Time)
    (ht : t ≤ cut) :
    Run.stateBeforeTime P (runPrefix rho cut) t = Run.stateBeforeTime P rho t := by
  simp only [Run.stateBeforeTime, runPrefix_events hs, List.filter_filter]
  congr 2
  funext e
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, h.le.trans ht⟩⟩

/-- A prefix event has the same input and output as the original event. -/
theorem runPrefix_event_states (hs : ScheduleWellFormed E rho) (cut : Time)
    {i : Nat} {e : Event V P.Object}
    (he : (runPrefix rho cut).events[i]? = some e) :
    Run.stateBefore P (runPrefix rho cut) i = Run.stateBefore P rho i ∧
      Run.stateBefore P (runPrefix rho cut) (i + 1) = Run.stateBefore P rho (i + 1) := by
  obtain ⟨orig, time⟩ := (runPrefix_event_iff hs cut i e).mp he
  have hi := (index_lt_read_length_iff hs cut orig).mpr time
  exact ⟨runPrefix_stateBefore cut i hi.le,
    runPrefix_stateBefore cut (i + 1) (Nat.succ_le_of_lt hi)⟩

theorem runPrefix_emits_iff (hs : ScheduleWellFormed E rho) (cut : Time)
    (F : Env V) (v : V) (o : P.Object) (t : Time) :
    Run.emits P F (runPrefix rho cut) v o t ↔ Run.emits P F rho v o t ∧ t ≤ cut := by
  constructor
  · rintro ⟨i, he, hm⟩
    obtain ⟨orig, time⟩ := (runPrefix_event_iff hs cut i _).mp he
    have states := (runPrefix_event_states hs cut he).1
    refine ⟨⟨i, orig, ?_⟩, time⟩
    simpa only [Run.emittedAt, states] using! hm
  · rintro ⟨⟨i, orig, hm⟩, time⟩
    have he := (runPrefix_event_iff hs cut i _).mpr ⟨orig, time⟩
    refine ⟨i, he, ?_⟩
    simpa only [Run.emittedAt, (runPrefix_event_states hs cut he).1] using! hm

omit [DecidableEq V] in
theorem runPrefix_processes_iff (hs : ScheduleWellFormed E rho) (cut : Time)
    (v : V) (o : P.Object) (t : Time) :
    Run.processes P (runPrefix rho cut) v o t ↔ Run.processes P rho v o t ∧ t ≤ cut := by
  simp only [Run.processes, runPrefix_event_iff hs cut]
  exact exists_and_right

theorem runPrefix_handlesAt_iff (hs : ScheduleWellFormed E rho) (cut : Time)
    (i : Nat) (v : V) (o : P.Object) (t : Time) :
    Run.handlesAt P (runPrefix rho cut) i v o t ↔
      Run.handlesAt P rho i v o t ∧ t ≤ cut := by
  constructor
  · rintro ⟨obj, he, hh⟩
    have states := (runPrefix_event_states hs cut he).1
    obtain ⟨orig, time⟩ := (runPrefix_event_iff hs cut i _).mp he
    exact ⟨⟨obj, orig, states ▸ hh⟩, time⟩
  · rintro ⟨⟨obj, orig, hh⟩, time⟩
    have he := (runPrefix_event_iff hs cut i _).mpr ⟨orig, time⟩
    exact ⟨obj, he, (runPrefix_event_states hs cut he).1.symm ▸ hh⟩

theorem runPrefix_acceptsAt_iff (hs : ScheduleWellFormed E rho) (cut : Time)
    (i : Nat) (v : V) (o : P.Object) (t : Time) :
    Run.acceptsAt P (runPrefix rho cut) i v o t ↔
      Run.acceptsAt P rho i v o t ∧ t ≤ cut := by
  constructor
  · rintro ⟨hh, hf, ht⟩
    obtain ⟨obj, he, hhandle⟩ := hh
    have states := runPrefix_event_states hs cut he
    obtain ⟨hh', time⟩ := (runPrefix_handlesAt_iff hs cut i v o t).mp ⟨obj, he, hhandle⟩
    exact ⟨⟨hh', states.1 ▸ hf, states.2 ▸ ht⟩, time⟩
  · rintro ⟨⟨hh, hf, ht⟩, time⟩
    have hh' := (runPrefix_handlesAt_iff hs cut i v o t).mpr ⟨hh, time⟩
    obtain ⟨obj, he, hhandle⟩ := hh'
    have states := runPrefix_event_states hs cut he
    exact ⟨⟨obj, he, hhandle⟩, states.1.symm ▸ hf, states.2.symm ▸ ht⟩

omit [DecidableEq V] in
theorem runPrefix_schedule (hs : ScheduleWellFormed E rho) (cut : Time)
    (hc : 0 ≤ cut) (hh : cut ≤ rho.horizon) :
    ScheduleWellFormed E (runPrefix rho cut) := by
  have mem (e : Event V P.Object) : e ∈ (runPrefix rho cut).events ↔
      e ∈ rho.events ∧ e.time ≤ cut := by
    rw [runPrefix_events hs]; simp
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.sorted.take
  · exact hs.nodup.take
  · intro e he
    exact ⟨(hs.in_horizon e ((mem e).mp he).1).1, ((mem e).mp he).2⟩
  · intro e he; exact hs.honest_only e ((mem e).mp he).1
  · intro v t he; exact hs.tick_public v t ((mem _).mp he).1
  · intro v hv t pub nonneg bound
    exact (mem _).mpr ⟨hs.tick_total v hv t pub nonneg (bound.trans hh), bound⟩

/-- Restricting a valid execution preserves authentication, including
carried signatures. Their emitting ticks precede the delivered object. -/
theorem runPrefix_execution (hx : ExecutionValid P E rho) (cut : Time)
    (hc : 0 ≤ cut) (hh : cut ≤ rho.horizon) : ExecutionValid P E (runPrefix rho cut) := by
  have hs := hx.toScheduleWellFormed
  refine { runPrefix_schedule hs cut hc hh with
    wire := ?_, deps := ?_, fresh := ?_, unforgeable := ?_, carried := ?_ }
  · intro i v o t he
    exact hx.wire i v o t ((runPrefix_event_iff hs cut i _).mp he).1
  · intro i v o t he
    rw [(runPrefix_event_states hs cut he).1]
    exact hx.deps i v o t ((runPrefix_event_iff hs cut i _).mp he).1
  · intro i v o t he
    rw [(runPrefix_event_states hs cut he).1]
    exact hx.fresh i v o t ((runPrefix_event_iff hs cut i _).mp he).1
  · intro v o t hp u hu holder
    obtain ⟨orig, time⟩ := (runPrefix_processes_iff hs cut v o t).mp hp
    obtain ⟨t', ht', emit⟩ := hx.unforgeable v o t orig u hu holder
    exact ⟨t', ht', (runPrefix_emits_iff hs cut E u o t').mpr ⟨emit, ht'.trans time⟩⟩
  · intro v o t hp obj carries u hu holder
    obtain ⟨orig, time⟩ := (runPrefix_processes_iff hs cut v o t).mp hp
    obtain ⟨t', ht', emit⟩ := hx.carried v o t orig obj carries u hu holder
    exact ⟨t', ht', (runPrefix_emits_iff hs cut E u obj t').mpr ⟨emit, ht'.trans time⟩⟩

end AvailableChain.Engine
end
