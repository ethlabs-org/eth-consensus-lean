module
public import AvailableChainKit.Engine.Execution

@[expose] public section
namespace AvailableChain.Engine
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- The common first-loss induction for finite leases. The tick step may
use protection after any earlier tick in the interval. This permits an
instance to bound release counts from its actual authenticated emissions. -/
theorem state_interval_induction {V : Type} [DecidableEq V] {n : Nat}
    (P : ProtocolSpec n) (rho : Run V P) (Q : V → P.State → Prop)
    (start finish : Nat) (hfinish : start ≤ finish)
    (hbase : ∀ v ∈ rho.honest, Q v (Run.stateBefore P rho start v))
    (hprocess : ∀ v ∈ rho.honest, ∀ st o, Q v st → Q v (P.process st o))
    (hclock : ∀ i v t, start ≤ i → i < finish →
      rho.events[i]? = some (.tick v t) → v ∈ rho.honest →
      Q v (Run.stateBefore P rho i v) →
      (∀ j, start ≤ j → j < i → ∀ u ∈ rho.honest,
        Q u (Run.stateBefore P rho (j + 1) u)) →
      Q v (P.clock (Run.stateBefore P rho i v) t)) :
    ∀ v ∈ rho.honest, Q v (Run.stateBefore P rho finish v) := by
  have all : ∀ i, start ≤ i → i ≤ finish →
      ∀ v ∈ rho.honest, Q v (Run.stateBefore P rho i v) := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hlo hhi v hv
      by_cases eq : i = start
      · subst i; exact hbase v hv
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have prev := ih j (by omega) (by omega) (by omega)
      cases he : rho.events[j]? with
      | none =>
        have eq : Run.stateBefore P rho (j + 1) = Run.stateBefore P rho j := by
          unfold Run.stateBefore
          rw [List.take_add_one, List.foldl_append, he]
          rfl
        rw [eq]; exact prev v hv
      | some e =>
        rw [stateBefore_succ_event he]
        cases e with
        | deliver u o t =>
          by_cases eq : v = u
          · subst v
            simpa only [World.step, Function.update_self] using hprocess u hv _ o (prev u hv)
          · simpa [World.step, eq] using prev v hv
        | tick u t =>
          by_cases eq : v = u
          · subst v
            simp only [World.step, Function.update_self]
            apply hclock j u t (by omega) (by omega) he hv (prev u hv)
            intro k hk hkj w hw
            exact ih (k + 1) (by omega) (by omega) (by omega) w hw
          · simpa [World.step, eq] using prev v hv
  exact all finish hfinish (le_refl _)

/-- A field unchanged by delivery has its clock value at a public read.
This uses only the common event schedule, so it applies to every instance. -/
theorem read_field_eq_clock {α V : Type} [DecidableEq V] {n : Nat}
    (P : ProtocolSpec n) (f : P.State → α)
    (hf : ∀ st o, f (P.process st o) = f st)
    (E : Env V) (rho : Run V P) (hs : ScheduleWellFormed E rho)
    (reader : V) (t : Time) (htick : Event.tick reader t ∈ rho.events) :
    f (Run.readAt P rho t reader) =
      f (P.clock (Run.stateBeforeTime P rho t reader) t) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  let k := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hik : i < k := (index_lt_read_length_iff hs t hi).mpr (le_refl _)
  have hstep : Run.stateBefore P rho (i + 1) reader =
      P.clock (Run.stateBeforeTime P rho t reader) t := by
    rw [stateBefore_succ_event hi]
    simp only [World.step, Function.update_self]
    exact congrArg (fun st => P.clock st t) (stateBefore_tick_eq_stateBeforeTime hs hi)
  have hstay : ∀ j, i + 1 ≤ j → j ≤ k →
      f (Run.stateBefore P rho j reader) =
        f (Run.stateBefore P rho (i + 1) reader) := by
    intro j
    induction j with
    | zero => intro hj; exact (Nat.not_succ_le_zero i hj).elim
    | succ j ih =>
        intro hj hjk
        rcases eq_or_lt_of_le hj with he | hlt
        · rw [he]
        · rw [← ih (by omega) (by omega)]
          cases he : rho.events[j]? with
          | none => simp [Run.stateBefore, List.take_add_one, he]
          | some e =>
              rw [stateBefore_succ_event he]
              cases e with
              | deliver v o t' =>
                  by_cases hv : reader = v
                  · subst v; simpa [World.step] using hf _ o
                  · simp [World.step, hv]
              | tick v t' =>
                  have hv : reader ≠ v := by
                    intro heq
                    subst v
                    have hu : t' ≤ t := (index_lt_read_length_iff hs t he).mp (by omega)
                    have ht : t' = t := by
                      apply le_antisymm hu
                      by_contra hn
                      have hji := eventIndex_lt_of_time_lt hs he hi (lt_of_not_ge hn)
                      omega
                    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
                    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
                    have hij : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp
                      (by rw [hje, hie, ht])
                    omega
                  simp [World.step, hv]
  rw [readAt_eq_stateBefore hs t]
  exact (hstay k (by omega) (le_refl _)).trans (congrArg f hstep)

end AvailableChain.Engine
end
