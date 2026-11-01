module
public import AvailableChainFGSARun.Model.TestSupport.Sleep -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.TestSupport.EmissionFreshness -- shake: keep (axioms)

public section

namespace AvailableChain.FGSA.Run.HistoryTests

open SleepTests

/-- Process a HEAD before sleep; restart clears its volatile vote. -/
def run : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 18
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 proposal 8, .tick 0 10, .deliver 0 row 10, .deliver 0 head 10,
    .restart 0 15, .tick 0 16, .tick 0 18]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

private theorem sleep_valid : V2.D.SleepWellFormed env run := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      V2.Event.tick.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro v o t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  · intro v t h
    simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      V2.Event.restart.injEq, reduceCtorEq, or_false, false_or] at h
    rcases h with ⟨rfl, rfl⟩; decide
  · intro v hv t _ _ hw
    have hv0 : v = 0 := Finset.mem_singleton.mp hv
    subst v
    have ht : t = 15 := by
      simp [V2.D.Wakes, env] at hw
      dsimp [Time] at *; omega
    subst t; simp [run]

/-- The full validity record checks sleep, schedule, delivery and signatures. -/
theorem history_valid : V2.D.ExecutionValid env run := by
  refine { toSleepWellFormed := sleep_valid, toScheduleWellFormed := ?_,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide
    · intro e he
      simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;> decide
    · intro v t he
      simp only [run, List.mem_cons, List.not_mem_nil, or_false,
        V2.Event.tick.injEq, reduceCtorEq, or_false, false_or] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨4, rfl⟩
      · exact ⟨5, rfl⟩
      · exact ⟨8, rfl⟩
      · exact ⟨9, rfl⟩
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      have htimes : t = 0 ∨ t = 2 ∨ t = 4 ∨ t = 6 ∨ t = 8 ∨ t = 10 ∨
          t = 16 ∨ t = 18 := by
        simp [env] at hk ha
        change t ≤ 18 at hh
        dsimp [Time] at *; omega
      rcases htimes with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [run]
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp only [run, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq, or_false, false_or] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp [run] at hib
    all_goals interval_cases i <;> first | contradiction | decide +kernel
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      have hu0 : u = 0 := Finset.mem_singleton.mp hu
      subst u
      unfold V2.D.Run.holder at hh
      cases ha : o.auth <;> simp [ha, run] at hh
    · intro v o t hp o' hc u hu hh
      have hu0 : u = 0 := Finset.mem_singleton.mp hu
      subst u
      unfold V2.D.Run.holder at hh
      cases ha : o'.auth <;> simp [ha, run] at hh

/-- The full valid trace has a processed HEAD that is erased at wake. -/
theorem head_erased :
    P.processed (V2.D.Run.stateBefore env run 9 0) head = true ∧
      P.processed (V2.D.Run.stateBefore env run 10 0) head = false := by
  decide +kernel

/-- Past processing satisfies the historical service disjunction after erasure. -/
theorem historical_service : V2.D.DeliveryService env run 0 head 16 18 := by
  left
  exact ⟨9, by decide, head_erased.1⟩

end AvailableChain.FGSA.Run.HistoryTests
end

#print axioms AvailableChain.FGSA.Run.HistoryTests.history_valid
#print axioms AvailableChain.FGSA.Run.HistoryTests.head_erased
#print axioms AvailableChain.FGSA.Run.HistoryTests.historical_service

public section

namespace AvailableChain.FGSA.Run.RefusalTests

open EmissionFreshnessTests

/-- The faulty future proposer sends before its admission time. -/
def future : Obj p :=
  ⟨.seat (.prop 3) ⟨0, by decide⟩, .proposal (namedProposal p .genesis 3 0 [] [] [])⟩

def refusedRun : V2.D.Run (Fin 2) P :=
  { EmissionFreshnessTests.run with events :=
    [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
      .deliver 0 future 8, .tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16, .tick 0 18] }

private theorem refused_sleep_valid : V2.D.SleepWellFormed env refusedRun := by
  refine ⟨by intros; rfl, by intros; rfl, by intros; rfl, ?_⟩
  intro v hv t ht hh hw
  have hf := hw.2
  change true = false at hf
  cases hf

/-- The collision trace satisfies every engine validity condition. -/
theorem refused_valid : V2.D.ExecutionValid env refusedRun := by
  refine { toScheduleWellFormed := ?_, toSleepWellFormed := refused_sleep_valid,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e he
      simp [refusedRun] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro e he
      simp [refusedRun] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    · intro v t he
      simp [refusedRun] at he
      refine ⟨(t / 2).toNat, ?_⟩
      simp; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t = (k : Time) * 2 at hk
      change t ≤ 18 at hh
      have hkbound : k ≤ 9 := by dsimp [Time] at *; omega
      interval_cases k <;> simp [refusedRun] <;>
        dsimp [Time] at * <;> omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [refusedRun] at he
    all_goals obtain ⟨rfl, rfl, rfl⟩ := he
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp [refusedRun] at hib
    all_goals interval_cases i <;> decide +kernel
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [refusedRun] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      have hu0 : u = 0 := Finset.mem_singleton.mp hu
      subst u
      change some (1 : Fin 2) = some 0 at hh
      cases hh
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [refusedRun] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      change o' ∈ [] ∨ o' ∈ [] ∨ o' ∈ [] at hc
      simp at hc

/-- A refused handler call does not satisfy the processing-history exemption. -/
theorem refused_not_history :
    V2.D.Run.handlesAt env refusedRun 5 0 future 8 ∧
      ¬ V2.D.ProcessedByActionCut env refusedRun 0 future 16 := by
  constructor
  · exact ⟨future, rfl, Or.inl rfl⟩
  · rintro ⟨k, hk, hp⟩
    change k ≤ 9 at hk
    interval_cases k <;>
      exact False.elim ((by decide +kernel : ¬ (type_of% hp)) hp)

end AvailableChain.FGSA.Run.RefusalTests
end

#print axioms AvailableChain.FGSA.Run.RefusalTests.refused_valid
#print axioms AvailableChain.FGSA.Run.RefusalTests.refused_not_history
