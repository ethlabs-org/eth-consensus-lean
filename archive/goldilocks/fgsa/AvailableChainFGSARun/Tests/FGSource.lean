module
public import AvailableChainFGSARun.Proofs.FGSource
public import AvailableChainFGSARun.Model.TestSupport.Sleep

@[expose] public section

namespace AvailableChain.FGSA.Run.FGSourceTests

open SleepTests

/-- A slot-2 HEAD supports the retained slot-1 block. -/
def head2 : Obj p := ⟨.seat (.base (.head 2)) ⟨0, by decide⟩, .head ⟨2⟩⟩

def env (w : Time) : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ w = 0 ∨ t < 15 ∨ w ≤ t)⟩

/-- The four traces differ only in the wake and the required awake ticks. -/
def run (w : Time) : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 28
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 proposal 8, .tick 0 10, .tick 0 12, .tick 0 14] ++
    (if w = 28 then [.restart 0 28, .tick 0 28] else
      (if w = 17 then [.restart 0 17] else
        if w = 16 then [.restart 0 16, .tick 0 16] else [.tick 0 16]) ++
      [.tick 0 18, .deliver 0 head2 18, .tick 0 20, .tick 0 22,
        .tick 0 24, .tick 0 26, .tick 0 28])
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

private theorem source_tick_total (w : Time)
    (hw : w = 0 ∨ w = 16 ∨ w = 17 ∨ w = 28) :
    ∀ v ∈ (run w).honest, ∀ t, V2.PublicTime (env w) t → 0 ≤ t →
      t ≤ (run w).horizon → (env w).awake v t = true →
      V2.Event.tick v t ∈ (run w).events := by
  intro v hv t ⟨k, hk⟩ ht hh ha
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  have he : t = (k : Time) * 2 := hk
  change t ≤ 28 at hh
  have hkbound : k ≤ 14 := by dsimp [Time] at *; omega
  rcases hw with rfl | rfl | rfl | rfl
  all_goals interval_cases k <;> simp [env] at ha <;> simp [run] <;>
    dsimp [Time] at * <;> omega

private theorem source_schedule (w : Time) (hw : w = 0 ∨ w = 16 ∨ w = 17 ∨ w = 28) :
    V2.D.ScheduleWellFormed (env w) (run w) := by
  rcases hw with rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide, by decide, by decide, ?_, ?_, ?_,
    source_tick_total _ (by simp)⟩
  all_goals first
    | (intro e he; simp [run] at he; rcases he with rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide)
    | (intro v t ht; simp [run] at ht; refine ⟨(t / 2).toNat, ?_⟩;
        simp [env]; dsimp [Time] at *; omega)

private theorem source_wake_restart (w : Time)
    (hw : w = 0 ∨ w = 16 ∨ w = 17 ∨ w = 28) :
    ∀ v ∈ (run w).honest, ∀ t, 0 < t → t ≤ (run w).horizon →
      V2.D.Wakes (env w) v t → V2.Event.restart v t ∈ (run w).events := by
  intro v hv t ht hh h
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  rcases hw with rfl | rfl | rfl | rfl
  all_goals simp [V2.D.Wakes, env] at h <;> simp [run] <;> dsimp [Time] at * <;> omega

private theorem source_deliver_awake (w : Time)
    (hw : w = 0 ∨ w = 16 ∨ w = 17 ∨ w = 28) :
    ∀ v o t, V2.Event.deliver v o t ∈ (run w).events → (env w).awake v t = true := by
  intro v o t h
  rcases hw with rfl | rfl | rfl | rfl
  all_goals simp [run] at h
  all_goals first
    | (rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide)

private theorem source_sleep (w : Time) (hw : w = 0 ∨ w = 16 ∨ w = 17 ∨ w = 28) :
    V2.D.SleepWellFormed (env w) (run w) := by
  rcases hw with rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, source_deliver_awake _ (by simp), ?_,
    source_wake_restart _ (by simp)⟩
  all_goals first
    | (solve | intro v t h; simp [run] at h; simp [env] <;> dsimp [Time] at * <;> omega)
    | (solve | intro v t h; simp_all [run])

/-- Every source test checks the complete validity record. -/
theorem valid (w : Time) (hw : w = 0 ∨ w = 16 ∨ w = 17 ∨ w = 28) :
    V2.D.ExecutionValid (env w) (run w) := by
  refine { toScheduleWellFormed := source_schedule w hw,
           toSleepWellFormed := source_sleep w hw,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · rcases hw with rfl | rfl | rfl | rfl
    all_goals refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [run] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp [run] at hib
    all_goals interval_cases i <;> first
      | decide +kernel
      | exact False.elim ((by decide +kernel : ¬ (type_of% hi)) hi)
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

/-- A wake at the FG action time has an empty source. -/
theorem wake_at_action :
    fgSource p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (env 28) (run 28) 10 0) (p.actionTime 1)).st = none := by
  exact fgsa_fgAction_unjoined_source_none (env 28) (run 28)
    (valid 28 (Or.inr (Or.inr (Or.inr rfl)))) (by decide) (by decide +kernel)

/-- A wake one time unit after the join cutoff has an empty source. -/
theorem wake_after_cutoff :
    fgSource p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (env 17) (run 17) 16 0) (p.actionTime 1)).st = none := by
  exact fgsa_fgAction_unjoined_source_none (env 17) (run 17)
    (valid 17 (Or.inr (Or.inr (Or.inl rfl)))) (by decide) (by decide +kernel)

/-- Equality at the join cutoff permits the source supported by the HEAD. -/
theorem wake_at_cutoff :
    joinedNow p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (env 16) (run 16) 17 0) (p.actionTime 1)).st = true ∧
    (fgSource p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (env 16) (run 16) 17 0) (p.actionTime 1)).st).isSome = true := by
  decide +kernel

/-- The initial joined epoch also has a source. -/
theorem joined_source :
    joinedNow p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (env 0) (run 0) 16 0) (p.actionTime 1)).st = true ∧
    (fgSource p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (env 0) (run 0) 16 0) (p.actionTime 1)).st).isSome = true := by
  decide +kernel

end AvailableChain.FGSA.Run.FGSourceTests
end

#print axioms AvailableChain.FGSA.Run.FGSourceTests.valid
#print axioms AvailableChain.FGSA.Run.FGSourceTests.wake_at_action
#print axioms AvailableChain.FGSA.Run.FGSourceTests.wake_after_cutoff
#print axioms AvailableChain.FGSA.Run.FGSourceTests.wake_at_cutoff
#print axioms AvailableChain.FGSA.Run.FGSourceTests.joined_source
