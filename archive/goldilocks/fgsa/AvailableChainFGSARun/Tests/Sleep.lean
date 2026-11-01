module
public import AvailableChainFGSARun.Model.TestSupport.Sleep
public import AvailableChainFGSARun.Proofs.Restore -- shake: keep (axioms)
public import AvailableChainFGSARun.Proofs.Schedule

@[expose] public section

namespace AvailableChain.FGSA.Run.SleepTests

open AvailableChain.SimplexFG

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
theorem valid : V2.D.ExecutionValid env run := by
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

/-- A non-public wake sets now to 15 before the public tick at 16. -/
theorem non_public_wake : ¬ V2.PublicTime env 15 ∧
    (V2.D.Run.stateBefore env run 9 0).st.base.now = 15 ∧
    (V2.D.Run.stateBefore env run 9 0).st.restartTime = some 15 := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  rintro ⟨k, hk⟩
  simp [env] at hk
  dsimp [Time] at *; omega

/-- The first HEAD receipt uses the wake clock and has a strict pre-tick stamp. -/
theorem receipt_before_tick :
    (V2.D.Run.stateBefore env run 10 0).st.base.voteStamp =
      [(⟨.seat 1 0, .head ⟨2⟩⟩, 15)] ∧
    (15 : Time) < 16 ∧
    (V2.D.Run.stateBefore env run 10 0).st.base.now = 15 := by
  decide +kernel

/-- Restart keeps Λ, the retained block and the signed row. -/
theorem durable_run :
    (V2.D.Run.stateBefore env run 9 0).record =
      (V2.D.Run.stateBefore env run 8 0).record ∧
    (V2.D.Run.stateBefore env run 9 0).st.proposals = [toWire p proposal] ∧
    (V2.D.Run.stateBefore env run 9 0).st.rowPool =
      [⟨.seat .fg 0, .vote ⟨.vote 1 genesisRoot false, none⟩⟩] ∧
    P.processed (V2.D.Run.stateBefore env run 9 0) proposal = true := by
  refine ⟨?_, by decide +kernel⟩
  rw [V2.D.Run.stateBefore_succ env run (show run.events[8]? =
    some (.restart 0 15) from by rfl)]
  exact fgsa_restore_record p unitCodec _ 15

/-- Delivering the retained block again fails the fresh-delivery field. -/
theorem retained_not_fresh : ¬ V2.D.DeliveryWellFormed env
    { run with events := run.events.take 9 ++ [.deliver 0 proposal 15] } := by
  intro h
  have hf := h.fresh 9 0 proposal 15 (by decide)
  have ht : P.processed (V2.D.Run.stateBefore env
      { run with events := run.events.take 9 ++ [.deliver 0 proposal 15] } 9 0)
      proposal = true := by decide +kernel
  rw [ht] at hf
  contradiction

/-- Node 0 owns the FG seat, emits before sleep on [31,35), and wakes at 35. -/
def ownEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 31 ∨ 35 ≤ t)⟩

def ownHead : Obj p := ⟨.seat (.base (.head 2)) ⟨0, by decide⟩, .head ⟨2⟩⟩

def ownRun : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 38
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 proposal 8, .tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16,
    .tick 0 18, .deliver 0 ownHead 18, .tick 0 20, .tick 0 22, .tick 0 24,
    .tick 0 26, .tick 0 28, .tick 0 30, .restart 0 35, .tick 0 36, .tick 0 38]
  seatOf := fun l _ => match l with | .base .fg => 0 | _ => 1
  input := fun _ _ => ()

/-- Full validity includes the honest own-row emission and exact non-public wake. -/
theorem own_valid : V2.D.ExecutionValid ownEnv ownRun := by
  refine { toSleepWellFormed := ?_, toScheduleWellFormed := ?_,
           toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
  · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
    · intro e h
      simp [ownRun] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro e h
      simp [ownRun] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · intro v t h
      simp [ownRun] at h
      refine ⟨(t / 2).toNat, ?_⟩
      simp [ownEnv]; dsimp [Time] at *; omega
    · intro v hv t ⟨k, hk⟩ ht hh ha
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      change t ≤ 38 at hh
      simp [ownEnv] at hk ha
      simp [ownRun]; dsimp [Time] at *; omega
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro i v o t hi
    all_goals have he := List.mem_of_getElem? hi
    all_goals simp [ownRun] at he
    all_goals rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals have hib := (List.getElem?_eq_some_iff.mp hi).1
    all_goals simp [ownRun] at hib
    all_goals interval_cases i <;> first | contradiction | decide +kernel
  · refine ⟨?_, ?_⟩
    · intro v o t hp u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [ownRun] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      all_goals have hu0 : u = 0 := Finset.mem_singleton.mp hu
      all_goals subst u
      all_goals simp [V2.D.Run.holder, proposal, ownHead, ownRun] at hh
    · intro v o t hp o' hc u hu hh
      obtain ⟨i, hi⟩ := hp
      have he := List.mem_of_getElem? hi
      simp [ownRun] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · change carriesS p proposal o' at hc
        change o' ∈ ([] : List (Obj p)) ∨ o' ∈ [] ∨ o' ∈ [] at hc
        simp at hc
        cases hc
      · change carriesS p ownHead o' at hc
        simp [carriesS, ownHead] at hc
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v t h
      simp [ownRun] at h
      have hv : v = 0 := by tauto
      subst v
      simp [ownEnv]; dsimp [Time] at *; omega
    · intro v o t h
      simp [ownRun] at h
      rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
    · intro v t h
      simp [ownRun] at h
      rcases h with ⟨rfl, rfl⟩; decide
    · intro v hv t _ _ h
      have hv0 : v = 0 := Finset.mem_singleton.mp hv
      subst v
      have ht : t = 35 := by simp [V2.D.Wakes, ownEnv] at h; dsimp [Time] at *; omega
      subst t; simp [ownRun]

/-- An own FG row makes Λ nonempty before sleep; wake keeps the same sent entries. -/
theorem own_record_retained :
    (∃ a, Msg.row a ∈ (V2.D.Run.emitsAt ownEnv ownRun 16).map (·.payload)) ∧
    (V2.D.Run.stateBefore ownEnv ownRun 18 0).record.sent ≠ [] ∧
    (V2.D.Run.stateBefore ownEnv ownRun 19 0).record.sent =
      (V2.D.Run.stateBefore ownEnv ownRun 18 0).record.sent ∧
    (V2.D.Run.stateBefore ownEnv ownRun 19 0).record =
      (V2.D.Run.stateBefore ownEnv ownRun 18 0).record := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_⟩
  · exact ⟨.vote ⟨.vote 1 genesisRoot false, none⟩, by decide +kernel⟩
  · rw [V2.D.Run.stateBefore_succ ownEnv ownRun (show ownRun.events[18]? =
      some (.restart 0 35) from by rfl)]
    exact fgsa_restore_record p unitCodec _ 35

/-- Sleep starts at 1; equality wakes at 8, and the late case wakes at 9. -/
def joinEnv (w : Time) : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 1 ∨ w ≤ t)⟩

def joinRun (w : Time) : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 26
  events := [.tick 0 0, .restart 0 w] ++
    (if w = 8 then [.tick 0 8] else []) ++
    [.tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16, .tick 0 18,
      .tick 0 20, .tick 0 22, .tick 0 24, .tick 0 26]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

private theorem join_no_delivery (w : Time) (v : Fin 2) (o : P.Object) (t : Time) :
    ¬ V2.D.Run.processes (joinRun w) v o t := by
  rintro ⟨i, hi⟩
  have hm := List.mem_of_getElem? hi
  simp [joinRun] at hm

/-- Both join fixtures satisfy all engine validity fields and restart at their wakes. -/
theorem join_valid (w : Time) (hw : w = 8 ∨ w = 9) :
    V2.D.ExecutionValid (joinEnv w) (joinRun w) ∧
    V2.D.RestartsAtWakes (joinEnv w) (joinRun w) := by
  rcases hw with rfl | rfl
  all_goals constructor
  case inl.left =>
    refine { toSleepWellFormed := ?_, toScheduleWellFormed := ?_,
             toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
    · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
      · intro e h
        simp [joinRun] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
      · intro e h
        simp [joinRun] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
      · intro v t h
        simp [joinRun] at h
        refine ⟨(t / 2).toNat, ?_⟩
        simp [joinEnv]; dsimp [Time] at *; omega
      · intro v hv t ⟨k, hk⟩ ht hh ha
        have hv0 : v = 0 := Finset.mem_singleton.mp hv
        subst v
        change t ≤ 26 at hh
        simp [joinEnv] at hk ha
        simp [joinRun]; dsimp [Time] at *; omega
    · refine ⟨?_, ?_, ?_⟩ <;> intro i v o t hi <;>
        exact (join_no_delivery 8 v o t ⟨i, hi⟩).elim
    · refine ⟨?_, ?_⟩
      · intro v o t hp; exact (join_no_delivery 8 v o t hp).elim
      · intro v o t hp; exact (join_no_delivery 8 v o t hp).elim
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro v t h
        simp [joinRun] at h
        have hv : v = 0 := by tauto
        subst v
        simp [joinEnv]; dsimp [Time] at *; omega
      · intro v o t h; simp [joinRun] at h
      · intro v t h
        simp [joinRun] at h
        rcases h with ⟨rfl, rfl⟩; decide
      · intro v hv t _ _ h
        have hv0 : v = 0 := Finset.mem_singleton.mp hv
        subst v
        have ht : t = 8 := by simp [V2.D.Wakes, joinEnv] at h; dsimp [Time] at *; omega
        subst t; simp [joinRun]
  case inr.left =>
    refine { toSleepWellFormed := ?_, toScheduleWellFormed := ?_,
             toDeliveryWellFormed := ?_, toUnforgeableSignatures := ?_ }
    · refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩
      · intro e h
        simp [joinRun] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
      · intro e h
        simp [joinRun] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;> decide
      · intro v t h
        simp [joinRun] at h
        refine ⟨(t / 2).toNat, ?_⟩
        simp [joinEnv]; dsimp [Time] at *; omega
      · intro v hv t ⟨k, hk⟩ ht hh ha
        have hv0 : v = 0 := Finset.mem_singleton.mp hv
        subst v
        change t ≤ 26 at hh
        simp [joinEnv] at hk ha
        simp [joinRun]; dsimp [Time] at *; omega
    · refine ⟨?_, ?_, ?_⟩ <;> intro i v o t hi <;>
        exact (join_no_delivery 9 v o t ⟨i, hi⟩).elim
    · refine ⟨?_, ?_⟩
      · intro v o t hp; exact (join_no_delivery 9 v o t hp).elim
      · intro v o t hp; exact (join_no_delivery 9 v o t hp).elim
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro v t h
        simp [joinRun] at h
        have hv : v = 0 := by tauto
        subst v
        simp [joinEnv]; dsimp [Time] at *; omega
      · intro v o t h; simp [joinRun] at h
      · intro v t h
        simp [joinRun] at h
        rcases h with ⟨rfl, rfl⟩; decide
      · intro v hv t _ _ h
        have hv0 : v = 0 := Finset.mem_singleton.mp hv
        subst v
        have ht : t = 9 := by simp [V2.D.Wakes, joinEnv] at h; dsimp [Time] at *; omega
        subst t; simp [joinRun]
  case inl.right =>
    intro v t h
    simp [joinRun] at h
    rcases h with ⟨rfl, rfl⟩; simp [V2.D.Wakes, joinEnv]
  case inr.right =>
    intro v t h
    simp [joinRun] at h
    rcases h with ⟨rfl, rfl⟩; simp [V2.D.Wakes, joinEnv]

/-- At slot 2, wake 8 passes the join cutoff exactly and wake 9 waits one slot. -/
theorem join_duties :
    let eqSt := (V2.D.Run.readAt (joinEnv 8) (joinRun 8) 18 0).st
    let lateSt := (V2.D.Run.readAt (joinEnv 9) (joinRun 9) 18 0).st
    (actS p unitCodec eqSt (.headAction 2) ()).isSome = true ∧
    (actS p unitCodec eqSt (.propAction 2) ()).isSome = true ∧
    actS p unitCodec lateSt (.headAction 2) () = none ∧
    actS p unitCodec lateSt (.propAction 2) () = none ∧
    (actS p unitCodec
      (V2.D.Run.readAt (joinEnv 9) (joinRun 9) 26 0).st (.headAction 3) ()).isSome = true := by
  decide +kernel

/-- A valid wake at a tick time makes the pre-tick clock equal to that time. -/
theorem wake_at_tick :
    (joinRun 8).events[2]? = some (.tick 0 8) ∧
    (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base.now = 8 := by
  decide +kernel

/-- Initial duties are joined without a restart time; slot zero still has no proposal. -/
theorem initial_duties : (initial 1).restartTime = none ∧
    (actS p unitCodec (initial 1) (.headAction 0) ()).isSome = true ∧
    (actS p unitCodec (initial 1) (.propAction 1) ()).isSome = true ∧
    actS p unitCodec (initial 1) (.propAction 0) () = none := by
  decide +kernel

end AvailableChain.FGSA.Run.SleepTests
end

#print axioms AvailableChain.FGSA.Run.SleepTests.valid
#print axioms AvailableChain.FGSA.Run.SleepTests.non_public_wake
#print axioms AvailableChain.FGSA.Run.SleepTests.receipt_before_tick
#print axioms AvailableChain.FGSA.Run.SleepTests.durable_run
#print axioms AvailableChain.FGSA.Run.SleepTests.retained_not_fresh
#print axioms AvailableChain.FGSA.Run.SleepTests.join_valid
#print axioms AvailableChain.FGSA.Run.SleepTests.join_duties
#print axioms AvailableChain.FGSA.Run.SleepTests.wake_at_tick
#print axioms AvailableChain.FGSA.Run.SleepTests.initial_duties

#print axioms AvailableChain.FGSA.Run.SleepTests.own_valid
#print axioms AvailableChain.FGSA.Run.SleepTests.own_record_retained

public section

namespace AvailableChain.FGSA.Run.SleepContinuationTests

open SleepTests

/-- The stored proposal has a delivery before the wake and is kept across it. -/
theorem retained_origin :
    ∃ j o t, j < 9 ∧ run.events[j]? = some (.deliver 0 o t) ∧
      toWire p o = toWire p proposal ∧ j + 1 ≤ 8 ∧
      ∀ k, j + 1 ≤ k → k ≤ 9 →
        toWire p proposal ∈ (V2.D.Run.stateBefore env run k 0).st.proposals := by
  obtain ⟨j, o, t, hj, hd, ho, -, hr⟩ :=
    stored_proposal_delivered env run 9 0 (toWire p proposal) (by decide +kernel)
  have he : o = proposal := toWire_injective ho
  subst o
  have hje : j = 5 := by
    interval_cases j <;> simp [run] at hd ⊢
    have he : row = proposal := (V2.Event.deliver.inj hd).2.1
    have hm := congrArg (fun o : Obj p => o.payload) he
    change Msg.row _ = Msg.proposal _ at hm
    cases hm
  exact ⟨j, proposal, t, hj, hd, ho, by omega, hr⟩

/-- A joined node reads a strict clock bound after an exact-boundary wake. -/
theorem joined_strict :
    (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 6 0).st.base.now < 16 := by
  exact fgsa_preTick_now_lt_joined (joinEnv 8) (joinRun 8)
    (join_valid 8 (Or.inl rfl)).1.toScheduleWellFormed (by decide) (by decide)
    (by decide +kernel)

/-- Same-time wake and tick have non-strict clock and vote-stamp bounds. -/
theorem same_time_bound :
    (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base.now ≤ 8 ∧
    ∀ o : GridCO.Wire p.n .root,
      GridCO.stampVote (V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base o ≤ 8 := by
  have hs := (join_valid 8 (Or.inl rfl)).1.toScheduleWellFormed
  exact ⟨fgsa_preTick_now_le (joinEnv 8) (joinRun 8) hs (by decide),
    fgsa_preTick_votes_stamped_le (joinEnv 8) (joinRun 8) hs (by decide)⟩

/-- Kept blocks remain below the next proposal slot, even for an unjoined node. -/
theorem retained_block_bound :
    (∀ b ∈ (V2.D.Run.stateBefore env run 10 0).st.base.blocks, b.slot < 2) ∧
    (namedProposal p .genesis 1 0 [] [] []).erase ∈
      (V2.D.Run.stateBefore env run 10 0).st.base.blocks := by
  exact ⟨(fgsa_stored_block_slots env run valid.toScheduleWellFormed
    (by decide) (by decide : 0 < 2)).1, by decide +kernel⟩

/-- The epoch condition fails exactly at the same-time wake boundary. -/
theorem wake_epoch_equiv :
    let epoch := ∀ j w, j < 2 → (joinRun 8).events[j]? = some (.restart 0 w) → w < 8
    ((V2.D.Run.stateBefore (joinEnv 8) (joinRun 8) 2 0).st.base.now < 8 ↔ epoch) ∧
      ¬ epoch := by
  refine ⟨fgsa_preTick_now_lt_iff (joinEnv 8) (joinRun 8)
    (join_valid 8 (Or.inl rfl)).1.toScheduleWellFormed (by decide) (by decide), ?_⟩
  intro h
  exact (lt_irrefl (8 : Time)) (h 1 8 (by decide) (by decide))

/-- API coverage for the unjoined companion; the raw fixture result is also empty. -/
theorem gate_empty :
    GridCO.savedGenuine (FGSA.clock p
      (V2.D.Run.stateBefore (joinEnv 9) (joinRun 9) 7 0).st
      (SA.gateTime p.toParams 1)).base 1 = some none := by
  exact fgsa_gate_saved_unjoined (joinEnv 9) (joinRun 9)
    (join_valid 9 (Or.inr rfl)).1.toScheduleWellFormed (by decide) (by decide +kernel)

/-- Public admission thresholds do not require public wakes. -/
theorem admission_public (o : Obj p) : V2.PublicTime env (fgsaAdmissionTime p o) :=
  fgsa_admissionTime_public p env rfl o

end AvailableChain.FGSA.Run.SleepContinuationTests
end

#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.retained_origin
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.joined_strict
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.same_time_bound
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.retained_block_bound
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.wake_epoch_equiv
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.gate_empty
#print axioms AvailableChain.FGSA.Run.SleepContinuationTests.admission_public
