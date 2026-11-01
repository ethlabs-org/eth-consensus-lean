module
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp -- shake: keep (source test uses)

set_option linter.privateModule false

namespace AvailableChain.FGSA.Run.Tests.RestartEpochs

open AvailableChain.SimplexFG

-- These local fixtures copy SleepTests.ownRun and joinRun from Run/Tests/Sleep.
-- That module proves ExecutionValid; this test checks the two failed implications.
private abbrev p : Params :=
  { Δ := 2, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def proposal : Obj p :=
  ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal (namedProposal p .genesis 1 0 [] [] [])⟩

private def ownEnv : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 31 ∨ 35 ≤ t)⟩

private def ownHead : Obj p := ⟨.seat (.base (.head 2)) ⟨0, by decide⟩, .head ⟨2⟩⟩

private def ownRun : V2.D.Run (Fin 2) (fgsa p unitCodec) where
  honest := {0}
  horizon := 38
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 proposal 8, .tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16,
    .tick 0 18, .deliver 0 ownHead 18, .tick 0 20, .tick 0 22, .tick 0 24,
    .tick 0 26, .tick 0 28, .tick 0 30, .restart 0 35, .tick 0 36, .tick 0 38]
  seatOf := fun l _ => match l with | .base .fg => 0 | _ => 1
  input := fun _ _ => ()

private def joinEnv (w : Time) : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 1 ∨ w ≤ t)⟩

private def joinRun (w : Time) : V2.D.Run (Fin 2) (fgsa p unitCodec) where
  honest := {0}
  horizon := 26
  events := [.tick 0 0, .restart 0 w] ++
    (if w = 8 then [.tick 0 8] else []) ++
    [.tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16, .tick 0 18,
      .tick 0 20, .tick 0 22, .tick 0 24, .tick 0 26]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

/-- A valid restart can remove a directly received HEAD from current processing.
Historical processing is therefore not a general safe-history supplier. -/
private theorem retained_head_history_not_safe :
    ¬ Gen.V2.Duty.HistorySafeAt ownEnv ownRun 0 ownHead 35 := by
  intro h
  have hp : (fgsa p unitCodec).processed
      (V2.D.Run.stateBefore ownEnv ownRun 12 0) ownHead = true := by
    decide +kernel
  have hk : 12 ≤ V2.D.Run.actionCut ownRun 35 := by decide +kernel
  have hf : (fgsa p unitCodec).processed
      (V2.D.Run.stateAfterRestartsAt ownEnv ownRun 35 0) ownHead = false := by
    decide +kernel
  have he := h ⟨12, hk, hp⟩
  rw [hf] at he
  cases he

/-- The existing valid fixture is awake at a HEAD tick but has not joined. -/
private theorem awake_head_tick_not_joined :
    (joinEnv 9).awake 0 10 = true ∧
    joinedNow p ((fgsa p unitCodec).clock
      (V2.D.Run.stateBefore (joinEnv 9) (joinRun 9) 2 0) 10).st = false := by
  exact ⟨by decide +kernel, by decide +kernel⟩

end AvailableChain.FGSA.Run.Tests.RestartEpochs

#print axioms AvailableChain.FGSA.Run.Tests.RestartEpochs.retained_head_history_not_safe
#print axioms AvailableChain.FGSA.Run.Tests.RestartEpochs.awake_head_tick_not_joined
