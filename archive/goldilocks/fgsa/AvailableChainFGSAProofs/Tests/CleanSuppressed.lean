module
public import AvailableChainFGSAProofs.Proofs.Clean.StateGate -- shake: keep (source declarations)
public import Mathlib.Tactic.IntervalCases -- shake: keep (interval_cases tests)

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.CleanSuppressed

open AvailableChain.SimplexFG

abbrev p : Params :=
  { Δ := 2, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

def env : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 1 ∨ 9 ≤ t)⟩

def head : Obj p := ⟨.seat (.base (.head 1)) ⟨0, by decide⟩, .head genesisRoot⟩

def run : V2.D.Run (Fin 2) (fgsa p unitCodec) where
  honest := {0}
  horizon := 20
  events := [.tick 0 0, .restart 0 9, .tick 0 10, .deliver 0 head 10,
    .tick 0 12, .tick 0 14, .tick 0 16, .tick 0 18, .tick 0 20]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

/-- The fixture includes every awake public tick and orders the wake before its duties. -/
theorem fgp_schedule : V2.D.ScheduleWellFormed env run := by
  refine
    { horizon_nonneg := by decide
      sorted := by decide
      nodup := by decide
      in_horizon := ?_
      honest_only := ?_
      tick_public := ?_
      tick_total := ?_ }
  · intro e he
    simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro e he
    simp only [run, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro v t ht
    simp [run] at ht
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first | exact ⟨0, rfl⟩ | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ |
      exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩ | exact ⟨10, rfl⟩
  · intro v hv t ⟨k, hk⟩ ht0 hth ha
    have hv0 : v = 0 := by simpa only [run, Finset.mem_singleton] using hv
    subst v
    change t = (k : Int) * 2 at hk
    change t ≤ 20 at hth
    have hk10 : k ≤ 10 := by dsimp [Time] at hk hth; omega
    have hA : t < 1 ∨ 9 ≤ t := by simpa [env] using ha
    interval_cases k <;> simp_all [run, env]

/-- A fresh faulty HEAD makes the diagnostic raw confirmation nonempty after a wake. -/
theorem raw_nonempty :
    SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p unitCodec env run 8 0).fg.F)
      (actView (clockPre p (storeAt p unitCodec env run 8 0)
        (SA.gateTime p.toParams 1))) 1 = some .genesis := by
  decide +kernel

/-- The executed gate is suppressed, although the diagnostic raw result is nonempty. -/
theorem executed_empty : gateResultAt p unitCodec env run 8 = some none := by
  apply clean_gate_unjoined (v := (0 : Fin 2)) (s := 1) fgp_schedule
    (by change run.events[8]? = some (.tick 0 20); decide)
  intro hE
  have hm : (storeAt p unitCodec env run 8 0).restartTime = some 9 := by decide +kernel
  have hw := hE.2
  change (match (storeAt p unitCodec env run 8 0).restartTime with
    | none => True | some w => w ≤ 8) at hw
  rw [hm] at hw
  norm_num at hw

end AvailableChain.FGSA.Run.Tests.CleanSuppressed

#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.p
#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.env
#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.head
#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.run
#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.fgp_schedule
#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.raw_nonempty
#print axioms AvailableChain.FGSA.Run.Tests.CleanSuppressed.executed_empty

end
