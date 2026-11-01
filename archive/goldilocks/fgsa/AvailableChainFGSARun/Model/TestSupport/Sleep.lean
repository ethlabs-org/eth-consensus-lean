module
public import AvailableChainEngineV2.Engine.Duty.Run
public import AvailableChainFGSARun.Model.Protocol
public import Mathlib.Tactic.FinCases -- shake: keep (re-export)
public import Mathlib.Tactic.IntervalCases -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA.Run.SleepTests

open AvailableChain.SimplexFG

abbrev p : Params :=
  { Δ := 2, n := 1, k := 2, η := 0, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

abbrev P := fgsa p unitCodec

def proposal : Obj p :=
  ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal (namedProposal p .genesis 1 0 [] [] [])⟩

def row : Obj p :=
  ⟨.seat (.base .fg) ⟨0, by decide⟩, .row (.vote ⟨.vote 1 genesisRoot false, none⟩)⟩

def head : Obj p := ⟨.seat (.base (.head 1)) ⟨0, by decide⟩, .head ⟨2⟩⟩

/-- Node 0 sleeps on [11,15). Node 1 holds the signing seats and is faulty. -/
def env : Generic.Env (Fin 2) :=
  ⟨2, by decide, 0, by decide, fun v t => decide (v = 1 ∨ t < 11 ∨ 15 ≤ t)⟩

/-- Deliver the block and row before sleep, then a fresh HEAD at the wake. -/
def run : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 18
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 proposal 8, .tick 0 10, .deliver 0 row 10,
    .restart 0 15, .deliver 0 head 15, .tick 0 16, .tick 0 18]
  seatOf := fun _ _ => 1
  input := fun _ _ => ()

end AvailableChain.FGSA.Run.SleepTests
end
