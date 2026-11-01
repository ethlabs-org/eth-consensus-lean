module
public import AvailableChainFGSARun.Model.TestSupport.Sleep

@[expose] public section

namespace AvailableChain.FGSA.Run.EmissionFreshnessTests

open AvailableChain.SimplexFG

/-- The current Params permits a digest collision outside the held named scope. -/
abbrev p : Params := { SleepTests.p with digest := fun _ => ⟨2⟩ }
abbrev P := fgsa p unitCodec

def first : Obj p :=
  ⟨.seat (.prop 1) ⟨0, by decide⟩, .proposal (namedProposal p .genesis 1 0 [] [] [])⟩
def second : Obj p :=
  ⟨.seat (.prop 2) ⟨0, by decide⟩, .proposal (namedProposal p .genesis 2 0 [] [] [])⟩
abbrev env : Generic.Env (Fin 2) := ⟨2, by decide, 0, by decide, fun _ _ => true⟩

abbrev run : V2.D.Run (Fin 2) P where
  honest := {0}
  horizon := 18
  events := [.tick 0 0, .tick 0 2, .tick 0 4, .tick 0 6, .tick 0 8,
    .deliver 0 first 8, .tick 0 10, .tick 0 12, .tick 0 14, .tick 0 16, .tick 0 18]
  seatOf := fun l _ => match l with
    | .prop s => if s = 2 then 0 else 1
    | _ => 1
  input := fun _ _ => ()

end AvailableChain.FGSA.Run.EmissionFreshnessTests
end
