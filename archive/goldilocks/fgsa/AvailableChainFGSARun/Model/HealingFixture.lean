module
public import AvailableChainEngineV2.Engine.Duty.Run
public import AvailableChainFGSARun.Model.Protocol

@[expose] public section

namespace AvailableChain.FGSA.Run.HealingFixture
open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3b. S5 fixture: one honest node, positive horizon, and unchanged SA clocks. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 304

abbrev Object := (fgsa params unitCodec).Object
abbrev Event := V2.Event (Fin 1) Object
abbrev FixtureNode := (fgsa params unitCodec).State

def mkRun (es : List Event) : V2.D.Run (Fin 1) (fgsa params unitCodec) where
  honest := Finset.univ
  horizon := horizon
  events := es
  seatOf := fun _ _ => 0
  input := fun _ _ => ()

/-- One tick, then one delivery of each released object, in release order. -/
def batch (acc : List Event × FixtureNode) (n : Nat) : List Event × FixtureNode :=
  let out := V2.D.tick env (mkRun []) acc.2 0 (n : Time)
  (acc.1 ++ [.tick 0 (n : Time)] ++ out.2.map (fun o => .deliver 0 o (n : Time)),
    out.2.foldl (fgsa params unitCodec).process out.1)

/-- The cached node avoids a repeated fold of all preceding events. -/
def runPrefix (n : Nat) : List Event × FixtureNode :=
  (List.range n).foldl batch ([], (fgsa params unitCodec).init)

def run := mkRun (runPrefix 305).1

end AvailableChain.FGSA.Run.HealingFixture
end
