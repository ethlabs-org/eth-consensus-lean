import Lean

/-! Negative fixture for the alpha-equality guard of `ConsensusTests/ReviewAxioms.lean` (same
guard code): the statement `Stmt` (`2 = 2`) is not the type of `src` (`1 = 1`), so the `run_meta`
throws, `#guard_msgs` (expecting no message) fails, and `lake env lean` exits nonzero. -/

namespace CheckFixtures.ReviewEqBad

def Stmt : Prop := 2 = 2

theorem src : 1 = 1 := rfl

end CheckFixtures.ReviewEqBad

open Lean Meta

#guard_msgs in
run_meta do
  for (s, t) in [(``CheckFixtures.ReviewEqBad.Stmt, ``CheckFixtures.ReviewEqBad.src)] do
    let some v := (← getConstInfo s).value? | throwError "{s} is not a definition"
    unless v == (← getConstInfo t).type do
      throwError "{s} is not alpha-equal to the type of {t}"
