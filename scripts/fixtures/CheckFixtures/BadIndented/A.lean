module
public meta import Lean.Elab.Command

@[expose] public section

namespace CheckFixtures.BadIndented

/-! Commands indented under a namespace: Lean accepts them, and `example` and `run_cmd` leave no
constant for `content` to see. -/

def x : Nat := 0
  example : True := trivial
  theorem t : True := trivial
  run_cmd Lean.logInfo "executed"

end CheckFixtures.BadIndented
