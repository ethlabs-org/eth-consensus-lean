module
public import Lean

@[expose] public section

namespace SnapAux
def loop (n acc : Nat) : Nat :=
  if h : n = 0 then acc else loop (n - 1) (acc + 1)
termination_by n
decreasing_by omega
end SnapAux
