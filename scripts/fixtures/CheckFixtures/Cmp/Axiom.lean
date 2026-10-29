module

@[expose] public section

namespace CheckFixtures.Cmp

/-! Comparator fixture: the solution uses a user axiom; `comparator-axiom.json` must fail. -/

axiom ax : 1 + 1 = 2

theorem t : 1 + 1 = 2 := ax

end CheckFixtures.Cmp

end
