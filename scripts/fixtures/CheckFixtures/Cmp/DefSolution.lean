module

@[expose] public section

namespace CheckFixtures.Cmp

/-! Comparator fixture: `d` defined differently from `Cmp.DefChallenge`; the statement is
syntactically the same, but the exported constant `d` differs; `comparator-def.json` must fail
("Const does not match"). -/

def d : Nat := 2

theorem t : d = d := rfl

end CheckFixtures.Cmp

end
