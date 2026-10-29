module

@[expose] public section

namespace CheckFixtures.Cmp

/-! Comparator fixture: the same name with a different statement; `comparator-stmt.json` must
fail. -/

theorem t : 2 + 2 = 4 := rfl

end CheckFixtures.Cmp

end
