module

@[expose] public section

namespace CheckFixtures.BadDefProp

/-- A proof stated with `def`. -/
def h : 2 + 2 = 4 := rfl

/-- A proof stated with `abbrev`. -/
abbrev h2 : True := trivial

end CheckFixtures.BadDefProp
