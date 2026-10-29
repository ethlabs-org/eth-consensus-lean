module

@[expose] public section

namespace CheckFixtures.BadImplBy

def g : Nat := 0

@[implemented_by g] def f : Nat := 0

end CheckFixtures.BadImplBy
