module

@[expose] public section

/-! Root of a fixture library for the check-decls step: it does not import `OrphanLib.Bad`, so a check
that only imported the root would miss the findings there. check.sh imports every inventory module. -/

namespace CheckFixtures.OrphanLib

def ok : Nat := 1

end CheckFixtures.OrphanLib
