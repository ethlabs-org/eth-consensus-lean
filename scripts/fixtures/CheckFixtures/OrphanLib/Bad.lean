module

@[expose] public section

/-! An orphan module (not imported by its root) with two findings: an `opaque` and an `axiom`. -/

namespace CheckFixtures.OrphanLib.Bad

opaque hidden : Nat

axiom assumed : 1 = 2

end CheckFixtures.OrphanLib.Bad
