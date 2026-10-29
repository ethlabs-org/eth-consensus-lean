module
public import CheckFixtures.Proof

@[expose] public section

namespace CheckFixtures.BadMacro

/-- Uses only the macro: no constant of `CheckFixtures.Proof` appears in the term. -/
def d : Nat := mkOne

end CheckFixtures.BadMacro
