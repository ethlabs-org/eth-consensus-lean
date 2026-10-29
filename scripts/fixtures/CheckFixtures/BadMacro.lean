module
public import CheckFixtures.BadMacro.A

@[expose] public section

macro "fixtureRootOne" : term => `(1)
def macroRootResult : Nat := fixtureRootOne
