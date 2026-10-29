module
public import Lean

@[expose] public section

macro "fixtureOne" : term => `(1)
def macroResult : Nat := fixtureOne
