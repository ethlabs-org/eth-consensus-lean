module
public import Lean

@[expose] public section

initialize fixtureCell : IO.Ref Nat ← IO.mkRef 0
