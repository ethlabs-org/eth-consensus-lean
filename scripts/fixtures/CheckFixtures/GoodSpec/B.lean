module
public import CheckFixtures.GoodSpec.A

@[expose] public section

namespace CheckFixtures.GoodSpec

/-- A definition in a second module that imports the first. -/
def fixed (c : Color) : Prop := colorEquiv c = c

end CheckFixtures.GoodSpec
