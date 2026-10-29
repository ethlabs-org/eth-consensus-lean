module
public import Lean

@[expose] public section

namespace FixtureScoped
scoped notation "fixtureTwo" => (2 : Nat)
end FixtureScoped
