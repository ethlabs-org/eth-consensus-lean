module

@[expose] public section

namespace CheckFixtures.BadAllowlisted

theorem t2 : 1 = 1 := rfl

theorem t3 : 1 = 1 := rfl

/-- A real Prop-class instance, but of a class that is not permitted (only `Countable` is). -/
instance t4 : Nonempty Nat := ⟨0⟩

end CheckFixtures.BadAllowlisted
