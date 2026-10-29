module

@[expose] public section

namespace Snap

/-- Prints like `SnapA` (the instance argument is implicit) but uses another `LT Nat` instance. -/
def cmp (a b : Nat) : Prop := @LT.lt Nat ⟨fun a b => a + 1 ≤ b⟩ a b

end Snap
