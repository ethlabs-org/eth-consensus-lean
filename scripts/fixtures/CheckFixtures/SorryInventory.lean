module

/-! Fixtures for declaration-level sorry closure, including private and type edges. -/
public section
namespace SorryInventory

private theorem hidden : False := by sorry

theorem through_private : False := hidden

def unfinishedType : Prop := by sorry

axiom type_only : unfinishedType

-- The inductive and its constructor form a dependency cycle. The constructor
-- directly mentions the unfinished type; every cycle member must be an ancestor.
inductive Cycle where
  | mk : unfinishedType → Cycle

theorem unrelated : True := by sorry

-- A root whose closure has no sorry owner.
theorem clean : True := trivial

end SorryInventory
