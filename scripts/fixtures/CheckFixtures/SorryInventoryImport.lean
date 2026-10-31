module
import CheckFixtures.SorryInventory

/-! A root whose proof depends on an imported, non-exposed theorem body. -/
public theorem SorryInventory.imported : False := SorryInventory.through_private
