module

@[expose] public section

namespace CheckFixtures.BadWrapped

/-! Commands behind `set_option … in` / `open … in` wrappers and split over lines. -/

def x : Nat := 0

set_option maxRecDepth 1000 in example : True := trivial

open Nat in
example : 0 = 0 := rfl

set_option maxRecDepth 1000 in
  @[simp]
    theorem t :
      True := trivial

end CheckFixtures.BadWrapped
