module

@[expose] public section

/-! The opaque constant for `HiddenOpaque`, outside its check-decls scope (as a dependency's
would be). -/

namespace CheckFixtures.HiddenOpaqueDep

opaque secret : Nat

end CheckFixtures.HiddenOpaqueDep
