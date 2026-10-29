module
public import CheckFixtures.HiddenOpaqueDep

@[expose] public section

/-! A definition in a proof module (a `Proofs` component): check-decls exempts it from
reaches-opaque. -/

namespace CheckFixtures.HiddenOpaque.Proofs.Helper

def helper : Nat := CheckFixtures.HiddenOpaqueDep.secret

end CheckFixtures.HiddenOpaque.Proofs.Helper
