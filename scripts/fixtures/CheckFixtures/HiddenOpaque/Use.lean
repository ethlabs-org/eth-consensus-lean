module
public import CheckFixtures.HiddenOpaque.Proofs.Helper
public import CheckFixtures.HiddenOpaque.Fmt

@[expose] public section

/-! Checked definitions that reach an opaque constant only through a definition check-decls does not
check: the exempt `helper` (`user`) and the formatting instance `fmt` (`user2`). check-decls must report
both (reaches-opaque), not treat `helper` or `fmt` as having reported it (check.sh step 3 self-test). -/

namespace CheckFixtures.HiddenOpaque.Use

def user : Nat := CheckFixtures.HiddenOpaque.Proofs.Helper.helper + 1

def user2 : String := @toString Unit CheckFixtures.HiddenOpaque.Fmt.fmt ()

end CheckFixtures.HiddenOpaque.Use
