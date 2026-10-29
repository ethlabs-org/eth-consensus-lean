module

@[expose] public section

/-! On Lean v4.35 a `local notation` still leaves persisted parser/macro entries in the module's
(private) `.olean` data, so the persisted-extension policy rejects it (`FAIL[ext]`). The plan expected
a pass here (`LocalSyntaxOk`); the policy is stricter than planned, i.e. local syntax is not allowed in
Spec modules either. -/

section
local notation "fixtureThree" => (3 : Nat)
def localResult : Nat := fixtureThree
end
