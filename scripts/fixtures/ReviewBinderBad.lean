import ConsensusLeanTest.ReviewGuard

/-! Negative fixture for the binder-kind half of the statement guard of
`ConsensusLeanTest/ReviewAxioms.lean` (same `Consensus.ReviewGuard.check`): `Stmt` and the type of
`src` are alpha-equal (`Expr` `==` ignores binder annotations) but `Stmt` binds `n` implicitly and
`src` explicitly, so the `run_meta` throws, `#guard_msgs` (expecting no message) fails, and
`lake env lean` exits nonzero with "does not have the binder kinds". The matching positive case
(binder names differ, kinds agree) is `ReviewGuardGood.lean`, which must exit 0. -/

namespace CheckFixtures.ReviewBinderBad

def Stmt : Prop := ∀ {n : Nat}, n = n

theorem src : ∀ (n : Nat), n = n := fun _ => rfl

end CheckFixtures.ReviewBinderBad

#guard_msgs in
run_meta Consensus.ReviewGuard.check [
    (``CheckFixtures.ReviewBinderBad.Stmt, ``CheckFixtures.ReviewBinderBad.src)]
