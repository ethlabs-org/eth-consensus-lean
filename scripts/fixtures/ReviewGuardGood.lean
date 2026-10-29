import ConsensusLeanTest.ReviewGuard

/-! Positive fixture for `Consensus.ReviewGuard` (the guard of
`ConsensusLeanTest/ReviewAxioms.lean`): `lake env lean` must exit 0 with no message, so an
over-strict guard cannot pass the negative fixtures (`ReviewEqBad`, `ReviewBinderBad`,
`ReviewCompleteBad`, `ReviewEscapeBad`) unnoticed.
`Good` differs from the type of `src` only in the binder name (`m` vs `n`), with the same kind,
and the file's only statement has a pair. -/

namespace CheckFixtures.ReviewGuardGood

def Good : Prop := ∀ (m : Nat), m = m

theorem src : ∀ (n : Nat), n = n := fun _ => rfl

end CheckFixtures.ReviewGuardGood

#guard_msgs in
run_meta do
  let pairs := [(``CheckFixtures.ReviewGuardGood.Good, ``CheckFixtures.ReviewGuardGood.src)]
  Consensus.ReviewGuard.check pairs
  Consensus.ReviewGuard.checkComplete (← Lean.getEnv).mainModule pairs
