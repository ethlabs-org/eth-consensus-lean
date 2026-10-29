import ConsensusTests.ReviewGuard

/-! Negative fixture for `Consensus.ReviewGuard.checkComplete` (the pair-completeness check of
`ConsensusTests/ReviewAxioms.lean`): the namespace has two statements but only `Stmt` has a pair,
so the `run_meta` throws, `#guard_msgs` (expecting no message) fails, and `lake env lean` exits
nonzero with "no review pair for [CheckFixtures.ReviewCompleteBad.Extra]". -/

namespace CheckFixtures.ReviewCompleteBad

def Stmt : Prop := ∀ (n : Nat), n = n

def Extra : Prop := True

theorem src : ∀ (n : Nat), n = n := fun _ => rfl

end CheckFixtures.ReviewCompleteBad

#guard_msgs in
run_meta do
  let pairs := [(``CheckFixtures.ReviewCompleteBad.Stmt, ``CheckFixtures.ReviewCompleteBad.src)]
  Consensus.ReviewGuard.check pairs
  Consensus.ReviewGuard.checkComplete `CheckFixtures.ReviewCompleteBad pairs
