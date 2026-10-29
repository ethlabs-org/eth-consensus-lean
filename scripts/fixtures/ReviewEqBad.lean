import ConsensusLeanTest.ReviewGuard

/-! Negative fixture for the statement guard of `ConsensusLeanTest/ReviewAxioms.lean` (it runs the
same `Consensus.ReviewGuard.check`): the statement `Stmt` (`2 = 2`) is not the type of `src`
(`1 = 1`), so the `run_meta` throws, `#guard_msgs` (expecting no message) fails, and
`lake env lean` exits nonzero with "is not alpha-equal". -/

namespace CheckFixtures.ReviewEqBad

def Stmt : Prop := 2 = 2

theorem src : 1 = 1 := rfl

end CheckFixtures.ReviewEqBad

#guard_msgs in
run_meta Consensus.ReviewGuard.check [
    (``CheckFixtures.ReviewEqBad.Stmt, ``CheckFixtures.ReviewEqBad.src)]
