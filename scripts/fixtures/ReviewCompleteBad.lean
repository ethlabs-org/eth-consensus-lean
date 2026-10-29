import ConsensusLeanTest.ReviewGuard

/-! Negative fixture for `Consensus.ReviewGuard.checkComplete` (the pair-completeness check of
`ConsensusLeanTest/ReviewAxioms.lean`) on the current file: only `Stmt` has a pair; the other
statements sit in another namespace, have names that `Name.isInternalDetail` treats as internal
(`eq_1`, `_Extra`) or are `private`. So the `run_meta` throws, `#guard_msgs` (expecting no
message) fails, and `lake env lean` exits nonzero with "no review pair for
[CheckFixtures.Elsewhere.Extra, CheckFixtures.ReviewCompleteBad.Extra,
CheckFixtures.ReviewCompleteBad._Extra, CheckFixtures.ReviewCompleteBad.eq_1,
_private.scripts.fixtures.ReviewCompleteBad.0.CheckFixtures.ReviewCompleteBad.Priv]" (one line;
`scripts.fixtures.ReviewCompleteBad` is the main module that `lake env lean` derives from the path
`scripts/fixtures/ReviewCompleteBad.lean`). -/

namespace CheckFixtures.ReviewCompleteBad

def Stmt : Prop := ∀ (n : Nat), n = n

def Extra : Prop := True

def eq_1 : Prop := True

def _Extra : Prop := True

private def Priv : Prop := True

theorem src : ∀ (n : Nat), n = n := fun _ => rfl

end CheckFixtures.ReviewCompleteBad

namespace CheckFixtures.Elsewhere

def Extra : Prop := True

end CheckFixtures.Elsewhere

#guard_msgs in
run_meta do
  let pairs := [(``CheckFixtures.ReviewCompleteBad.Stmt, ``CheckFixtures.ReviewCompleteBad.src)]
  Consensus.ReviewGuard.check pairs
  Consensus.ReviewGuard.checkComplete (← Lean.getEnv).mainModule pairs
