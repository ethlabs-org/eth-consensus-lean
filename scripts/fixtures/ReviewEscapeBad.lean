module
public import CheckFixtures.ReviewEscape
import all CheckFixtures.ReviewEscape
public meta import ConsensusTests.ReviewGuard

/-! Negative fixture for `Consensus.ReviewGuard.checkComplete` on an imported module, set up like
`ConsensusTests/ReviewAxioms.lean` (`import all` for the private statements): only `Stmt` of
`CheckFixtures.ReviewEscape` (lib `CheckFixtures`, built first) has a pair, so the `run_meta`
throws, `#guard_msgs` (expecting no message) fails, and `lake env lean` exits nonzero with "no
review pair for [CheckFixtures.Elsewhere.Extra, CheckFixtures.ReviewEscape._Extra,
CheckFixtures.ReviewEscape.eq_1,
_private.CheckFixtures.ReviewEscape.0.CheckFixtures.ReviewEscape.Priv]" (one line): a statement
in another namespace, with an internal-looking name or `private` is still listed. -/

#guard_msgs in
run_meta do
  let pairs := [(``CheckFixtures.ReviewEscape.Stmt, ``CheckFixtures.ReviewEscape.src)]
  Consensus.ReviewGuard.check pairs
  Consensus.ReviewGuard.checkComplete `CheckFixtures.ReviewEscape pairs
