module
public import Solution
import all ConsensusLean.Statements.Review
public meta import ConsensusLeanTest.ReviewGuard
@[expose] public section

/-! # Review pins

Pinned by the build, pattern of verified-consensus `scripts/ReviewAxioms.lean` (compiled instead of
parsed):
* each review statement of `ConsensusLean/Statements/Review.lean` is *the* type of its source
  theorem: a `run_meta` (`Consensus.ReviewGuard.check`, shared with the negative fixtures) throws
  unless the statement's body is alpha-equal (`Expr` `==`) to the theorem's type with the same
  binder kinds, so a later edit of either side breaks the build here; every non-proof constant
  declared in `ConsensusLean/Statements/Review.lean`, in any namespace, `private` (hence
  `import all`) or not, must have a pair (`Consensus.ReviewGuard.checkComplete`);
* each `#guard_msgs` pins the exact axiom list (`propext`, `Classical.choice`, `Quot.sound`) of the
  review theorems, of their source theorems and of the solution's Goldilocks statements, the
  obligations endpoint `meetsObligations` and the headline `goldilocksCorrect`
  (whose statements are the milestone
  definitions themselves, so they need no pair); an unfinished proof
  or a new axiom changes the message and fails the build. The other Goldilocks milestones are
  pinned, untrusted, by `ConsensusLeanTest/MilestoneAxioms.lean`. -/

-- `#guard_msgs in #print axioms` puts the command off column 0; the linter's warning would
-- otherwise be part of the guarded messages; the pinned messages are longer than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

open Lean Meta

/-! ## Statements are the source theorems' types (alpha-equality, same binder kinds) -/

#guard_msgs in
run_meta do
  let pairs := [
    (``Consensus.Review.ObligationsSufficient, ``Consensus.Shape.ShapeObligations.correct),
    (``Consensus.Review.ObligationsSufficientOn, ``Consensus.Shape.ShapeObligationsOn.correct),
    (``Consensus.Review.RegimesRealizable, ``Consensus.Shape.regimes_realizable),
    (``Consensus.Review.LogFaithful, ``Consensus.Model.sysOf_log_faithful),
    (``Consensus.Review.HeldIffServed, ``Consensus.Model.Run.held_iff_served)]
  Consensus.ReviewGuard.check pairs
  Consensus.ReviewGuard.checkComplete `ConsensusLean.Statements.Review pairs

/-! ## Axiom pins: the review theorems -/

/-- info: 'Consensus.Review.obligationsSufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.obligationsSufficient

/-- info: 'Consensus.Review.obligationsSufficientOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.obligationsSufficientOn

/-- info: 'Consensus.Review.regimesRealizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.regimesRealizable

/-- info: 'Consensus.Review.logFaithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.logFaithful

/-- info: 'Consensus.Review.heldIffServed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.heldIffServed

/-- info: 'Consensus.Goldilocks.meetsObligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.meetsObligations

/-- info: 'Consensus.Goldilocks.goldilocksCorrect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.goldilocksCorrect

/-! ## Axiom pins: the source theorems -/

/-- info: 'Consensus.Shape.ShapeObligations.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Shape.ShapeObligations.correct

/-- info: 'Consensus.Shape.ShapeObligationsOn.correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Shape.ShapeObligationsOn.correct

/-- info: 'Consensus.Shape.regimes_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Shape.regimes_realizable

/-- info: 'Consensus.Model.sysOf_log_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.sysOf_log_faithful

/-- info: 'Consensus.Model.Run.held_iff_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.Run.held_iff_served

end
