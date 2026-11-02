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
  review theorems, of their source theorems and of the solution's instance milestone theorems
  (whose statements are the milestone definitions themselves, so they need no pair); an
  unfinished proof or a new axiom changes the message and fails the build. -/

-- `#guard_msgs in #print axioms` puts the command off column 0; the linter's warning would
-- otherwise be part of the guarded messages; the pinned messages are longer than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

open Lean Meta

/-! ## Statements are the source theorems' types (alpha-equality, same binder kinds) -/

#guard_msgs in
run_meta do
  let pairs := [
    (``Consensus.Review.AcceptedGood, ``Consensus.Shape.Accepted.good),
    (``Consensus.Review.RegimesRealizable, ``Consensus.Shape.regimes_realizable),
    (``Consensus.Review.LogFaithful, ``Consensus.Model.sysOf_log_faithful),
    (``Consensus.Review.HeldIffServed, ``Consensus.Model.Run.held_iff_served)]
  Consensus.ReviewGuard.check pairs
  Consensus.ReviewGuard.checkComplete `ConsensusLean.Statements.Review pairs

/-! ## Axiom pins: the review theorems -/

/-- info: 'Consensus.Review.acceptedGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.acceptedGood

/-- info: 'Consensus.Review.regimesRealizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.regimesRealizable

/-- info: 'Consensus.Review.logFaithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.logFaithful

/-- info: 'Consensus.Review.heldIffServed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.heldIffServed

/-- info: 'Consensus.Goldilocks.FG.fGSafety' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.FG.fGSafety

/-- info: 'Consensus.Goldilocks.SA.aCSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCSteps

/-- info: 'Consensus.Goldilocks.Store.fGStoreLocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreLocal

/-- info: 'Consensus.Goldilocks.Store.fGStoreTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreTrace

/-- info: 'Consensus.Goldilocks.SA.aCBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.SA.aCBase

/-- info: 'Consensus.Goldilocks.localRunReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.localRunReachable

/-- info: 'Consensus.Goldilocks.Store.fGStoreService' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Store.fGStoreService

/-- info: 'Consensus.Goldilocks.Compose.composeInterfaceStatements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.composeInterfaceStatements

/-- info: 'Consensus.Goldilocks.Compose.composeNodeStatements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.composeNodeStatements

/-- info: 'Consensus.Goldilocks.Compose.eventOrder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.eventOrder

/-- info: 'Consensus.Goldilocks.Compose.readyImpliesJoined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.readyImpliesJoined

/-- info: 'Consensus.Goldilocks.Compose.aCProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.aCProjection

/-- info: 'Consensus.Goldilocks.Compose.fGProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.fGProjection

/-- info: 'Consensus.Goldilocks.Compose.goldilocksACProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.goldilocksACProjection

/-- info: 'Consensus.Goldilocks.Compose.groupStatesReachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.groupStatesReachable

/-- info: 'Consensus.Goldilocks.Compose.syncProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.syncProjection

/-- info: 'Consensus.Goldilocks.Compose.joinedProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.joinedProjection

/-- info: 'Consensus.Goldilocks.Compose.honestFastConfirmationsPersist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.honestFastConfirmationsPersist

/-- info: 'Consensus.Goldilocks.Compose.recentSourceNextVote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.recentSourceNextVote

/-- info: 'Consensus.Goldilocks.Regimes.outputsNested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.outputsNested

/-- info: 'Consensus.Goldilocks.Regimes.finalizedMonotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.finalizedMonotone

/-- info: 'Consensus.Goldilocks.Regimes.outputsValid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.outputsValid

/-- info: 'Consensus.Goldilocks.Regimes.finalAccountable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.finalAccountable

/-- info: 'Consensus.Goldilocks.Regimes.nonFraming' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.nonFraming

/-- info: 'Consensus.Goldilocks.Regimes.finalizedSafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.finalizedSafe

/-- info: 'Consensus.Goldilocks.Regimes.sleepySafe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.sleepySafe

/-- info: 'Consensus.Goldilocks.Regimes.sleepySafePrefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.sleepySafePrefix

/-- info: 'Consensus.Goldilocks.Regimes.includeSleepy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.includeSleepy

/-- info: 'Consensus.Goldilocks.Regimes.growSleepy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Regimes.growSleepy

/-- info: 'Consensus.Goldilocks.Compose.headExtendsRecord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.headExtendsRecord

/-- info: 'Consensus.Goldilocks.Compose.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Compose.inclusion

/-- info: 'Consensus.Goldilocks.Refinement.acceptedEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Refinement.acceptedEndpoint

/-! ## Axiom pins: the source theorems -/

/-- info: 'Consensus.Shape.Accepted.good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Shape.Accepted.good

/-- info: 'Consensus.Shape.regimes_realizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Shape.regimes_realizable

/-- info: 'Consensus.Model.sysOf_log_faithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.sysOf_log_faithful

/-- info: 'Consensus.Model.Run.held_iff_served' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Model.Run.held_iff_served

end
