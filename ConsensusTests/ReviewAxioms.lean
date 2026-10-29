module
public import ConsensusProofs.Review
@[expose] public section

/-! # Review pins

Pinned by the build, pattern of verified-consensus `scripts/ReviewAxioms.lean` (compiled instead of
parsed):
* each review statement of `ConsensusSpec/Statements.lean` is *the* type of its source theorem:
  a `run_meta` throws unless the statement's body is alpha-equal (`Expr` `==`) to the theorem's
  type, so a later edit of either side breaks the build here;
* each `#guard_msgs` pins the exact axiom list (`propext`, `Classical.choice`, `Quot.sound`) of the
  review theorems and of their source theorems; an unfinished proof or a new axiom changes the
  message and fails the build. -/

-- `#guard_msgs in #print axioms` puts the command off column 0; the linter's warning would
-- otherwise be part of the guarded messages; the pinned messages are longer than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

open Lean Meta

/-! ## Statements are the source theorems' types (alpha-equality) -/

#guard_msgs in
run_meta do
  for (s, t) in [(``Consensus.Review.AcceptedGood, ``Consensus.Shape.Accepted.good),
      (``Consensus.Review.RegimesRealizable, ``Consensus.Shape.regimes_realizable),
      (``Consensus.Review.LogFaithful, ``Consensus.Model.sysOf_log_faithful),
      (``Consensus.Review.HeldIffServed, ``Consensus.Model.Run.held_iff_served)] do
    let some v := (← getConstInfo s).value? | throwError "{s} is not a definition"
    unless v == (← getConstInfo t).type do
      throwError "{s} is not alpha-equal to the type of {t}"

/-! ## Axiom pins: the review theorems -/

/-- info: 'Consensus.Review.acceptedGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.acceptedGood

/-- info: 'Consensus.Review.regimesRealizable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.regimesRealizable

/-- info: 'Consensus.Review.logFaithful' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.logFaithful

/-- info: 'Consensus.Review.heldIffServed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Review.heldIffServed

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
