module
public import ConsensusLean.Spec.Problem.Basic

@[expose] public section

/-! # Protocol profiles (L0): which capabilities a protocol provides

A profile names a standard set of provided capabilities:

* `ebbAndFlow`: final, stable and available;
* `bft`: final only;
* `available`: available and stable, no final.

`Profile.Matches p O` says that the schema `O` provides exactly the capabilities of `p`: a
capability of `p` is provided and every other capability is not. Only capabilities are compared, not
the physical outputs: the output type `O.Id` is not fixed, two capabilities may be served by one
output (aliasing; the Goldilocks confirmed output serves both available and stable), and identifiers
that serve no capability are allowed. The three profiles are not exhaustive: a schema with an
available output only, or with a final and an available output but no stable one, matches none of
them, and `CorrectProtocol` and `ShapeObligations` apply to it unchanged.

A profile is a label, not a property set: it adds no claim about any capability and removes none.
What is claimed of each provided capability is the fixed table `Behaviour` (`CorrectProtocol.lean`),
which selects its rows from the schema alone; a profile only names the capability set a protocol is
reviewed as. -/

namespace Consensus

/-- The standard capability sets a protocol may be reviewed as. -/
inductive Profile where
  /-- Final, stable and available. -/
  | ebbAndFlow
  /-- Final only. -/
  | bft
  /-- Available and stable, no final. -/
  | available
  deriving DecidableEq, Repr

/-- The capabilities a profile provides. -/
def Profile.provides : Profile → Capability → Bool
  | .ebbAndFlow, _ => true
  | .bft, .final => true
  | .bft, .stable => false
  | .bft, .available => false
  | .available, .final => false
  | .available, .stable => true
  | .available, .available => true

/-- The schema `O` provides exactly the capabilities of `p`: each capability is provided iff `p`
provides it. Outputs may alias, and the output type is not fixed. -/
def Profile.Matches (p : Profile) (O : OutputSchema) : Prop :=
  ∀ cap, (O.output cap).isSome = p.provides cap

end Consensus

end
