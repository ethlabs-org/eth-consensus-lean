module
public import ConsensusLean.Spec.Shape.Claims
public import ConsensusLean.Spec.Shape.ProgressFit
public import ConsensusLean.Spec.Shape.Active
public import ConsensusLean.Spec.Problem.Profile
public import ConsensusLean.Spec.Model.Guard

@[expose] public section

/-! # Shape obligations (L2): the review endpoint

`ShapeObligations F K` is what an instance must establish: its shape claims
(`ShapeClaims`, proved by the protocol), admissible numbers
(`Params.Admissible`: realizable fractions, not necessarily optimal), a served ledger
(`OutputSchema.Serves`: a final output, or an available one), and progress
requirements that fit the skeleton (`ProgressFits`: a recurrence needs
one proposer per slot), and tolerate arbitrary numbers of validators not
ready and a bad proposer slot in every window (`ProgressTolerant`), and its own
slashing protection (`GuardIdleAlways`: on every valid run, no own-signed candidate of an
honest node conflicts with itself or with an own-signed object the node has seen; the engine
has no guard, so this is the protocol's non-framing).

`ShapeObligations.correct` (in `ConsensusLean/Main.lean`) gives the full L0
`CorrectProtocol` of the compiled system, for every
finite validator type: `ShapeObligations.behaviour` (the refinement of the shape
claims), the model's adequacy (`sysOf_adequate`, an L1 theorem, independent
of the claims), non-framing from `GuardIdleAlways`, and the generic `regimes_realizable`
(from admissibility, progress fit and tolerance). Its corollary
`ShapeObligations.activeService` (a final or available output actively serves transactions) is in
`ConsensusLean/Main.lean`.

`ShapeObligationsAs p F K` is the same obligations under a profile label: the schema provides
exactly the capabilities of `p` (`Profile.Matches`, `Spec/Problem/Profile`) and `F` meets
`ShapeObligations F K`. Beyond fixing the capability set, the label adds no obligation and drops
none: `ShapeObligations` and `CorrectProtocol` already read the provided capabilities from the
schema. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- **The protocol's own slashing protection**: for every finite validator type, on every valid
run of the compiled family, slashing protection never refuses a candidate
(`Model.Run.GuardIdle`): honest code never signs an object that conflicts with itself or with an
own-signed object its node has seen. -/
def GuardIdleAlways (F : ChainShapeFamily O Info) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V], (Sys F V).HoldsAlways fun r => r.2.GuardIdle

/-- The shape obligations of an instance: shape claims, admissible numbers, a served ledger,
progress requirements that fit the skeleton and tolerate arbitrary numbers
of validators not ready and a bad proposer slot in every window, and the protocol's own
slashing protection. -/
structure ShapeObligations (F : ChainShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- The numbers are admissible. -/
  admissible : K.params.Admissible
  /-- A final or an available output is provided. -/
  serves : O.Serves
  /-- The progress requirements fit the skeleton. -/
  progressFits : ProgressFits K F
  /-- Every provided output tolerates arbitrary numbers of validators not
  ready and a bad proposer slot in every window. -/
  progressTolerant : ProgressTolerant O K
  /-- Slashing protection never fires on a valid run (non-framing). -/
  guardIdle : GuardIdleAlways F

/-- The shape obligations under the profile label `p`: the schema provides exactly the
capabilities of `p` (outputs may alias), and the family meets `ShapeObligations F K`. -/
def ShapeObligationsAs (p : Profile) (F : ChainShapeFamily O Info) (K : Contract ProgressReq) :
    Prop :=
  p.Matches O ∧ ShapeObligations F K

end Consensus.Shape

end
