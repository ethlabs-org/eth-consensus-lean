module
public import ConsensusShape.ProgressFit
public import ConsensusShape.Realizable

@[expose] public section

/-! # Acceptance (L2): the review endpoint

`Accepted F K` is what an instance must establish: its shape claims
(`ShapeClaims`, proved by the protocol), admissible numbers
(`Params.Admissible`: thresholds no stronger than standard), a served ledger
(`OutputSchema.Serves`: a final output, or an available one), and progress
requirements that fit the skeleton (`ProgressFits`: a recurrence needs
one proposer per slot), and tolerate arbitrary numbers of validators not ready.

`Accepted.good` gives the full L0 `Good` of the compiled system, for every
finite validator type: `Accepted.behaviour` (the refinement of the shape
claims), the model's adequacy (`sysOf_adequate`, an L1 theorem, independent
of the claims) and the generic `regimes_realizable` (from admissibility,
progress fit and tolerance). Its corollary `Accepted.activeService` (a final
or available output actively serves transactions) is in `Service.lean`. -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- An accepted instance: shape claims, admissible numbers, a served ledger,
and progress requirements that fit the skeleton and tolerate arbitrary numbers
of validators not ready. -/
structure Accepted (F : ShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- The numbers are admissible. -/
  admissible : K.params.Admissible
  /-- A final or an available output is provided. -/
  serves : O.Serves
  /-- The progress requirements fit the skeleton. -/
  progressFits : ProgressFits K F
  /-- Every provided output tolerates arbitrary numbers of validators not ready. -/
  progressTolerant : ProgressTolerant O K

/-- An accepted instance has the L0 behaviour for every finite validator
type. -/
theorem Accepted.behaviour {F : ShapeFamily O Info} {K : Contract ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Behaviour (sysOf O (compiled F) V) (shapeProgress F V) K :=
  refinement F K V h.claims h.admissible h.serves

/-- An accepted instance is a good protocol (L0 `Good`) for every finite
validator type. -/
theorem Accepted.good {F : ShapeFamily O Info} {K : Contract ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Good (sysOf O (compiled F) V) (shapeProgress F V) K :=
  ⟨h.behaviour V, Model.sysOf_adequate _ rfl,
    fun hn =>
      (regimes_realizable F K h.admissible h.progressFits h.progressTolerant V hn).toRealizable⟩

end Consensus.Shape

end
