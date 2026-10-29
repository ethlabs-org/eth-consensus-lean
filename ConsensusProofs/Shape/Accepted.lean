module
public import ConsensusSpec.Shape.Accepted
public import ConsensusProofs.Shape.Realizable

@[expose] public section

/-! # Acceptance: the theorems (L2)

`Accepted.behaviour` and `Accepted.good` for the structure `Accepted` of
`ConsensusSpec/Shape/Accepted.lean` (moved from it). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

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
