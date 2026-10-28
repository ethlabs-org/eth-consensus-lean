module
public import ConsensusShape.Realizable

@[expose] public section

/-! # Acceptance (L2): the review endpoint

`Accepted F K` is what an instance must establish: its shape claims
(`ShapeClaims`, proved by the protocol), admissible numbers
(`Params.Admissible`: thresholds no stronger than standard), a served ledger
(`OutputSchema.Serves`: a final output, or an available one), and progress
requirements that fit the skeleton (`Contract.ProgressFits`: a recurrence needs
one proposer per slot).

`Accepted.behaviour` gives the L0 `Behaviour` of the compiled system and
`Accepted.adequate` its L0 adequacy (proved once for the model). The
realizability part of `Good` is the generic `regimes_realizable` (stage 4,
`Accepted.good`). -/

namespace Consensus.Shape

open Blocks
open Consensus.Model (pubOf sysOf)

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Encodable Info]

/-- A progress requirement fits a skeleton: a recurrence needs one proposer
per slot (`.sized 1`, independent of the population: with every key selected,
a faulty validator is always among the proposers and recurrence has no witness,
`allProposers_no_witness`); a bound on the validators not ready fits every
skeleton. -/
def _root_.Consensus.Blocks.ProgressReq.Fits {n : Nat} (sk : Skeleton n) : ProgressReq → Prop
  | .recur _ => sk.proposerSel = .sized 1
  | .notReadyAtMost _ => True

/-- Every progress requirement of the contract fits the family's skeleton at
every public parameter. -/
def _root_.Consensus.Contract.ProgressFits (K : Contract O ProgressReq)
    (F : ShapeFamily O Info) : Prop :=
  ∀ cap i pub, (K.progress cap i).Fits (F pub).skel

/-- An accepted instance: shape claims, admissible numbers, a served ledger,
and progress requirements that fit the skeleton. -/
structure Accepted (F : ShapeFamily O Info) (K : Contract O ProgressReq) : Prop where
  /-- The chain-level claims (proved by the protocol). -/
  claims : ShapeClaims F K
  /-- The numbers are admissible. -/
  admissible : K.params.Admissible
  /-- A final or an available output is provided. -/
  serves : O.Serves
  /-- The progress requirements fit the skeleton. -/
  progressFits : K.ProgressFits F

/-- An accepted instance has the L0 behaviour for every finite validator
type. -/
theorem Accepted.behaviour {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    Behaviour (sysOf O (compiled F) V) (shapeProgress F V) K :=
  refinement F K V h.claims h.admissible h.serves

/-- The compiled system of every family is adequate for the shape's progress
reader (an L1 theorem; it does not depend on the claims). -/
theorem Accepted.adequate {F : ShapeFamily O Info} {K : Contract O ProgressReq}
    (_h : Accepted F K) (V : Type) [Fintype V] [DecidableEq V] :
    (sysOf O (compiled F) V).Adequate (shapeProgress F V) :=
  Model.sysOf_adequate _ rfl

end Consensus.Shape

end
