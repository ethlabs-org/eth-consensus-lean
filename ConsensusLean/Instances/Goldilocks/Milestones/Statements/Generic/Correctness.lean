module
public import ConsensusLean.Spec.Shape.Obligations

@[expose] public section

/-! # Correctness assembly, separate from local protocol obligations

This record contains the nine endpoint claims. It is not the AC supplier contract and is not
a reduction theorem. Reusing `ShapeClaims` retains `HoldsAlways` for the first three claims
and `Holds` (including the excuse alternative) for the other six, with every regime/progress
hypothesis unchanged. No implication from local obligations to these claims is asserted here.

O-CORR-ASSEMBLY: per-claim reductions need the specified AC-to-shape/engine morphism, concrete
regime conversions, the local rows and population FG contracts. The AC-to-shape relationship
is not represented by unrelated free AC and shape parameters or an arbitrary Prop callback.
O-CORR-CORRECT: the correctness edge follows the existing ShapeObligations.correct route once
all claims and the four independent non-claim inputs are supplied; it is not new evidence.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]

/-- Assembly evidence for the nine claims only; not a local AC obligation. -/
structure GenericClaims (F : ChainShapeFamily O Info) (K : Contract ProgressReq) : Prop where
  /-- All nine claims, with their existing wrappers and hypotheses. -/
  claims : ShapeClaims F K

/-- An intended unproved assembly implication. Admissibility, service, progress fit and
tolerance remain separate inputs; nine claims do not silently supply them. -/
def GenericMeetsObligations : Prop :=
  ∀ (F : ChainShapeFamily O Info) (K : Contract ProgressReq),
    GenericClaims F K → K.params.Admissible → O.Serves → ProgressFits K F →
      ProgressTolerant O K → ShapeObligations F K

end Consensus.Goldilocks.Generic

end
