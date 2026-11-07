module
public import ConsensusLean.Instances.Goldilocks.Statements.Growing
public import ConsensusLean.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Obligations.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Endpoint
public import ConsensusLean.Lemmas.Shape.OnRuns

public section

/-! # Growing-fault endpoint

The dynamic obligations are proved here, and dynamic correctness and the constant-fault endpoint
follow from them. Certifying these endpoints through `Solution` is a separate step; until then
the certified constant-fault endpoint uses the existing milestone proofs. The compiled proposer
hold-zero counterexample that certification of the dynamic roots requires is in place
(`ConsensusLeanTest/Goldilocks/Regimes/ProposerHold.lean`).
-/

namespace Consensus.Goldilocks.Growing

/-- The dynamic obligations endpoint, proved under growing faults. -/
theorem meets_obligations : MeetsObligations := fun S A =>
  ⟨Obligations.schema_matches_ebbAndFlow, Obligations.Growing.meetsObligations_growing S A⟩

/-- Dynamic correctness follows from the obligations endpoint. -/
theorem goldilocks_correct : GoldilocksCorrect := fun S A V =>
  Consensus.Shape.ShapeObligations.correct (meets_obligations S A).2 V

/-- The constant-fault endpoint follows from the growing-fault one. -/
theorem meetsObligationsConstant_of_growing (h : MeetsObligations) : MeetsObligationsConstant :=
  fun S A => (h S A).toOnAs _

end Consensus.Goldilocks.Growing
end
