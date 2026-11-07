module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Fields
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete

public section

/-! # The growing-fault endpoint

`meetsObligations_claims_growing`: the nine chain-level claims of `ShapeClaimsAt` on every run,
from `Concrete/Fields`; `meetsObligations_growing`: the shape obligations, with the admissible
numbers, the served ledger, progress fit and tolerance of the constant-fault endpoint (they read no
faults). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Obligations
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S)

/-- The nine chain-level claims on every run. -/
theorem meetsObligations_claims_growing :
    ∀ (V : Type) [Fintype V] [DecidableEq V], ShapeClaimsAt (goldilocks S) (K S A) V := by
  intro V _ _
  exact {
    outputValid := meetsObligations_outputValid_growing S V
    nested := meetsObligations_nested_growing S V
    finalMonotone := meetsObligations_finalMonotone_growing S V
    finalAccountable := meetsObligations_finalAccountable_growing S A V
    healthyLive := meetsObligations_healthyLive_growing S A V
    sleepySafe := meetsObligations_sleepySafe_growing S A V
    sleepyLive := meetsObligations_sleepyLive_growing S A V
    healedSafe := meetsObligations_healedSafe_growing S A V
    persists := meetsObligations_persists_growing S A V }

/-- **The growing-fault endpoint** at the coefficients `contract_coefficients S A`. -/
theorem meetsObligations_growing : ShapeObligations (goldilocks S) (K S A) :=
  { claims := meetsObligations_claims_growing S A
    admissible := meetsObligations_admissible S A
    serves := by simp [OutputSchema.Serves, schema]
    progressFits := meetsObligations_progressFits S A
    progressTolerant := meetsObligations_progressTolerant S A }

end Consensus.Goldilocks.Obligations.Growing

end
