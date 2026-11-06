module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! # Goldilocks under growing faults (statements)

The growing-fault endpoint and headline of the Goldilocks family, at the contract of
`Statements/Obligations` (`goldilocksContract A (contract_coefficients S A)`, whose growing-fault
numbers are the sleepy look-ahead `5`, the cohort look-ahead `0` and the proposer hold `1`). Stated,
not yet certified: the comparator certifies `MeetsObligationsConstant` and
`GoldilocksCorrectConstant` (`Statements/Obligations`) until these are proved; this module is then
merged into `Statements/Obligations`.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks
open AsChainShape
open Blocks Shape

/-- **Goldilocks meets the obligations**, the concrete endpoint: for every setup and every
assumption set (the FG delay in slots `fgSlots ≥ 2` and the timeout `3·fgSlots ≤ δ_t`), the
Goldilocks family meets the obligations as an Ebb-and-Flow protocol (its schema provides exactly
the final, stable and available capabilities; available and stable are both the `confirmed`
output) at the contract `goldilocksContract A (contract_coefficients S A)`, every number of which
is fixed in `Statements/Obligations`. -/
def MeetsObligations : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S),
    ShapeObligationsAs .ebbAndFlow (goldilocks S) (goldilocksContract A (contract_coefficients S A))

/-- **Goldilocks is correct**, the headline statement: for every setup `S`, every assumption set
`A` (the FG delay in slots `fgSlots ≥ 2` and the timeout `3·fgSlots ≤ δ_t`) and every finite
validator type `V`, the Goldilocks family, compiled and run by the general execution model
(`sysOf schema (compiled (goldilocks S)) V`, with progress read by `shapeProgress`), is an L0
`CorrectProtocol` at the contract `goldilocksContract A (contract_coefficients S A)`. It composes
`MeetsObligations` with the review statement `ObligationsSufficient`; it has their parameters and
no further hypothesis. -/
def GoldilocksCorrect : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    CorrectProtocol (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V) (goldilocksContract A (contract_coefficients S A))

end Consensus.Goldilocks

end
