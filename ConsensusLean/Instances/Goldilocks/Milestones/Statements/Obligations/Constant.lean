module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Spec.Shape.OnRuns

@[expose] public section

/-! # Goldilocks on constant faults (statements, untrusted)

The obligations endpoint and the headline on the runs whose faults do not grow, at the contract
`goldilocksContract A (contract_coefficients S A)` of `Statements/Obligations`: no longer comparator
roots, they follow from the growing-fault pair (`meetsObligationsConstant_of_growing`) and are
proved directly from the constant-fault milestones (`Proofs/Obligations`). Rejection tests on the
static adversary are stated at this class of runs (`docs/decisions.md` §"Adversary growth").

Statements only: no proofs here. -/

namespace Consensus.Goldilocks
open AsChainShape
open Blocks Shape

/-- **Goldilocks meets the obligations on constant faults**: for every setup and every assumption
set, the Goldilocks family meets the obligations as an Ebb-and-Flow protocol with the chain-level
claims on the runs whose faults do not grow (the static adversary) and every other obligation
unchanged, at the contract `goldilocksContract A (contract_coefficients S A)`. -/
def MeetsObligationsConstant : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S),
    ShapeObligationsOnAs .ebbAndFlow (goldilocks S)
      (goldilocksContract A (contract_coefficients S A)) fun _ p => p.ConstantFaults

/-- **Goldilocks is correct on constant faults**: for every setup, assumption set and finite
validator type, the compiled Goldilocks family is a correct protocol on the runs whose faults do not
grow (`CorrectProtocolOn`), with the adequacy and realizability (growth witnesses included) of the
whole growing-fault system. It composes `MeetsObligationsConstant` with
`Review.ObligationsSufficientOn`. -/
def GoldilocksCorrectConstant : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    CorrectProtocolOn (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V) (goldilocksContract A (contract_coefficients S A))
      fun p => p.ConstantFaults

end Consensus.Goldilocks

end
