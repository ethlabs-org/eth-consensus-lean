module
public import ConsensusLean.Comparison.Defaults
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! # Slice 0 defaults for Goldilocks (statements)

The composite Goldilocks instances of the Slice 0 defaults: at every setup, assumption set,
validator type, capability and outer gap, the compiled Goldilocks system at the endpoint's contract
`goldilocksContract A (contract_coefficients S A)` has the default heal profile
(`hsDefault`, `hlDefault`, `latDefault`) and the default transaction latency (`txLatDefault`).
They follow from the headline `GoldilocksCorrect` and the generic defaults. -/

namespace Consensus.Goldilocks.Comparison

open AsChainShape Blocks Shape Consensus.Comparison

/-- **Goldilocks' Slice 0 heal defaults**: the default heal profile of the compiled Goldilocks
system at the endpoint's contract, at every capability and outer gap `X`. -/
def GoldilocksHealDefault0 : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]
    (cap : Capability) (X : ℕ+),
    HealProfile0 (Model.sysOf schema (compiled (goldilocks S)) V) (shapeProgress (goldilocks S) V)
      (goldilocksContract A (contract_coefficients S A)) cap X
      (hsDefault (goldilocksContract A (contract_coefficients S A)) cap X)
      (hlDefault (goldilocksContract A (contract_coefficients S A)) cap X)
      (latDefault (goldilocksContract A (contract_coefficients S A)) cap X)

/-- **Goldilocks' Slice 0 transaction latency default** at the endpoint's contract, at every
capability and outer gap `X`. -/
def GoldilocksTxLatencyDefault0 : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]
    (cap : Capability) (X : ℕ+),
    TxLatency0 (Model.sysOf schema (compiled (goldilocks S)) V) (shapeProgress (goldilocks S) V)
      (goldilocksContract A (contract_coefficients S A)) cap X
      (txLatDefault V (goldilocksContract A (contract_coefficients S A)) cap X)

end Consensus.Goldilocks.Comparison

end
