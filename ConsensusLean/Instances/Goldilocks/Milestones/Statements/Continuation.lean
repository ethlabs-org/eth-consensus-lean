module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Continuation
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations

@[expose] public section

/-! # Goldilocks continues after healing under corruption growth (statement, untrusted)

`GoldilocksContinues`: for every setup `S`, every assumption set `A` and every finite validator
type `V`, the Goldilocks family, compiled and run by the general execution model, meets
`Continues` (`Milestones/Spec/Continuation`) at the contract of the headline
(`goldilocksContract A (contract_coefficients S A)`): its available and stable outputs stay safe
and live on runs that are healthy up to a hand-over time at or after the heal point and only
sleepy afterwards, the corruption growing from below `n/3` to below `n/2`, with fewer than a
third of the validators convicted by honestly seen evidence. It is not part of
`GoldilocksCorrect`, and no Challenge statement reaches it: an untrusted milestone statement,
outside the spec snapshots.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks
open AsChainShape
open Blocks Shape

/-- **Goldilocks continues after healing**: the side property `Continues` of the compiled family
at the headline contract, for every setup, assumption set and finite validator type. -/
def GoldilocksContinues : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    Continues (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V) (goldilocksContract A (contract_coefficients S A))

end Consensus.Goldilocks

end
