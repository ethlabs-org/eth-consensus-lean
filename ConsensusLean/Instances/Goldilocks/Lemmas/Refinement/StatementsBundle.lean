module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Simulation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Chains
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Evidence

public section

/-! # Goldilocks milestone Refinement, assembled

`RefinementStatements` (`Lemmas/Refinement/Interface`) from its six proved fields: the engine
simulates the node (`engineSimulatesNode`, `Simulation`), reads are outputs (`readIsOut`,
`Chains`), collision transport (`noCollTransport`, `Transport`), the conflict characterisation
(`conflicts_iff`, `Shape`), evidence in view (`evidenceInView`, `Evidence`) and finalized
accountability (`finalizedAccountable`, `Transport`). -/

namespace Consensus.Goldilocks.Refinement

/-- **The Refinement statements** for every setup and validator set. -/
theorem refinement_statements (V : Type) [Fintype V] [DecidableEq V] (S : Setup) :
    RefinementStatements V S where
  engineSimulatesNode := engineSimulatesNode V S
  readIsOut := readIsOut V S
  noCollTransport := noCollTransport V S
  conflictsIff := conflicts_iff
  evidenceInView := evidenceInView V S
  finalizedAccountable := finalizedAccountable V S

end Consensus.Goldilocks.Refinement

end
