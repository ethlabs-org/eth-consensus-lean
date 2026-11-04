module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Evidence

public section

/-! # Goldilocks simulation statements, assembled

`SimulationStatements` (`Lemmas/Simulation/Interface`) from its six proved fields: the engine
simulates the node (`engineSimulatesNode`, `Core`), reads are outputs (`readIsOut`,
`Chains`), collision transport (`noCollTransport`, `Transport`), the conflict characterisation
(`conflicts_iff`, `Shape`), evidence in view (`evidenceInView`, `Evidence`) and finalized
accountability (`finalizedAccountable`, `Transport`). -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

/-- **The simulation statements** for every setup and validator set. -/
theorem simulation_statements (V : Type) [Fintype V] [DecidableEq V] (S : Setup) :
    SimulationStatements V S where
  engineSimulatesNode := engineSimulatesNode V S
  readIsOut := readIsOut V S
  noCollTransport := noCollTransport V S
  conflictsIff := conflicts_iff
  evidenceInView := evidenceInView V S
  finalizedAccountable := finalizedAccountable V S

end Consensus.Goldilocks.Simulation

end
