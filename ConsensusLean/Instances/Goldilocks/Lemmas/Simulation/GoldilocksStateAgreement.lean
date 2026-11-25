module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeStateAgreement
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsInstance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksReady
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AdmitsAtTick

public section

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Model (pubOf)
open NodeAsChainShape.CanonicalTrace (afterClock_eq engineDuty_eq envelope_eq
  engineRole_eq engineObj_eq Encoding)

variable {V : Type} [Fintype V] {E : Env V} [DecidableEq V]

/-- The Goldilocks run establishes the local replay laws; its due flag is proof-side only. -/
theorem traceEncoding_lawful (S : Setup) (hn : 1 ≤ Fintype.card V) :
    (traceEncoding (E := E) S hn).Lawful (traceDue S hn) :=
  (traceEncoding_opLaws S hn).toLawful (goldilocks_ready S hn) (goldilocks_admitsOwn S hn)

end Consensus.Goldilocks.Simulation
