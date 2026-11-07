module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Proposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Inclusion

public section

/-! # Pending interface of the growing query suppliers

`healthy_confirmed_supply_at`, the healthy selected-proposal service the confirmed query supplier
consumes, home `Lemmas/Growing/Obligations/Healthy`. The proved engine and node lemmas the
suppliers read (`Sleepy/Service/Inclusion`, `Sleepy/Engine/{Transport,Reads,Inclusion}`) are
re-exported.

Each theorem here is an open `sorry`; this module is deleted when the home module lands. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape
open Consensus.Model (pubOf)

section Healthy

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **Healthy selected-proposal service under growing faults**: a confirmed proposal after the
heal point, in the confirmed read of every node ready at the deadline. -/
theorem healthy_confirmed_supply_at (Q : ConfirmedQueryAt S A V)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) Q.gst Q.run)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index ((Sys (goldilocks S) V).ready (K S A) Q.gst Q.run)
      Q.run.2.horizon Q.run)
    (ht : (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst Q.run ≤ Q.query) :
    ∃ P : ConfirmedProposalAt Q,
      ∀ y j, Regimes.Growing.ReadyAt Q.trace Q.keys Q.duration y Q.deadline →
        Regimes.CutAfter Q.trace j Q.deadline →
        Anc (Q.trace.HonestBlocksAt Q.keys) P.block
          (Regimes.readAfter Q.trace y j Q.deadline) := by
  sorry

end Healthy

end Consensus.Goldilocks.Obligations.Growing

end
