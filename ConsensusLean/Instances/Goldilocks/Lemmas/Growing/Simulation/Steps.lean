module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Queue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps

public section

/-! # Growing-fault public ticks realize node steps

The forms of `Simulation/Steps` under growing faults, with the poll-attestation protection
`GrowingInventory.pollAttProtected` and the event's node honest at time zero
(`event_honest_zero`): proposal releasability and the node transition inside honest engine
ticks. Public-time ticks execute the node duty; non-public ticks leave the node unchanged. These
event-local facts support the simulating trace's run laws and cut-map assembly in
`Simulation/Run`. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The release guarantee applies to the selected proposal at its scheduled slot start. -/
theorem proposal_releasable_at (hv : rho.ExecutionValid)
    (v : V) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (par : ParentRef)
    (info : Info) (cs : List (Wire (Fintype.card V)))
    (hs : 0 < s) (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (hselected : rho.ownKey v ∈ rho.sel (.proposer s))
    (hprop : (propose (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) s).2 =
      some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure (atProposal S rho v (rho.stateBefore i v) t).seen :=
  proposal_releasable_of_protected S rho hn (GrowingInventory.pollAttProtected S rho hn hv) hv v
    (event_honest_zero S rho hv he) i t he s par info cs hs hone hselected hprop

/-- **`Simulates.tick`'s node step at a public time.** An engine tick of an honest node at a public
time runs the node's tick with the encoded mempool on the node state before it. -/
theorem node_of_tick_public_at (hv : rho.ExecutionValid)
    (v : V) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node =
      (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).1 :=
  node_of_tick_public_of_protected S rho hn (GrowingInventory.pollAttProtected S rho hn hv) hv v
    (event_honest_zero S rho hv he) i t he hp

end Engine

end Consensus.Goldilocks.Simulation

end
