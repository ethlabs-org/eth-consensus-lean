module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Queue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps

public section

/-! # Growing-fault proposals are releasable

The form of `Simulation/Steps` under growing faults: proposal releasability
(`proposal_releasable_at`). -/

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
    (info : Info) (cs : List (Wire (Fintype.card V) S.vote))
    (hs : 0 < s) (hone : (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs])
    (hselected : rho.ownKey v ∈ rho.sel (.proposer s))
    (hprop : (propose (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) s).2 =
      some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure (atProposal S rho v (rho.stateBefore i v) t).seen :=
  proposal_releasable S rho hn hv v i t he s par info cs hs hone hselected hprop

end Engine

end Consensus.Goldilocks.Simulation

end
