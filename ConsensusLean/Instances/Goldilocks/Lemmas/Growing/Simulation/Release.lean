module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick

public section

/-! # Releasability at a growing-fault engine tick

The proposal closure premise needed by the static release analysis is local to the
scheduled engine tick. It follows from the dynamic inventory, not a static global run.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A proposal selected at an actual tick carries only objects already available there. -/
theorem preNode_releasable_at (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (he : rho.events[i]? = some (.tick v t)) :
    ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
      rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen := by
  rw [preNode_eq_atProposal]
  exact fun s hs hone hsel par info cs h =>
    proposal_releasable_at S rho hn hv v i t he s par info cs hs hone hsel h

end Consensus.Goldilocks.Simulation
