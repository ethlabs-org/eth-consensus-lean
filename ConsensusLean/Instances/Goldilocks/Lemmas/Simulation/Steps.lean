module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue

public section

/-! # Engine proposals are releasable

Uses `Queue`'s inventories to prove proposal releasability (`proposal_releasable`): the selected
proposal at its scheduled slot start carries only objects the node has seen. The engine and trace
states agree through `CanonicalTrace.stateAgreement_all` (`EventGroups`). -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (Vote)

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The release guarantee applies to the selected proposal at its scheduled slot start. -/
theorem proposal_releasable (hv : rho.ExecutionValid)
    (v : V) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (par : ParentRef)
    (info : Info) (cs : List (Wire (Fintype.card V) S.vote))
    (hs : 0 < s) (hone : (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs])
    (hselected : rho.ownKey v ∈ rho.sel (.proposer s))
    (hprop : (propose (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) s).2 =
      some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure (atProposal S rho v (rho.stateBefore i v) t).seen := by
  apply scheduled_proposal_releasable S rho hn hv (i := i) (p := 3) (t := t)
    (s := s)
    (hprop := hprop)
  rw [engineProposalAt_iff]
  refine ⟨he, hv.tick_awake v t (List.mem_of_getElem? he), hs, ?_, hselected, ?_⟩
  · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1]
    simp only [dutiesInit, hone]
    rfl
  · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1, atProposal_eq]
    simp only [dutiesInit, hone]
    rfl

end Engine

end Consensus.Goldilocks.Simulation

end
