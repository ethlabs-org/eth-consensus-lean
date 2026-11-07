module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Steps

public section

/-! # Proposal acceptance at a tick under growing faults

The growing-fault form of `tick_proposal_acceptance_queued`, without a constant-fault or
honesty premise: the tick is an actual event, hence an honest one, and the carried objects of
its proposal are available from the dynamic inventory (`proposal_releasable_at`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- At a scheduled tick, an accepting proposal cut queues its exact wrapper. Coverage comes from
the engine prefix, carried-object readiness from the tick's own inventory. -/
theorem tick_proposal_acceptance_queued_at (hv : rho.ExecutionValid)
    (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node
      t (encodeTxs (mempool rho.inbox v t)) .proposal).2) :
    ∃ p, forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
      pendingWrappers (shapeOf S hn
        (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1) := by
  have hsel := poll_selected S rho hv v
  have hself : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).self =
      rho.ownKey v := by
    rw [atProposal_self S rho hn v _ t hsel]
    simpa only [stateAt_eq] using self_eq_ownKey S rho hn v i
  have hnow := atProposal_now S rho hn v (rho.stateBefore i v) t hsel
  have hcover : WrappersCover
      (propose (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) s).1 := by
    have hc : WrappersCover (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) := by
      rw [atProposal_eq]
      exact tick_duty_prefix_wrappersCover S rho hn v i t _
    unfold propose
    dsimp only
    split <;> simpa only [wrappersCover_iff, Node.acProposal] using hc
  obtain ⟨p, hp⟩ := dutyStep_propose_acceptance_queued S rho hn v _ s hs
    (selValid_proposer S rho hn hv.selValid s) hself
    (by rw [hnow, ht]; exact slotOf_slotTime _ s) (hnow.trans ht)
    (fun hselected par info cs hprop =>
      proposal_releasable_at S rho hn hv v i t he s par info cs hs hone hselected hprop)
    hcover B (by simpa only [hnow, atProposal_mempool] using ha)
  exact ⟨p, by simpa only [hself, hnow] using hp⟩

end Consensus.Goldilocks.Simulation

end
