module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Queue

public section

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The release guarantee applies to the selected proposal at its scheduled slot start. -/
theorem proposal_releasable (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (par : ParentRef)
    (info : Info) (cs : List (Wire (Fintype.card V)))
    (hs : 0 < s) (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (hselected : rho.ownKey v ∈ rho.sel (.proposer s))
    (hprop : (propose (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) s).2 =
      some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure (atProposal S rho v (rho.stateBefore i v) t).seen := by
  apply scheduled_proposal_releasable S rho hn hv hv' (i := i) (p := 3) (t := t) (s := s)
    (hprop := hprop)
  rw [engineProposalAt_iff]
  refine ⟨he, hv.tick_awake v t (List.mem_of_getElem? he), hs, ?_, hselected, ?_⟩
  · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1]
    simp only [dutiesInit, hone]
    rfl
  · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1, atProposal_eq]
    simp only [dutiesInit, hone]
    rfl

/-- **`Simulates.tick`'s node step at a public time.** An engine tick of an honest node at a public
time runs the node's tick with the encoded mempool on the node state before it. -/
theorem node_of_tick_public (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node =
      (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).1 := by
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hsel := poll_selected S rho hv v
  rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw hsel]
  have hPself : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).self =
      rho.ownKey v := by
    rw [atProposal_self _ _ _ _ _ _ hsel]; exact self_eq_ownKey S rho hn v i
  have hPnow : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).now = t :=
    atProposal_now S rho hn v _ t hsel
  have hPfg : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).fgDue = true :=
    atProposal_fgDue S rho hn v _ t hp hsel
  have hPnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).1 := by
    rw [atProposal_node S rho hn v _ t (fgDue_eq_false S rho hn v i) hsel,
      nodeTick_node_public _ (by exact hp)]
    exact congrArg (fun k => (Node.acCall k _ t _).1) (self_eq_ownKey S rho hn v i)
  have hPmem : (atProposal S rho v (rho.stateBefore i v) t).st.2 =
      Model.mempool rho.inbox v t := atProposal_mempool S rho v _ t
  change _ = (Node.onTick _ _ _ _ _ _).1
  erw [onTick_node (sp := S.params (pubOf E) hn)
    (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) _ t
    (encodeTxs (Model.mempool rho.inbox v t)),
    tickStep_acTick (sp := S.params (pubOf E) hn)
    (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) _ t
    (encodeTxs (Model.mempool rho.inbox v t))]
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, hts⟩
  · rw [hnil]
    erw [runDuties_fst_nil]
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _), poll_node_of_fgDue_true _ _ hPfg,
      fgUpdate_node_digestOf S rho hn _ (encodeTxs (Model.mempool rho.inbox v t)),
      hPself, hPnow, hPnode]
    have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) t :=
      not_proposes S hn _ _ t (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    erw [tickStep_proposal_not (sp := S.params (pubOf E) hn)
      (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) _ t
      (encodeTxs (Model.mempool rho.inbox v t)) hnp]
  · rw [hone]
    erw [runDuties_fst_cons, runDuties_fst_nil]
    have hts' : t = (S.params (pubOf E) hn).toParams.slotTime s :=
      hts.trans (slotTime_eq S hn s).symm
    have hfg' : (shapeOf S hn (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t)
        (.propose s hs)).1).fgDue = true :=
      dutyStep_propose_pres S rho hn (fun st => st.fgDue = true)
        (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
        (fun st s h => (propose_fgDue st s).trans h) v _ s hs hPfg
    have hself' : (shapeOf S hn (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t)
        (.propose s hs)).1).self = rho.ownKey v :=
      dutyStep_propose_pres S rho hn (fun st => st.self = rho.ownKey v)
        (fun st o hs h => (recordOwn_self st o hs).trans h)
        (fun st s h => (propose_self st s).trans h) v _ s hs hPself
    have hnow' : (shapeOf S hn (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t)
        (.propose s hs)).1).now = t :=
      dutyStep_propose_pres S rho hn (fun st => st.now = t)
        (fun st o hs h => (recordOwn_now st o hs).trans h)
        (fun st s h => (propose_now st s).trans h) v _ s hs hPnow
    erw [poll_node_of_fgDue _ _ (poll_fgDue _ _), poll_node_of_fgDue_true _ _ hfg',
      fgUpdate_node_digestOf S rho hn _ (encodeTxs (Model.mempool rho.inbox v t)),
      hself', hnow',
      dutyStep_propose_node S rho hn v _ s hs (selValid_proposer S rho hn hv.selValid s) hPself
        (by rw [hPnow, hts']; exact slotOf_slotTime _ s) (hPnow.trans hts')
        (fun hselected par info cs hprop =>
          proposal_releasable S rho hn hv v hv' i t he s par info cs hs hone hselected hprop)]
    erw [hPnode, hPnow, hPmem]

end Engine

end Consensus.Goldilocks.Refinement

end
