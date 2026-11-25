module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps

public section

/-! # Engine signings and trace signings

The two halves of the bridge between an engine signing (`EngineSignsAt`, the FG update of a
trailing poll of a public tick) and a trace signing cut of that tick:
`updateNode_of_tick_public` identifies the engine's node state at that poll with the trace
handler's state after its AC tick and proposal steps (same key, time and signing calendar), and
`attest_mem_exec_tick` puts the attestation the FG update creates there among the tick's cuts. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

/-- The FG update of a tick with the signing calendar on: when `ac_to_fg` reports `C` and the
attestation duty creates `a` for it, the tick's cuts contain the signing cut of `a`. -/
theorem attest_mem_exec_tick {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (st : NodeState A) (t : Time)
    (x : Nat) {C : A.Blk} {a : FG.Att P.n} {Λ' : FG.Record}
    (hC : (acToFG (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
      t x .proposal).1 t).2.2 = some C)
    (ha : (acToFG (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
      t x .proposal).1 t).1.fg.attest
        (acToFG (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
          t x .proposal).1 t).1.record self C = some (a, Λ')) :
    Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t (.tick x true)).2 := by
  change _ ∈ (exec proposer dg self st t (.tick x false)).2 ++
    (tickStep proposer dg self (tickStep proposer dg self
      (tickStep proposer dg self st t x .acTick).1 t x .proposal).1 t x .fgUpdate).2
  refine List.mem_append_right _ ?_
  generalize (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
    t x .proposal).1 = st₂ at hC ha ⊢
  simp only [tickStep, hC, Node.attest, ha]
  exact List.mem_cons_of_mem _ List.mem_cons_self

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The node at the FG update of a public tick.** After the leading polls and the tick's
proposal duty, the engine's node state is the trace handler's state after its AC tick and
proposal steps, at the tick's time and key, with the FG update due exactly when the signing
calendar says so. -/
theorem updateNode_of_tick_public (hv : rho.ExecutionValid) (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (shapeOf S hn (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1).self = rho.ownKey v ∧
      (shapeOf S hn (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1).now = t ∧
      (shapeOf S hn (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1).fgDue =
          S.sign (pubOf E) (rho.ownKey v) t ∧
      (shapeOf S hn (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1).node =
        (tickStep (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (tickStep (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            (stateAt S rho hn v i).node t (encodeTxs (Model.mempool rho.inbox v t)) .acTick).1 t
          (encodeTxs (Model.mempool rho.inbox v t)) .proposal).1 := by
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hsel := poll_selected S rho hv v
  have hPself : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).self =
      rho.ownKey v := by
    rw [atProposal_self _ _ _ _ _ _ hsel, ← stateAt_eq S rho hn v i]
    exact self_eq_ownKey S rho hn v i
  have hPnow : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).now = t :=
    atProposal_now S rho hn v _ t hsel
  have hPfg : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).fgDue =
      S.sign (pubOf E) (rho.ownKey v) t := by
    rw [atProposal_fgDue S rho hn v _ t hp hsel, ← stateAt_eq S rho hn v i,
      self_eq_ownKey S rho hn v i]
  have hPnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).1 := by
    rw [atProposal_node S rho hn v _ t
      (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel,
      nodeTick_node_public _ (by exact hp), ← stateAt_eq S rho hn v i]
    exact congrArg (fun k => (Node.acCall k _ t _).1) (self_eq_ownKey S rho hn v i)
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, hts⟩
  · have hnd : (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1 =
          atProposal S rho v (rho.stateBefore i v) t := by
      rw [hnil]; rfl
    have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) t :=
      not_proposes S hn _ _ t (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    rw [hnd, tickStep_proposal_not (sp := S.params (pubOf E) hn)
      (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) _ t
      (encodeTxs (Model.mempool rho.inbox v t)) hnp]
    exact ⟨hPself, hPnow, hPfg, hPnode⟩
  · have hnd : (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1 =
          (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1 := by
      rw [hone]; rfl
    have hts' : t = (S.params (pubOf E) hn).toParams.slotTime s :=
      hts.trans (slotTime_eq S hn s).symm
    rw [hnd]
    refine ⟨dutyStep_propose_pres S rho hn (fun st => st.self = rho.ownKey v)
        (fun st o hs h => (recordOwn_self st o hs).trans h)
        (fun st s h => (propose_self st s).trans h) v _ s hs hPself,
      dutyStep_propose_pres S rho hn (fun st => st.now = t)
        (fun st o hs h => (recordOwn_now st o hs).trans h)
        (fun st s h => (propose_now st s).trans h) v _ s hs hPnow,
      dutyStep_propose_pres S rho hn (fun st => st.fgDue = S.sign (pubOf E) (rho.ownKey v) t)
        (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
        (fun st s h => (propose_fgDue st s).trans h) v _ s hs hPfg, ?_⟩
    rw [dutyStep_propose_node S rho hn v _ s hs
      (selValid_proposer S rho hn hv.selValid s) hPself
      (by rw [hPnow, hts']; exact slotOf_slotTime _ s) (hPnow.trans hts')
      (fun hselected par info cs hprop =>
        proposal_releasable S rho hn hv v i t he s par info cs hs hone hselected hprop),
      hPnode, hPnow, atProposal_mempool]
    rfl

end Consensus.Goldilocks.Simulation

end
