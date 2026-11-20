module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeStateAgreement
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Steps

public section

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V} [DecidableEq V]

open NodeAsChainShape.CanonicalTrace (afterClock_eq engineDuty engineDuty_eq envelope_eq)

private theorem map_cast {α β : Type} (h : α = β) (ds : List α) :
    ds.map (cast h) = cast (congrArg List h) ds := by
  cases h
  exact List.map_id' _

omit [DecidableEq V] in
private theorem engineDuty_map (S : Setup) (hn : 1 ≤ Fintype.card V)
    (e : NodeAsChainShape.CanonicalTrace.Encoding (goldilocks S) E
      (S.params (pubOf E) hn).toParams rfl hn (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))
    (ds : List (ShapeDuty e.skel.Kind)) :
    ds.map (engineDuty e) = cast (congrArg List
      (congrArg (fun s : ChainShape (pubOf E) schema.Id Info => (compile s).Duty)
        e.shape_eq.symm)) ds := by
  rw [show engineDuty e = _ from funext (engineDuty_eq e)]
  exact map_cast _ _

omit [DecidableEq V] in
private theorem trace_proposer (S : Setup) (hn : 1 ≤ Fintype.card V)
    (rho : Model.Run (compiled (goldilocks S)) E) :
    NodeAsChainShape.CanonicalTrace.runProposer rho hn = runProposer S rho hn :=
  funext fun j => (NodeAsChainShape.CanonicalTrace.runProposer_eq (hn := hn) rho j).trans
    (runProposer_eq S rho hn j).symm

private theorem fold_delivery {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {binding : VoteBinding} (pr : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)) (hs : List (Header Info × Nat))
    (k : Fin sp.n) (t : Time) (os : List (Wire sp.n binding))
    (st : NodeState (goldilocksNode sp ro)) :
    os.foldl (fun s w => ((NodeAsChainShape.canonEvent (wireCodec sp ro binding) hs w).map
      (fun ev => (Node.exec pr dg k s t ev).1)).getD s) st = deliverState pr dg hs k t os st := by
  induction os generalizing st with
  | nil => rw [deliverState_nil]; rfl
  | cons o os ih =>
    rw [List.foldl_cons, ih]
    change deliverState pr dg hs k t os
      (((canonEvent sp ro hs o).map (fun ev => (Node.exec pr dg k st t ev).1)).getD st) = _
    cases he : canonEvent sp ro hs o with
    | none => rw [deliverState_cons_none _ _ _ _ _ _ _ _ he]; rfl
    | some ev => rw [deliverState_cons_some _ _ _ _ _ _ _ _ ev he]; rfl

/-- The Goldilocks run establishes the local replay laws; its due flag is proof-side only. -/
theorem traceEncoding_lawful (S : Setup) (hn : 1 ≤ Fintype.card V) :
    (traceEncoding (E := E) S hn).Lawful (traceDue S hn) :=
  traceEncoding_induction S hn (fun e due => e.Lawful due) fun hg => {
  init_due := fun _ _ => rfl
  set_due := fun _ _ => rfl
  clock_due := fun _ _ => rfl
  process_due := fun st o hs => by
    exact process_fgDue st o hs
  restore_due := fun _ _ _ => rfl
  cut_due rho v i := by
    rw [NodeAsChainShape.CanonicalTrace.stateAt_eq]
    have h := fgDue_eq_false S rho hn v i
    rw [stateAt_eq] at h
    exact h
  tick_schedule t ht := by
    rw [duties_eq S t ht]
    simp only [dutiesInit]
    rw (config := { transparency := .default }) [engineDuty_map S hn, cast_eq]
    exact List.append_assoc _ [ShapeDuty.poll t.toNat] [ShapeDuty.poll t.toNat]
  tick_prefix rho hv i v t he := by
    dsimp only
    rw (config := { transparency := .default }) [engineDuty_map S hn, cast_eq, afterClock_eq]
    rw (config := { transparency := .default })
      [← atProposal_eq S rho v (rho.stateBefore i v) t]
    rw [envelope_eq, NodeAsChainShape.CanonicalTrace.stateAt_eq]
    have hsel := poll_selected S rho hv v
    have hn' := atProposal_node S rho hn v (rho.stateBefore i v) t
      (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · rw [ite_eq_left hp]
      refine ⟨?_, atProposal_fgDue S rho hn v _ t hp hsel⟩
      refine hn'.trans ((nodeTick_node_public _ hp).trans ?_)
      have hself := self_eq_ownKey S rho hn v i
      rw [stateAt_eq] at hself
      exact congrArg (fun k => (Node.acCall k ((rho.stateBefore i v).st.1 hn).node t .tick).1)
        hself
    · rw [ite_eq_right hp]
      refine ⟨hn'.trans (nodeTick_node_other _ hp), ?_⟩
      change (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).fgDue = false
      rw [atProposal_shape _ _ _ _ _ _ hsel, nodeTick_eq]
      rw [ite_eq_right (by rw [poll_now, poll_now]; exact hp)]
      exact poll_fgDue _ _
  tick_proposal rho hv i v t he := by
    dsimp only
    rw (config := { transparency := .default })
      [engineDuty_map S hn, cast_eq, engineDuty_map S hn, cast_eq, afterClock_eq]
    rw (config := { transparency := .default })
      [← atProposal_eq S rho v (rho.stateBefore i v) t]
    simp only [trace_proposer, hg, ← digestOf_eq, envelope_eq]
    let nd := atProposal S rho v (rho.stateBefore i v) t
    have hsel := poll_selected S rho hv v
    have hnow := atProposal_now S rho hn v (rho.stateBefore i v) t hsel
    have hself := (atProposal_self S rho hn v (rho.stateBefore i v) t hsel).trans
      (by rw [← stateAt_eq S rho hn v i, self_eq_ownKey])
    have hmem := atProposal_mempool S rho v (rho.stateBefore i v) t
    let post := (rho.runDuties v nd ((skeleton (pubOf E) S.vote).proposeAt t)).1
    change (shapeOf S hn post).fgDue = (shapeOf S hn nd).fgDue ∧
      (shapeOf S hn post).node = (Node.tickStep (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (shapeOf S hn nd).node t (encodeTxs (Model.mempool rho.inbox v t))
        .proposal).1 ∧ (¬ (S.params (pubOf E) hn).toParams.IsPublic t →
          (shapeOf S hn post).node = (shapeOf S hn nd).node)
    unfold post
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with
      ⟨hnil, hno⟩ | ⟨s, hs, hone, hts⟩
    · rw [hnil]
      rw (config := { transparency := .default }) [runDuties_fst_nil]
      refine ⟨rfl, ?_, fun _ => rfl⟩
      exact (tickStep_proposal_not _ _ _ _ _ _ (not_proposes S hn _ _ t
        (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s))))).symm
    · rw [hone]
      rw (config := { transparency := .default }) [runDuties_fst_cons, runDuties_fst_nil]
      have ht := hts.trans (slotTime_eq S hn s).symm
      refine ⟨?_, ?_, fun hp => (hp (ht ▸ (S.params (pubOf E) hn).toParams.slotTime_public s)).elim⟩
      · exact dutyStep_propose_pres S rho hn (fun st => st.fgDue = (shapeOf S hn nd).fgDue)
          (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
          (fun st s h => (propose_fgDue st s).trans h) v nd s hs rfl
      · have h := dutyStep_propose_node S rho hn v nd s hs
          (selValid_proposer S rho hn hv.selValid s) hself
          (by rw [hnow, ht, slotOf_slotTime]) (hnow.trans ht)
          (fun hk par info cs hp => proposal_releasable_at S rho hn hv v i t he s par info cs
            hs hone hk hp)
        exact h.trans (congrArg₂ (fun time mp => (Node.tickStep (runProposer S rho hn)
          (digestOf S rho) (rho.ownKey v) (shapeOf S hn nd).node time (encodeTxs mp) .proposal).1)
          hnow hmem)
  tick_finish rho hv i v t _ := by
    dsimp only
    rw (config := { transparency := .default })
      [engineDuty_map S hn, cast_eq, engineDuty_map S hn, cast_eq, engineDuty_map S hn, cast_eq,
        afterClock_eq]
    rw (config := { transparency := .default })
      [← atProposal_eq S rho v (rho.stateBefore i v) t]
    simp only [trace_proposer, hg, ← digestOf_eq, envelope_eq]
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let post := (rho.runDuties v nd ((skeleton (pubOf E) S.vote).proposeAt t)).1
    have hsel := poll_selected S rho hv v
    have hnow := atProposal_now S rho hn v (rho.stateBefore i v) t hsel
    have hself := (atProposal_self S rho hn v (rho.stateBefore i v) t hsel).trans
      (by rw [← stateAt_eq S rho hn v i, self_eq_ownKey])
    have hpost : (shapeOf S hn post).self = rho.ownKey v ∧ (shapeOf S hn post).now = t := by
      unfold post
      rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨h, _⟩ | ⟨s, hs, h, _⟩
      · rw [h]
        rw (config := { transparency := .default }) [runDuties_fst_nil]
        exact ⟨hself, hnow⟩
      · rw [h]
        rw (config := { transparency := .default }) [runDuties_fst_cons, runDuties_fst_nil]
        exact dutyStep_propose_pres S rho hn (fun st => st.self = rho.ownKey v ∧ st.now = t)
          (fun st o hs h => ⟨(recordOwn_self st o hs).trans h.1, (recordOwn_now st o hs).trans h.2⟩)
          (fun st s h => ⟨(propose_self st s).trans h.1, (propose_now st s).trans h.2⟩)
          v nd s hs ⟨hself, hnow⟩
    change (shapeOf S hn (rho.runDuties v post [.poll t.toNat, .poll t.toNat]).1).node =
      if (shapeOf S hn post).fgDue then
        (Node.tickStep (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (shapeOf S hn post).node t (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
      else (shapeOf S hn post).node
    rw (config := { transparency := .default }) [runDuties_fst_cons, runDuties_fst_cons,
      runDuties_fst_nil, dutyStep_poll S rho hn _ _ _ hsel, dutyStep_poll S rho hn _ _ _ hsel]
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _)]
    cases h : (shapeOf S hn post).fgDue
    · exact poll_node_of_fgDue _ _ h
    · rw [poll_node_of_fgDue_true _ _ h, fgUpdate_node_digestOf, hpost.1, hpost.2]
      rfl
  gossip_node rho v nd t := by
    simp only [envelope_eq]
    exact gossip_node_eq S rho hn (rho.ownKey v) nd t
  delivery_process rho hv i v o t he := by
    rw [NodeAsChainShape.CanonicalTrace.deliveryPost_eq]
    rw [NodeAsChainShape.CanonicalTrace.stateAt_eq, NodeAsChainShape.CanonicalTrace.wireOf_eq]
    dsimp only
    rw [trace_proposer, hg, ← digestOf_eq]
    change (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o)).node = _
    rw [← stateAt_eq S rho hn v i]
    rw [process_eq (stateAt S rho hn v i) o (Model.digests rho.hash o)]
    refine (foldl_processOne_node (runProposer S rho hn) (digestOf S rho) _ _ _).trans ?_
    rw [self_eq_ownKey, now_eq_lastClock S rho hn hv, lastClock_of_deliver S rho hv v he]
    have hf := (fold_delivery (runProposer S rho hn) (digestOf S rho) (Model.digests rho.hash o)
      (rho.ownKey v) t (delivered (Model.digests rho.hash o) (stateAt S rho hn v i) o)
      (stateAt S rho hn v i).node).symm
    rw [stateAt_eq]
    rw [stateAt_eq] at hf
    exact hf
  delivery_publish rho i v o t he hd := by
    rw [NodeAsChainShape.CanonicalTrace.stateAt_eq, NodeAsChainShape.CanonicalTrace.stateAt_eq,
      NodeAsChainShape.CanonicalTrace.wireOf_eq]
    change ((rho.stateBefore (i + 1) v).st.1 hn).node =
      (process ((rho.stateBefore i v).st.1 hn) o (Model.digests rho.hash o)).node
    rw [← stateAt_eq S rho hn v (i + 1), ← stateAt_eq S rho hn v i]
    rw [stateAt_deliver S rho hn v he]
    rw [NodeAsChainShape.CanonicalTrace.stateAt_eq, NodeAsChainShape.CanonicalTrace.wireOf_eq] at hd
    exact (deliver_pres S rho hn
      (fun st => st.node = (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node ∧
        st.fgDue = false)
      (fun st t h => ⟨(poll_node_of_fgDue st t h.2).trans h.1, poll_fgDue st t⟩)
      (fun st _ _ hs h =>
        ⟨(recordOwn_none_node st _ _ hs).trans h.1, (recordOwn_fgDue st _ hs).trans h.2⟩)
      v _ o t ⟨by rw [stateAt_eq], hd⟩).1
  restore_node := fun _ _ _ => rfl }

end Consensus.Goldilocks.Simulation
