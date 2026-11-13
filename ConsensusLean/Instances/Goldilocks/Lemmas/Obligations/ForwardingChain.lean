module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingDecodeBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationDecode

public section

/-! # Forwarding decoder correspondence along a run

Every engine state of a node `v` satisfies `WrappersDecoded` and `WrappersHeld`
(`stateAt_decoded_held_of_own`), and every acceptance in the simulating trace has an actual,
exactly decoded same-event forwarding publication (`forward_publication_of_events`). The proofs
read only the engine run; the facts that depend on the fault model enter as premises:

* own proposals: the canonical child of every scheduled proposal of `v` decodes
  (`OwnProposalsDecode`);
* queueing: an accepting scheduled proposal queues its exact wrapper;
* the per-event publications, for the final assembly.

Constant faults (`Obligations/ForwardingDecode`) supply them for nodes honest from the start,
growing faults (`Growing/Obligations/Network/Forwarding`) for every node with an actual event. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks
open Consensus.Model

/-- Own proposals of `v` decode: at every tick of `v` with a scheduled proposal, the canonical
child that the proposal constructs from the engine state decodes. -/
structure OwnProposalsDecode {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V) (v : V) : Prop where
  decodes : ∀ i t, rho.events[i]? = some (.tick v t) →
    Node.Proposes (P := (S.params (pubOf E) hn).toParams)
      (runProposer S rho hn) (rho.ownKey v) t →
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let r := Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf S rho) (rho.ownKey v) r.1.fg
        (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p
      decodeBlock (S.params (pubOf E) hn) (binding := stock) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B

/-- A node step from the engine state before a scheduled tick decodes the tick's own proposal:
the reachable node configuration supplies canonical child validity. -/
theorem scheduled_proposal_child_decodes_of_step {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid) (v : V) (i : Nat) (t : Time)
    (hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams)
      (runProposer S rho hn) (rho.ownKey v) t)
    {cfg cfg' : Node.Config (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    -- Node run: a reachable configuration holding the engine state of `v` before the tick steps
    -- through the tick at `t`, and the genesis block is well rooted.
    (hr : Node.Reachable (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) cfg)
    (hst : cfg.st = (stateAt S rho hn v i).node)
    (hs : Node.Step (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) cfg
      (.tick (encodeTxs (mempool rho.inbox v t))) t cfg')
    (hg : ((S.params (pubOf E) hn).toParams.genesisBlock
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload).RootOk (digestOf S rho)) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let r := Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf S rho) (rho.ownKey v) r.1.fg
        (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p
      decodeBlock (S.params (pubOf E) hn) (binding := stock) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B := by
  dsimp only
  intro d p hdp
  have hpub := (S.params (pubOf E) hn).toParams.slotTime_public
    ((S.params (pubOf E) hn).toParams.slotOf t)
  rw [← hp.2.1] at hpub
  have hsel := poll_selected S rho hv v
  have hnode := atProposal_node S rho hn v (rho.stateBefore i v) t
    (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel
  rw [nodeTick_node_public { (rho.stateBefore i v).st.1 hn with now := t } hpub] at hnode
  have hself := self_eq_ownKey S rho hn v i
  rw [stateAt_eq] at hself
  have hnow := atProposal_now S rho hn v (rho.stateBefore i v) t hsel
  have req := SA.interface_requirements (S.params (pubOf E) hn)
    (List (FG.Att (Fintype.card V))) (S.ro _)
  have hdecode := own_proposal_decodes S rho hn (runProposer S rho hn) (rho.ownKey v)
    cfg _ t (encodeTxs (mempool rho.inbox v t))
    ⟨req.1, req.2.1, req.2.2.1, req.2.2.2, SA.proposal_payload_valid _ _ _⟩
    hg hr hs hp d p (by
      rw [hst]
      simpa only [hnode, hnow, Node.tickStep, stateAt_eq, hself] using hdp)
  simpa only [hnode, hnow, atProposal_mempool, hst, Node.tickStep, stateAt_eq, hself]
    using hdecode

/-- At a scheduled tick, the proposal duty preserves the joint invariant without assuming child
decoding of the run: reachable proposal execution and the own-proposal premise supply it. -/
theorem decoded_held_scheduled_proposal_of_own {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (hd : WrappersDecoded (digests rho.hash)
      (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)))
    (hh : WrappersHeld (digests rho.hash)
      (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)))
    -- Own proposals of `v` decode.
    (hown : OwnProposalsDecode S rho hn v) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let st' := shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  let nd := atProposal S rho v (rho.stateBefore i v) t
  have hpoll := poll_selected S rho hv v
  have hnow : (shapeOf S hn nd).now = t := atProposal_now S rho hn v _ t hpoll
  have hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s := by
    rw [hnow, ht]; exact slotOf_slotTime _ s
  have hc : WrappersCover (propose (shapeOf S hn nd) s).1 := by
    have h := tick_duty_prefix_wrappersCover S rho hn v i t
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
        List (protoOf (compiled (goldilocks S)) E).Duty)
    rw [← atProposal_eq S rho v (rho.stateBefore i v) t] at h
    unfold propose
    dsimp only
    split <;> simpa only [wrappersCover_iff, Node.acProposal] using h
  have hr : (propose (shapeOf S hn nd) s).1.node.fg.Reachable
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload := by
    have hnode := atProposal_node S rho hn v (rho.stateBefore i v) t
      (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hpoll
    have hpub : (S.params (pubOf E) hn).toParams.IsPublic t :=
      ht ▸ (S.params (pubOf E) hn).toParams.slotTime_public s
    have hfg : (shapeOf S hn nd).node.fg = (stateAt S rho hn v i).node.fg := by
      rw [hnode, nodeTick_node_public { (rho.stateBefore i v).st.1 hn with now := t } hpub]
      rw [stateAt_eq]
      rfl
    have hr := stateAt_fg_reachable S rho hn v i
    rw [← hfg] at hr
    unfold propose; dsimp only; split <;> exact hr
  by_cases hsel : rho.ownKey v ∈ rho.sel (.proposer s)
  · have hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) t := by
      rw [ht, proposes_iff S hn _ _ s hs]
      rw [selValid_proposer S rho hn hv.selValid s] at hsel
      exact (Finset.mem_singleton.mp hsel).symm
    cases hdp : (Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with
    | none =>
      have hempty : ((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2 = [] := by
        rw [act_propose_snd S hn nd s hs]
        simp only [propose, hdp, Option.map_none, Option.toList_none]
        rfl
      have hpre := decoded_held_propose (shapeOf S hn nd) s hd hh
      change WrappersDecoded (digests rho.hash)
          (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) ∧
        WrappersHeld (digests rho.hash) (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1)
      simp only [Model.Run.dutyStep,
        show (protoOf (compiled (goldilocks S)) E).role (.propose s hs) = .proposer s from rfl,
        hsel, ↓reduceIte, hempty, Model.Run.signedCandidate, List.filterMap_nil,
        Model.releaseAll]
      change WrappersDecoded (digests rho.hash)
          (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn) ∧
        WrappersHeld (digests rho.hash)
          (((protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).1.1 hn)
      rw [shapeOf_act_propose S hn]
      exact hpre
    | some result =>
      obtain ⟨d, p⟩ := result
      exact decoded_held_proposal_candidate S rho hn v nd s hs hd hh hc hr
        (Node.mkBlock (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _))
          (digestOf S rho) (rho.ownKey v)
          (Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
          (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p)
        (by simp only [Node.mkBlock, ne_eq, reduceCtorEq, not_false_eq_true]) rfl
        (hown.decodes i t he hp d p hdp)
        (hnow.symm ▸ (hv.in_horizon _ (List.mem_of_getElem? he)).1) hsel
        (proposal_candidate_block S rho hn v nd s hs hsel hslot d p hdp)
  · simpa only [Model.Run.dutyStep,
      show (protoOf (compiled (goldilocks S)) E).role (.propose s hs) = .proposer s from rfl,
      hsel, ↓reduceIte] using And.intro hd hh

/-- Every tick of `v` preserves the joint invariant, including its own proposal. -/
theorem decoded_held_tick_of_own {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hd : WrappersDecoded (digests rho.hash) (stateAt S rho hn v i))
    (hh : WrappersHeld (digests rho.hash) (stateAt S rho hn v i))
    -- Own proposals of `v` decode.
    (hown : OwnProposalsDecode S rho hn v) :
    let st' := shapeOf S hn (rho.tick (rho.stateBefore i v) v t).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hsel := poll_selected S rho hv v
  have hclock := stateAt_clock_bounds S rho hn hv v i
  rw [stateAt_eq] at hd hh hclock
  have hp := decoded_held_atProposal S rho hn v (rho.stateBefore i v) t hd hh
    (hclock.2 i _ le_rfl he) hsel
  have hprop :
      WrappersDecoded (digests rho.hash) (shapeOf S hn
        (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
          ((skeleton (pubOf E)).proposeAt t)).1) ∧
      WrappersHeld (digests rho.hash) (shapeOf S hn
        (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
          ((skeleton (pubOf E)).proposeAt t)).1) := by
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
      ⟨hnil, _⟩ | ⟨s, hs, hone, htime⟩
    · rw [hnil]; erw [runDuties_fst_nil]; exact hp
    · rw [hone]; erw [runDuties_fst_cons, runDuties_fst_nil]
      exact decoded_held_scheduled_proposal_of_own S rho hn hv v i t he s hs
        (htime.trans (slotTime_eq S hn s).symm) hp.1 hp.2 hown
  dsimp only
  rw [tick_of_awake S rho v _ t hw]
  apply releaseAll_pres_mem S rho hn
    (fun st => WrappersDecoded (digests rho.hash) st ∧ WrappersHeld (digests rho.hash) st)
  · intro c hc st hs h
    obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp hc
    have unsigned (m : Msg (Header Info) Body) (cs : List (Wire (Fintype.card V))) :
        WrappersDecoded (digests rho.hash) (recordOwn st (.mk .none m cs) hs) ∧
        WrappersHeld (digests rho.hash) (recordOwn st (.mk .none m cs) hs) := by
      unfold recordOwn
      split
      · exact ⟨h.1.mono rfl rfl rfl le_rfl, h.2.preserve rfl rfl rfl⟩
      · rename_i k s header carried heq; cases heq
      · exact h
    exact unsigned mc.1 mc.2
  · -- The duty steps stated on the goal's own `ShapeDuty` lists, so plain `rw` applies (as in
    -- `tick_node_eq`); `erw [← atProposal_eq …]` tried every projection at default transparency.
    have hpoll : ∀ (nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (x : Nat),
        shapeOf S hn (rho.runDuties v nd' [.poll x]).1 = (poll (shapeOf S hn nd') x).1 :=
      fun nd' x => dutyStep_poll S rho hn v nd' x hsel
    have hinit : ∀ nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
        (rho.runDuties v nd' (dutiesInit S t)).1 =
          (rho.runDuties v (rho.runDuties v (rho.runDuties v nd'
            ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
              List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
            ((skeleton (pubOf E)).proposeAt t)).1 [.poll t.toNat]).1 := fun nd' =>
      (runDuties_fst_append S rho v nd' _ _).trans
        (congrArg (fun x => (rho.runDuties v x [.poll t.toNat]).1)
          (runDuties_fst_append S rho v nd' _ _))
    rw [duties_eq S t ht, runDuties_fst_append, hpoll, hinit, hpoll,
      ← atProposal_eq S rho v (rho.stateBefore i v) t]
    exact decoded_held_poll _ _ (decoded_held_poll _ _ hprop.1 hprop.2).1
      (decoded_held_poll _ _ hprop.1 hprop.2).2

/-- Every engine state of `v` has decoded wrappers corresponding to held blocks. No decoder,
parent-slot, payload-validity or clock premise is assumed. -/
theorem stateAt_decoded_held_of_own {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V)
    -- Own proposals of `v` decode.
    (hown : OwnProposalsDecode S rho hn v)
    (i : Nat) :
    WrappersDecoded (digests rho.hash) (stateAt S rho hn v i) ∧
    WrappersHeld (digests rho.hash) (stateAt S rho hn v i) := by
  induction i with
  | zero =>
    rw [stateAt_zero]
    exact ⟨wrappersDecoded_empty _ _ (fun _ => rfl) rfl,
      wrappersHeld_empty _ _ (fun _ => rfl)⟩
  | succ i ih =>
    cases he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some ev =>
      by_cases hvn : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hvn
          subst w
          rw [stateAt_tick S rho hn v he]
          exact decoded_held_tick_of_own S rho hn hv v i t he ih.1 ih.2 hown
        | deliver w o t =>
          simp only [Model.Event.node] at hvn
          subst w
          rw [stateAt_deliver S rho hn v he]
          have hc := stateAt_wrappersCover S rho hn v i
          have hr := stateAt_fg_reachable S rho hn v i
          have ht := (stateAt_clock_bounds S rho hn hv v i).1
          rw [stateAt_eq] at ih hc hr ht
          exact decoded_held_deliver S rho hn v _ ih.1 ih.2
            hc hr o t ht
        | restart w t =>
          simp only [Model.Event.node] at hvn
          subst w
          rw [stateAt_restart S rho hn v he]
          have h := decoded_held_restore (stateAt S rho hn v i) t ih.1 ih.2
            ((stateAt_clock_bounds S rho hn hv v i).2 i _ le_rfl he)
          rwa [self_eq_ownKey S rho hn v i] at h
      · rw [state_of_other S rho hn v i ev he hvn]; exact ih

/-- Receipt acceptances publish a wrapper that decodes, not merely a candidate with the right
syntactic shape. The queue and decoder witnesses use the same processed state. -/
theorem delivery_acceptance_decoded_publication_of_held {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {o : (protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B)
    -- Own proposals of `v` decode.
    (hown : OwnProposalsDecode S rho hn v) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  have hstate := stateAt_decoded_held_of_own S rho hn hv v hown i
  have ht : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he)
  rw [eventCuts_deliver S rho hn i v o t he] at hr
  have hr' : r ∈ deliverRecs (runProposer S rho hn) (digestOf S rho)
      (digests rho.hash o) (stateAt S rho hn v i).self (stateAt S rho hn v i).now i
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0 := by
    simpa only [self_eq_ownKey, ht] using hr
  obtain ⟨p, hp⟩ := deliverRecs_acceptance_pending (runProposer S rho hn) (digestOf S rho)
    (digests rho.hash o) i _ _ 0 (stateAt_wrappersCover S rho hn v i) r B hr' hb
  have hself : (process (stateAt S rho hn v i) o (digests rho.hash o)).self =
      rho.ownKey v := (process_self _ _ _).trans (self_eq_ownKey S rho hn v i)
  have hc : forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
      pendingWrappers (process (stateAt S rho hn v i) o (digests rho.hash o)) := by
    rw [pendingWrappers_eq]
    refine List.mem_map.mpr ⟨_, hp, ?_⟩
    simp only [ht, forwardObj]
    rw [hself]
  have hprocessed := decoded_held_process S rho hn _ hstate.1 hstate.2
    (stateAt_wrappersCover S rho hn v i) (stateAt_fg_reachable S rho hn v i) o
    (stateAt_clock_bounds S rho hn hv v i).1
  have hd := pending_forward_decodes S rho hn _ hprocessed.1 t p B
    (hself.symm ▸ hc) hchild
  rw [hself] at hd
  obtain ⟨q, hq, hi, hx, ho⟩ := delivery_pending_publication S rho hn hv he _ hc
  exact ⟨p, q, hq, hi, hx, ho, ho.symm ▸ hd⟩

/-- Scheduled proposal acceptance publishes its exact decoded wrapper in the same tick. -/
theorem tick_proposal_acceptance_decoded_publication_of_queued {V : Type} [Fintype V]
    [DecidableEq V] {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (v : V)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (B : Blk (S.params (pubOf E) hn))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B)
    -- Own proposals of `v` decode.
    (hown : OwnProposalsDecode S rho hn v)
    -- Queueing: the proposal duty queues the exact wrapper of `B`.
    (hqueued : ∃ p, forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
      pendingWrappers (shapeOf S hn
        (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1)) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  obtain ⟨p, hp⟩ := hqueued
  have hstate := stateAt_decoded_held_of_own S rho hn hv v hown i
  have hclock := (stateAt_clock_bounds S rho hn hv v i).2 i _ le_rfl he
  rw [stateAt_eq] at hstate hclock
  have hprefix := decoded_held_atProposal S rho hn v (rho.stateBefore i v) t
    hstate.1 hstate.2 hclock
    (poll_selected S rho hv v)
  have hprop := decoded_held_scheduled_proposal_of_own S rho hn hv v i t he s hs ht
    hprefix.1 hprefix.2 hown
  have hself : (shapeOf S hn (rho.dutyStep v
      (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1).self =
      rho.ownKey v := by
    apply dutyStep_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h)
      (fun st h => (nodeTick_self st).trans h)
      (fun st t h => (poll_self st t).trans h)
    exact (atProposal_self S rho hn v _ t (poll_selected S rho hv v)).trans
      (by simpa only [stateAt_eq] using self_eq_ownKey S rho hn v i)
  have hd := pending_forward_decodes S rho hn _ hprop.1 t p B
    (hself.symm ▸ hp) hchild
  rw [hself] at hd
  have hpub : ∃ q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B := by
    apply tick_pending_publication S rho hn hv he
      ([ShapeDuty.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ [.propose s hs])
      [ShapeDuty.poll t.toNat]
    · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1]
      simp only [dutiesInit, hone]
      rfl
    · erw [runDuties_fst_append, runDuties_fst_cons, runDuties_fst_nil]
      rwa [atProposal_eq] at hp
  obtain ⟨q, hq, hi, hx, ho⟩ := hpub
  exact ⟨p, q, hq, hi, hx, ho, ho.symm ▸ hd⟩

/-- Every accepting cut of a tick has a successfully decoded publication. -/
theorem tick_acceptance_decoded_publication_of_queued {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (v : V)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B)
    -- Own proposals of `v` decode.
    (hown : OwnProposalsDecode S rho hn v)
    -- Queueing: an accepting scheduled proposal of this tick queues the exact wrapper of `B`.
    (hqueued : ∀ s (hs : 0 < s), (skeleton (pubOf E)).proposeAt t = [.propose s hs] →
      t = (S.params (pubOf E) hn).toParams.slotTime s →
      .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node
        t (encodeTxs (mempool rho.inbox v t)) .proposal).2 →
      ∃ p, forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
        pendingWrappers (shapeOf S hn
          (rho.dutyStep v (atProposal S rho v (rho.stateBefore i v) t) (.propose s hs)).1)) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  have hpub : (S.params (pubOf E) hn).toParams.IsPublic t := by
    by_contra h
    rw [eventCuts_tick_other S rho hn i v t he h] at hr
    exact List.not_mem_nil hr
  rw [eventCuts_tick_public S rho hn i v t he hpub] at hr
  obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hr
  have hl := (getElem_groupRecs (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (mempool rho.inbox v t))) k hk).2.2.2.2
  rw [hkr, hb] at hl
  have ha := tick_acceptance_proposal (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (encodeTxs (mempool rho.inbox v t)) B
    (hl.symm ▸ List.getElem_mem _)
  have hsel := poll_selected S rho hv v
  have hnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).1 := by
    rw [atProposal_node S rho hn v _ t
      (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel,
      nodeTick_node_public _ hpub, ← stateAt_eq S rho hn v i]
    exact congrArg (fun key => (Node.acCall key _ t .tick).1) (self_eq_ownKey S rho hn v i)
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, htime⟩
  · have hnp := not_proposes S hn (runProposer S rho hn) (rho.ownKey v) t
      (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    simp only [Node.tickStep, hnp, ↓reduceIte, List.not_mem_nil] at ha
  · have ht := htime.trans (slotTime_eq S hn s).symm
    exact tick_proposal_acceptance_decoded_publication_of_queued S rho hn hv v i t he s hs hone
      ht B hchild hown (hqueued s hs hone ht (by rwa [hnode]))

/-- Every acceptance in the simulating trace has an actual, exactly decoded same-event
publication, once every accepting cut of a tick or a delivery of the accepting node publishes
its decoded wrapper. A restart accepts no block. -/
theorem forward_publication_of_events {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    {x : Fin (Fintype.card V)} {k : Nat} {B : Blk (S.params (pubOf E) hn)}
    (ha : (simTrace S rho hn).AcceptAt x k B)
    -- Tick publication: an accepting cut of a tick of the node with key `x` publishes the
    -- decoded wrapper of `B` in that tick.
    (htick : ∀ v i t r, rho.events[i]? = some (.tick v t) → rho.ownKey v = x →
      r ∈ eventCuts S rho hn i → r.label = .fg (.block B true) →
      ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
        q.origin = rho.ownKey v ∧
        q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
        decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
          some (rho.ownKey v, t, p, B))
    -- Delivery publication: the same for an accepting cut of a delivery.
    (hdeliver : ∀ v i o t r, rho.events[i]? = some (.deliver v o t) → rho.ownKey v = x →
      r ∈ eventCuts S rho hn i → r.label = .fg (.block B true) →
      ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
        q.origin = rho.ownKey v ∧
        q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
        decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
          some (rho.ownKey v, t, p, B)) :
    ∃ r p, (publisherExecution S rho).actual r ∧ r.origin = x ∧
      cutMap S rho hn r.event ≤ k ∧ k < cutMap S rho hn (r.event + 1) ∧
      (publisherExecution S rho).eventTime r.event = (simTrace S rho hn).time k ∧
      r.object = forwardObj (S.params (pubOf E) hn) x ((simTrace S rho hn).time k) p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash r.object) r.object =
        some (x, (simTrace S rho hn).time k, p, B) := by
  obtain ⟨hxk, hlab⟩ := ha
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hlo, hhi, hidx, hnode, htime, _, hlabel⟩ :=
    simTrace_cut S rho hn hl
  have hb : r.label = .fg (.block B true) := Option.some.inj (hlabel.symm.trans hlab)
  have hr := List.mem_of_getElem? hidx
  have hxev : rho.ownKey ev.node = x := hnode.symm.trans hxk
  have hp : ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey ev.node ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey ev.node) ev.time p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey ev.node, ev.time, p, B) := by
    cases ev with
    | tick v t => exact htick v i t r he hxev hr hb
    | deliver v o t => exact hdeliver v i o t r he hxev hr hb
    | restart v t =>
      rw [eventCuts_restart S rho hn i v t he] at hr
      obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr
      have hc := (getElem_groupRecs (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0) .restart j hj).2.2.2.2
      rw [hjr, hb] at hc
      have hm := hc.symm ▸ List.getElem_mem (by simpa only [length_groupRecs] using hj)
      simp [Node.exec, Node.restart, Node.acCall] at hm
  obtain ⟨p, q, hq, hqi, hqx, hqo, hd⟩ := hp
  refine ⟨q, p, hq, hqx.trans hxev, hqi ▸ hlo, hqi ▸ hhi, ?_, ?_, ?_⟩
  · rw [hqi, publisherExecution_eventTime_eq, he]
    exact htime.symm
  · simpa only [hxev, ← htime] using hqo
  · simpa only [hxev, ← htime] using hd

end Consensus.Goldilocks.Obligations

end
