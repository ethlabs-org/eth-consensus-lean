module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteForwardQueue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Queue
import ConsensusLean.Lemmas.Model.Credentials

public section

/-! # Same-event forwarding of freshly pooled votes: the node-local steps

A vote that an engine event newly inserts into a node's pool is queued as a vote-forward envelope
before the event's releasing poll. The queueing reads the node's own steps only; the release of a
delivery's queue reads two facts that depend on the fault model, and they are premises:

* `tick_pool_insertion_queued`: a tick's insertion is queued before the tick's trailing polls;
* `delivery_voteForward_released_of`: when each envelope a delivery queues has its vote held or at
  the outbox head, and the delivering node is honest at `0`, the delivery releases every one;
* `delivery_pool_insertion_queued`: a delivery's insertion is queued by its processing.

Constant faults (`Simulation/Core`) and growing faults (`Growing/Simulation/VoteForwardRelease`)
supply the premises. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The own-token gate holds at every engine state. -/
theorem stateAt_voteGate (hv : rho.ExecutionValid) (v : V) (i : Nat) :
    VoteGate (stateAt S rho hn v i) :=
  (voteGate_iff _).2 fun m hm => stateAt_ownToken_exists S rho hn hv v i m hm

omit [DecidableEq V] in
/-- A state with an engine state's AC vote permission and vote authentication has its gate. -/
private theorem voteGate_of_eq {st σ : State (S.params (pubOf E) hn) (S.ro _) S.vote}
    (hg : VoteGate σ) (hm : st.node.ac.mayVote = σ.node.ac.mayVote)
    (hio : st.voteIO = σ.voteIO) : VoteGate st := by
  rw [voteGate_iff] at hg ⊢
  intro m h
  rw [hm] at h
  rw [hio]
  exact hg m h

omit [DecidableEq V] in
private theorem nodeTick_mayVote (st : State (S.params (pubOf E) hn) (S.ro _) S.vote) :
    (nodeTick st).node.ac.mayVote = st.node.ac.mayVote := by
  rw [nodeTick_eq]
  split
  · exact AC.step_mayVote _ _ _ _ _ _
  · rfl

/-- **A tick's pool insertion is queued before its trailing polls.** A vote `m` that the tick
event `i` of `v` at `t` newly inserts into `v`'s pool is the envelope `(t, m)` of the shape after
the tick's leading polls and proposal duties. -/
theorem tick_pool_insertion_queued (hv : rho.ExecutionValid) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (m : AC.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    ∃ w, (t, m, w) ∈ (shapeOf S hn (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++
        (skeleton (pubOf E) S.vote).proposeAt t)).1).voteForwards := by
  have hsel := poll_selected S rho hv v
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  let st := (poll (poll { stateAt S rho hn v i with now := t } t.toNat).1 t.toNat).1
  have hn' : st.node = (stateAt S rho hn v i).node := by
    dsimp only [st]
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _)]
    exact poll_node_of_fgDue { stateAt S rho hn v i with now := t } _
      (fgDue_eq_false S rho hn v i)
  have hg : VoteGate st := voteGate_of_eq S hn (stateAt_voteGate S rho hn hv v i)
    (by rw [hn']) (by dsimp only [st]; rw [poll_voteIO S hn, poll_voteIO S hn])
  have hshape : shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t) = nodeTick st := by
    rw [atProposal_shape S rho hn v _ t hsel, ← stateAt_eq S rho hn v i]
  have hbase :
      m ∈ (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node.ac.pool m.slot →
      ∃ w, (t, m, w) ∈
        (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).voteForwards := by
    rw [hshape]
    have ht' : st.now = t := by dsimp only [st]; rw [poll_now, poll_now]
    intro hm
    have hq := nodeTick_pool_insertion_queued st hg m (hn' ▸ hold) hm
    rwa [ht'] at hq
  have hgate : VoteGate (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) := by
    rw [hshape]
    exact voteGate_of_eq S hn hg (nodeTick_mayVote S hn st) (nodeTick_voteIO S hn st)
  have hpool : m ∈ (shapeOf S hn (rho.runDuties v
      (atProposal S rho v (rho.stateBefore i v) t)
      ((skeleton (pubOf E) S.vote).proposeAt t)).1).node.ac.pool m.slot := by
    rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw hsel,
      poll_pool_eq, poll_pool_eq] at hnew
    exact hnew
  have hq := proposal_pool_insertion_queued S rho hn v
    (atProposal S rho v (rho.stateBefore i v) t) t hgate m
    (by rw [atProposal_now S rho hn v _ t hsel]; exact hbase) hpool
  rw [atProposal_now S rho hn v _ t hsel] at hq
  erw [runDuties_fst_append]
  rw [atProposal_eq] at hq
  exact hq

/-- **A delivery releases every envelope it queues.** Premises: `hheld`, each queued object is
the canonical object of its vote with some token, held in the seen closure or the own vote with
that token at the outbox head (`delivery_voteForward_canonical_held`); `hv'`, the delivering node
is honest at `0`, so it signs the outbox votes. -/
theorem delivery_voteForward_released_of (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0)
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (hheld : ∀ tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards,
      ∃ z, tv.2.2 = voteObj tv.2.1 z ∧
        (voteObj tv.2.1 z ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
          (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
            some (.vote (encodeVote tv.2.1) z)))
    (tv : Time × AC.Vote (Fintype.card V) × Wire (Fintype.card V) S.vote)
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward tv.1 (encodeVote tv.2.1))) [tv.2.2] ∈ rho.releasesAt i := by
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  let nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
    ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
      (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
  have hshape : shapeOf S hn nd =
      process (stateAt S rho hn v i) o (Model.digests rho.hash o) := by
    rw [stateAt_eq]; rfl
  have hself : (shapeOf S hn nd).self = rho.ownKey v := by
    rw [hshape]; exact (process_self _ _ _).trans (self_eq_ownKey S rho hn v i)
  have hfg : (shapeOf S hn nd).fgDue = false := by
    rw [hshape]; exact (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
  have hpre : pollPre (shapeOf S hn nd) = shapeOf S hn nd := by
    rw [pollPre_eq, hfg]; rfl
  have hav : ∀ q ∈ (shapeOf S hn nd).voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧
      (voteObj q.2.1 z ∈ Model.closure nd.seen ∨
        (shapeOf S hn nd).outbox.head? = some (.vote (encodeVote q.2.1) z)) := by
    intro q hq
    rw [hshape]
    exact hheld q (hshape ▸ hq)
  have hrel : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2.1))) [q.2.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
    by_cases hh : ∀ q ∈ (shapeOf S hn nd).voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧
        voteObj q.2.1 z ∈ Model.closure nd.seen
    · exact dutyStep_poll_voteForward S rho hn v nd t.toNat (poll_selected S rho hv v) hself hh
    · push Not at hh
      obtain ⟨q, hq, hnot⟩ := hh
      obtain ⟨z, hz, hq'⟩ := hav q hq
      have hhead := hq'.resolve_left (hnot z hz)
      obtain ⟨hsign, hk⟩ := delivery_outbox_vote_member S rho hn hv hv' i o q.2.1
        (List.mem_of_mem_head? (Option.mem_def.mpr (hshape ▸ hhead)))
      apply dutyStep_poll_voteForward_of_own_vote S rho hn v nd t.toNat
        (poll_selected S rho hv v) hself q.2.1 z hsign hk (by rw [hpre]; exact hhead)
      intro r hr
      obtain ⟨z', hz', h | h⟩ := hav r hr
      · exact ⟨z', hz', Or.inr h⟩
      · obtain ⟨hw, hzz⟩ := Body.vote.inj (Option.some.inj (h.symm.trans hhead))
        have hd := congrArg (decodeVote (Fintype.card V)) hw
        simp only [decodeVote_encodeVote, Option.some.injEq] at hd
        exact ⟨z', hz', Or.inl ⟨hd, hzz⟩⟩
  have hout := hrel tv (hshape ▸ htv)
  simp only [Model.Run.releasesAt, he]
  unfold Model.Run.deliver
  rw [deliverDuties_eq S t ht]
  apply List.mem_append_left
  erw [Model.Run.runDuties_cons]
  exact List.mem_append_left _ hout

/-- **A delivery's pool insertion is queued by its processing.** A vote `m` that the delivery
event `i` of `v` at `t` newly inserts into `v`'s pool, `v` honest at `0`, is the envelope `(t, m)`
of the processed shape. -/
theorem delivery_pool_insertion_queued (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∉ rho.faultyAt 0)
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : AC.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    ∃ w, (t, m, w) ∈
      (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards := by
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hnode : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node =
      (stateAt S rho hn v (i + 1)).node := by
    rw [node_of_deliver S rho hn hv v hv' i o t he]
    rw [process_eq (stateAt S rho hn v i) o (Model.digests rho.hash o)]
    erw [foldl_processOne_node (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) (digestOf S rho)]
    rw [self_eq_ownKey, hnow]
  rw [← hnow]
  rw [process_eq (stateAt S rho hn v i) o (Model.digests rho.hash o)]
  exact foldl_processOne_pool_insertion_queued (sp := S.params (pubOf E) hn)
    (ro := S.ro _) (stateAt S rho hn v i).voteIO (Model.digests rho.hash o) _
    (stateAt S rho hn v i) (stateAt_voteGate S rho hn hv v i) m hold
    (show m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool m.slot
      from hnode.symm ▸ hnew)

section QueuedObjects

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}

/-- A fresh envelope's object is the own object with its own token, whose body the same handler
queues and whose vote a cut of the handler emits, or the received object of a message call
admitting that vote. -/
theorem apply_voteForward_obj (st : State sp ro S.vote) origin r (t : Time)
    (v : AC.Vote sp.n) (w : Wire sp.n S.vote) (h : (t, v, w) ∈ (apply st origin r).voteForwards) :
    (t, v, w) ∈ st.voteForwards ∨
      (∃ z, w = voteObj v z ∧ Body.vote (encodeVote v) z ∈ (apply st origin r).outbox ∧
        ownToken st.voteIO v = some z ∧ ∃ ℓ, Cut.ac ℓ ∈ r.2 ∧ ∃ em ∈ ℓ.emits, em.msg = v) ∨
      (origin = some w ∧ ∃ ℓ, Cut.ac ℓ ∈ r.2 ∧ ℓ.call = .message v) := by
  classical
  simp only [apply, List.mem_append] at h
  obtain h | h := h
  · exact Or.inl h
  obtain ⟨u, hu, he⟩ := List.mem_filterMap.mp h
  obtain ⟨w', hw', heq⟩ := Option.map_eq_some_iff.mp he
  cases heq
  right
  have hcand := (List.mem_dedup.mp (List.mem_filter.mp hu).1)
  split_ifs at hw' with hown
  · obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hw'
    obtain ⟨c, hc, hvc⟩ := List.mem_flatMap.mp hown
    cases c with
    | fg _ => cases hvc
    | ac ℓ =>
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp hvc
      exact Or.inl ⟨z, rfl, List.mem_append_right _ (mem_emitted.mpr ⟨⟨ℓ, hc, e, he', rfl⟩, hz⟩),
        hz, ℓ, hc, e, he', rfl⟩
  · refine Or.inr ⟨hw', ?_⟩
    obtain ⟨c, hc, hvc⟩ := List.mem_flatMap.mp hcand
    cases c with
    | fg _ => cases hvc
    | ac ℓ =>
      rcases List.mem_append.mp hvc with hm | hm
      · refine ⟨ℓ, hc, ?_⟩
        revert hm
        cases hcall : ℓ.call <;> simp
        intro h; exact h ▸ rfl
      · exact absurd (List.mem_flatMap.mpr ⟨.ac ℓ, hc, hm⟩) hown

/-- Each envelope a processed object queues carries the canonical object of its vote: the own
object with the token of a queued own body, or the processed object itself. -/
private theorem processOne_voteForward_obj (io : VoteAuth sp.n S.vote)
    (hs : List (Header Info × Nat)) (st : State sp ro S.vote) (o : Wire sp.n S.vote)
    (t : Time) (v : AC.Vote sp.n) (w : Wire sp.n S.vote)
    (h : (t, v, w) ∈ (processOne io hs st o).voteForwards) :
    (t, v, w) ∈ st.voteForwards ∨ ∃ z, w = voteObj v z ∧
      (Body.vote (encodeVote v) z ∈ (processOne io hs st o).outbox ∨ w = o) := by
  have hrelay : ∀ (s : State sp ro S.vote) (c : Prop) (_ : Decidable c),
      (relayIf s c o).voteForwards = s.voteForwards ∧ (relayIf s c o).outbox = s.outbox := by
    intro s c _
    unfold relayIf
    split <;> exact ⟨rfl, rfl⟩
  rcases canonEvent_cases (ro := ro) io hs o with he | ⟨B, he⟩ | ⟨m, he⟩ | ⟨a, he⟩
  · simp only [AsChainShape.processOne_eq, he] at h
    exact Or.inl h
  · simp only [AsChainShape.processOne_eq, he] at h ⊢
    rw [(hrelay _ _ _).1] at h
    rw [(hrelay _ _ _).2]
    rcases apply_voteForward_obj S st none _ t v w h with h | ⟨z, hz, hb, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, hz, Or.inl hb⟩
    · cases h
  · simp only [AsChainShape.processOne_eq, he] at h ⊢
    rcases apply_voteForward_obj S st (some o) _ t v w h with h | ⟨z, hz, hb, -⟩ | ⟨h, ℓ, hℓ, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, hz, Or.inl hb⟩
    · cases Option.some.inj h
      simp only [Node.onMessage, Node.acCall, List.mem_singleton] at hℓ
      cases Cut.ac.inj hℓ
      cases hc
      rcases canonEvent_eq_some he with ⟨B, hB, -⟩ | ⟨v', z, hv, ho, -⟩ | ⟨a, ha, -⟩
      · cases hB
      · cases hv
        exact Or.inr ⟨z, ho, Or.inr rfl⟩
      · cases ha
  · simp only [AsChainShape.processOne_eq, he] at h ⊢
    rw [(hrelay _ _ _).1] at h
    rw [(hrelay _ _ _).2]
    rcases apply_voteForward_obj S st none _ t v w h with h | ⟨z, hz, hb, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨z, hz, Or.inl hb⟩
    · cases h

/-- Over a delivery traversal of objects from `L`, every queued object is the canonical object
of its vote: an object of `L`, or the own object whose same-token body is queued. -/
private theorem foldl_voteForward_obj (io : VoteAuth sp.n S.vote)
    (hs : List (Header Info × Nat)) (L : List (Wire sp.n S.vote)) :
    ∀ (os : List (Wire sp.n S.vote)) (st : State sp ro S.vote), (∀ x ∈ os, x ∈ L) →
    (∀ q ∈ st.voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧
      (Body.vote (encodeVote q.2.1) z ∈ st.outbox ∨ q.2.2 ∈ L)) →
    ∀ q ∈ (os.foldl (processOne io hs) st).voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧
      (Body.vote (encodeVote q.2.1) z ∈ (os.foldl (processOne io hs) st).outbox ∨ q.2.2 ∈ L) := by
  intro os
  induction os with
  | nil => exact fun _ _ h0 => h0
  | cons o os ih =>
    intro st hos h0
    have hsub : st.outbox ⊆ (processOne io hs st o).outbox := by
      intro x hx
      rw [processOne_outbox_eq (fun _ => st.self) (fun _ _ _ _ _ => 0)]
      exact List.mem_append_left _ hx
    refine ih (processOne io hs st o) (fun x hx => hos x (List.mem_cons_of_mem _ hx)) ?_
    rintro ⟨t, v, w⟩ hq
    rcases processOne_voteForward_obj S io hs st o t v w hq with hq | ⟨z, hz, hb | rfl⟩
    · obtain ⟨z, hz, hb | hb⟩ := h0 _ hq
      · exact ⟨z, hz, Or.inl (hsub hb)⟩
      · exact ⟨z, hz, Or.inr hb⟩
    · exact ⟨z, hz, Or.inl hb⟩
    · exact ⟨z, hz, Or.inr (hos _ List.mem_cons_self)⟩

end QueuedObjects

/-- **Every envelope a delivery queues carries the canonical object of its vote, held or
pending.** Each queued object is `voteObj m z` for its vote `m`: the received object, a part of
the delivered receipt and so in the seen closure, or the own object, whose body with the same
token is the head of the ordinary outbox. The queue is empty at every event boundary, so the
delivery's processing is the whole history. Discharges `hheld` of
`delivery_voteForward_released_of`. -/
theorem delivery_voteForward_canonical_held (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    ∀ tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards,
      ∃ z, tv.2.2 = voteObj tv.2.1 z ∧
        (voteObj tv.2.1 z ∈ Model.closure ((rho.stateBefore i v).seen ++ [o]) ∨
          (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.head? =
            some (.vote (encodeVote tv.2.1) z)) := by
  intro tv htv
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hpre : OneVote t (stateAt S rho hn v i) := by
    rcases (outbox_inv S rho hn hv v i).2 with h | h
    · exact absurd h (not_lastRestart_deliver S rho hv he)
    · rwa [hnow] at h
  have hproc := process_oneVote (digestOf S rho) (Model.digests rho.hash o)
    (hv.in_horizon _ (List.mem_of_getElem? he)).1
    (delivered (stateAt S rho hn v i).voteIO (Model.digests rho.hash o) (stateAt S rho hn v i) o)
    (stateAt S rho hn v i) hnow hpre
  have hlen := ((atMostOneVote_iff _).mp hproc.atMost).2
  change (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox.length ≤ 1 at hlen
  change tv ∈ ((delivered (stateAt S rho hn v i).voteIO (Model.digests rho.hash o)
    (stateAt S rho hn v i) o).foldl (processOne (stateAt S rho hn v i).voteIO
      (Model.digests rho.hash o)) (stateAt S rho hn v i)).voteForwards at htv
  obtain ⟨z, hz, hb | hL⟩ := foldl_voteForward_obj S (stateAt S rho hn v i).voteIO
    (Model.digests rho.hash o) _ _ (stateAt S rho hn v i) (fun x hx => hx)
    (fun q hq => by rw [voteForwards_empty S rho hn hv v i] at hq; cases hq) tv htv
  · refine ⟨z, hz, Or.inr ?_⟩
    change _ ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox at hb
    generalize (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).outbox = q at hb hlen ⊢
    cases q with
    | nil => cases hb
    | cons b bs =>
      cases bs with
      | nil => exact congrArg some (List.mem_singleton.mp hb).symm
      | cons c cs => simp at hlen
  · refine ⟨z, hz, Or.inl ?_⟩
    rw [← hz]
    exact List.mem_flatMap.mpr ⟨o, List.mem_append_right _ (List.mem_singleton_self _),
      mem_delivered _ _ hL⟩

section QueuedChecks

variable {sp : AC.ACParams} {ro : AC.ReplayOrder sp (List (FG.Att sp.n))}

/-- Every queued envelope carries the canonical object of its vote with a token the node's own
verifier accepts. -/
def QueuedChecked (st : State sp ro S.vote) : Prop :=
  ∀ q ∈ st.voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧
    st.voteIO.check q.2.1.val (S.vote.voteRole q.2.1.slot) (encodeVote q.2.1) z = true

omit [DecidableEq V] in
theorem queuedChecked_iff (st : State sp ro S.vote) : QueuedChecked S st ↔
    ∀ q ∈ st.voteForwards, ∃ z, q.2.2 = voteObj q.2.1 z ∧
      st.voteIO.check q.2.1.val (S.vote.voteRole q.2.1.slot) (encodeVote q.2.1) z = true :=
  Iff.rfl

/-- The node's verifier accepts the token its own issuer gives for a vote of its own key. -/
def OwnChecks (st : State sp ro S.vote) : Prop :=
  ∀ (m : AC.Vote sp.n) z, m.val = st.self → ownToken st.voteIO m = some z →
    st.voteIO.check m.val (S.vote.voteRole m.slot) (encodeVote m) z = true

omit [DecidableEq V] in
private theorem acCall_val (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    (c) {ℓ} (h : Cut.ac ℓ = (Node.acCall self st t c).2) : ∀ e ∈ ℓ.emits, e.msg.val = self := by
  simp only [Node.acCall] at h
  cases h
  exact emits_val (ro := ro) self st.ac _ t c

omit [DecidableEq V] in
private theorem onBlock_val (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time)
    B {ℓ} (h : Cut.ac ℓ ∈ (Node.onBlock self st t B).2) : ∀ e ∈ ℓ.emits, e.msg.val = self := by
  unfold Node.onBlock at h
  split at h
  · cases h
  · split at h
    · simp at h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · cases h
      · exact acCall_val self _ t _ h

omit [DecidableEq V] in
private theorem ownChecks_of_eq {st st' : State sp ro S.vote} (h : OwnChecks S st)
    (hio : st'.voteIO = st.voteIO) (hself : st'.self = st.self) : OwnChecks S st' := by
  intro m z hm hz
  rw [hio] at hz ⊢
  exact h m z (hm.trans hself) hz

omit [DecidableEq V] in
private theorem queuedChecked_apply (st : State sp ro S.vote) origin
    (r : NodeState (goldilocksNode sp ro) × List (Cut (goldilocksNode sp ro)))
    (h : QueuedChecked S st) (hown : OwnChecks S st)
    (hcuts : ∀ ℓ, Cut.ac ℓ ∈ r.2 → ∀ e ∈ ℓ.emits, e.msg.val = st.self)
    (horig : ∀ (w : Wire sp.n S.vote) (v : AC.Vote sp.n), origin = some w →
      (∃ ℓ, Cut.ac ℓ ∈ r.2 ∧ ℓ.call = .message v) →
      ∃ z, w = voteObj v z ∧
        st.voteIO.check v.val (S.vote.voteRole v.slot) (encodeVote v) z = true) :
    QueuedChecked S (apply st origin r) := by
  rintro ⟨t, v, w⟩ hq
  rcases apply_voteForward_obj S st origin r t v w hq with
    hq | ⟨z, hz, -, htok, ℓ, hℓ, em, hem, rfl⟩ | ⟨ho, hc⟩
  · exact h _ hq
  · exact ⟨z, hz, hown _ z (hcuts ℓ hℓ em hem) htok⟩
  · exact horig w v ho hc

omit [DecidableEq V] in
/-- Processing one object keeps every queued token checked: an own envelope carries the own
token of an own emission, and a received one is the object whose check admitted the vote. -/
theorem queuedChecked_processOne (hs : List (Header Info × Nat)) (st : State sp ro S.vote)
    (o : Wire sp.n S.vote) (h : QueuedChecked S st) (hown : OwnChecks S st) :
    QueuedChecked S (processOne st.voteIO hs st o) := by
  have hrelay : ∀ (s : State sp ro S.vote) (c : Prop) (_ : Decidable c),
      QueuedChecked S s → QueuedChecked S (relayIf s c o) := by
    intro s c _ hs'
    unfold relayIf
    split <;> exact hs'
  rcases canonEvent_cases (ro := ro) st.voteIO hs o with he | ⟨B, he⟩ | ⟨m, he⟩ | ⟨a, he⟩
  · simp only [AsChainShape.processOne_eq, he]
    exact h
  · simp only [AsChainShape.processOne_eq, he]
    refine hrelay _ _ _ (queuedChecked_apply S st none _ h hown
      (fun ℓ hℓ => onBlock_val _ _ _ _ hℓ) (fun _ _ h => by cases h))
  · simp only [AsChainShape.processOne_eq, he]
    refine queuedChecked_apply S st (some o) _ h hown ?_ ?_
    · intro ℓ hℓ
      simp only [Node.onMessage, List.mem_singleton] at hℓ
      exact acCall_val _ _ _ _ hℓ
    · rintro w v hw ⟨ℓ, hℓ, hc⟩
      cases Option.some.inj hw
      simp only [Node.onMessage, Node.acCall, List.mem_singleton] at hℓ
      cases Cut.ac.inj hℓ
      cases hc
      rcases canonEvent_eq_some he with ⟨B, hB, -⟩ | ⟨v', z, hv, ho, hck⟩ | ⟨a, ha, -⟩
      · cases hB
      · cases hv
        exact ⟨z, ho, hck⟩
      · cases ha
  · simp only [AsChainShape.processOne_eq, he]
    refine hrelay _ _ _ (queuedChecked_apply S st none _ h hown ?_ (fun _ _ h => by cases h))
    intro ℓ hℓ
    simp [Node.onAttestation] at hℓ

omit [DecidableEq V] in
/-- A delivery traversal keeps every queued token checked. -/
theorem queuedChecked_foldl (hs : List (Header Info × Nat)) (io : VoteAuth sp.n S.vote) :
    ∀ (os : List (Wire sp.n S.vote)) (st : State sp ro S.vote), st.voteIO = io →
      QueuedChecked S st → OwnChecks S st →
      QueuedChecked S (os.foldl (processOne io hs) st) := by
  intro os
  induction os with
  | nil => exact fun _ _ h _ => h
  | cons o os ih =>
    intro st hio h hown
    subst hio
    exact ih _ (processOne_voteIO _ _ _ _) (queuedChecked_processOne S hs st o h hown)
      (ownChecks_of_eq S hown (processOne_voteIO _ _ _ _) (processOne_self _ _ _ _))

omit [DecidableEq V] in
theorem queuedChecked_recordOwn (st : State sp ro S.vote) o hs (h : QueuedChecked S st)
    (hown : OwnChecks S st) : QueuedChecked S (recordOwn st o hs) := by
  rw [AsChainShape.recordOwn_eq]
  split
  · exact h
  · split
    · exact queuedChecked_apply S st none _ h hown (fun ℓ hℓ => onBlock_val _ _ _ _ hℓ)
        (fun _ _ h => by cases h)
    · exact h
  · exact h

omit [DecidableEq V] in
theorem queuedChecked_propose (st : State sp ro S.vote) s (h : QueuedChecked S st) :
    QueuedChecked S (propose st s).1 := by
  rw [propose_eq]; dsimp only; split <;> exact h

omit [DecidableEq V] in
theorem queuedChecked_nodeTick (st : State sp ro S.vote) (h : QueuedChecked S st)
    (hown : OwnChecks S st) : QueuedChecked S (nodeTick st) := by
  rw [nodeTick_eq]
  split
  · refine queuedChecked_apply S st none _ h hown ?_ (fun _ _ h => by cases h)
    intro ℓ hℓ
    exact acCall_val _ _ _ _ (List.mem_singleton.mp hℓ)
  · exact h

omit [DecidableEq V] in
theorem queuedChecked_poll (st : State sp ro S.vote) u : QueuedChecked S (poll st u).1 := by
  intro q hq
  rw [poll_voteForwards] at hq
  cases hq

end QueuedChecks

/-- A node's own verifier accepts its own tokens on its own votes, under the run's vote
verification. -/
theorem ownChecks_of_eq_voteIO (hv : rho.ExecutionValid) {v : V}
    {st : State (S.params (pubOf E) hn) (S.ro _) S.vote}
    (hio : st.voteIO = rho.voteIO v) (hself : st.self = rho.ownKey v) : OwnChecks S st := by
  intro m z hm hz
  rw [hio] at hz ⊢
  rw [hm, hself]
  refine rho.voteIO_own_check hv.credentials.1 hz ?_ v
  change (decodeVote _ (encodeVote m)).map _ = _
  rw [decodeVote_encodeVote, ← hself, ← hm]
  rfl

/-- **Every envelope a delivery queues carries a token that verifies.** -/
theorem delivery_voteForward_checked (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) :
    ∀ tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards,
      ∃ z, tv.2.2 = voteObj tv.2.1 z ∧
        rho.verify (tv.2.1.val, S.vote.voteRole tv.2.1.slot, encodeVote tv.2.1) z = true := by
  have _ := he
  have h := queuedChecked_foldl S (Model.digests rho.hash o) (stateAt S rho hn v i).voteIO
    (delivered (stateAt S rho hn v i).voteIO (Model.digests rho.hash o) (stateAt S rho hn v i) o)
    (stateAt S rho hn v i) rfl
    (fun q hq => by rw [voteForwards_empty S rho hn hv v i] at hq; cases hq)
    (ownChecks_of_eq_voteIO S rho hn hv (stateAt_voteIO S rho hn v i) (self_eq_ownKey S rho hn v i))
  intro tv htv
  obtain ⟨z, hz, hc⟩ := h tv htv
  refine ⟨z, hz, ?_⟩
  have hio : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteIO = rho.voteIO v :=
    (process_voteIO S hn _ _ _).trans (stateAt_voteIO S rho hn v i)
  change (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteIO.check _ _ _ _ = _
    at hc
  rw [hio] at hc
  exact hc

end Consensus.Goldilocks.Simulation

end
