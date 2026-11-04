module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant

public section

/-! # Goldilocks Simulation: the engine simulates the node

`EngineSimulatesNode` (`Statements/Obligations`) assembled from its steps: the trace `simTrace`
with the cut map `cutMap` (`Trace`), a Goldilocks run by `simTrace_goldilocksRun` and agreeing
with the engine by the `Simulates` steps (`Run`). Signed fresh-admission publication follows
from event-local pool insertion and global first-release provenance. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape Blocks
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private def VoteQueueStamped {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (t : Time) (st : State sp ro) : Prop :=
  st.now = t ∧ ∀ q ∈ st.voteForwards, q.1 = t

/-- Every fresh block-handler insertion passes the forwarding candidate filter. -/
theorem onBlock_pool_insertion_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (B : Blk sp) (m : SA.Vote sp.n) (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (Node.onBlock st.self st.node st.now B).1.ac.pool m.slot) :
    (st.now, m) ∈ (apply st (Node.onBlock st.self st.node st.now B)).voteForwards := by
  unfold Node.onBlock at hnew ⊢
  split_ifs at hnew ⊢ with ht
  · exact False.elim (hold hnew)
  · cases hf : st.node.fg.onBlock B with
    | none => simp only [hf] at hnew; exact False.elim (hold hnew)
    | some fg =>
      simp only [hf] at hnew ⊢
      refine apply_voteForward_of_admission st _ m
        ⟨.block B, Node.frame { st.node with fg := fg },
          ((goldilocksNode sp ro).step st.self st.node.ac
            (Node.frame { st.node with fg := fg }) st.now (.block B)).2⟩
        (by simp [Node.acCall]) ?_ hold hnew
      · exact Compose.step_pool_insertion_source st.self st.node.ac
          (Node.frame { st.node with fg := fg }) st.now (.block B) (by simp) m hold hnew

/-- Every fresh message-handler insertion passes the forwarding candidate filter. -/
theorem onMessage_pool_insertion_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (v m : SA.Vote sp.n) (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (Node.onMessage st.self st.node st.now v).1.ac.pool m.slot) :
    (st.now, m) ∈ (apply st (Node.onMessage st.self st.node st.now v)).voteForwards := by
  refine apply_voteForward_of_admission st _ m ⟨.message v, Node.frame st.node,
    ((goldilocksNode sp ro).step st.self st.node.ac (Node.frame st.node) st.now (.message v)).2⟩
    (by simp [Node.onMessage, Node.acCall]) ?_ hold hnew
  · exact Compose.step_pool_insertion_source st.self st.node.ac (Node.frame st.node)
      st.now (.message v) (by simp) m hold hnew

/-- Processing any canonical object queues every newly inserted pool vote. -/
theorem processOne_pool_insertion_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} hs (st : State sp ro) o
    (m : SA.Vote sp.n) (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (processOne hs st o).node.ac.pool m.slot) :
    (st.now, m) ∈ (processOne hs st o).voteForwards := by
  rcases canonEvent_cases (ro := ro) hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩
  · simp only [processOne, h] at hnew
    exact False.elim (hold hnew)
  · simp only [processOne, h] at hnew ⊢
    unfold relayIf at hnew ⊢
    split_ifs at hnew ⊢ <;> exact onBlock_pool_insertion_queued st B m hold hnew
  · simp only [processOne, h] at hnew ⊢
    exact onMessage_pool_insertion_queued st v m hold hnew
  · simp only [processOne, h, relayIf, ↓reduceIte] at hnew
    exact False.elim (hold hnew)

/-- Recursive delivery processing cannot insert a vote without queueing its envelope. -/
theorem foldl_processOne_pool_insertion_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} hs (os : List (Wire sp.n))
    (st : State sp ro) (m : SA.Vote sp.n) (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (os.foldl (processOne hs) st).node.ac.pool m.slot) :
    (st.now, m) ∈ (os.foldl (processOne hs) st).voteForwards := by
  induction os generalizing st with
  | nil => exact False.elim (hold hnew)
  | cons o os ih =>
    by_cases hm : m ∈ (processOne hs st o).node.ac.pool m.slot
    · exact foldl_processOne_voteForwards_subset hs os _
        (processOne_pool_insertion_queued hs st o m hold hm)
    · have hq := ih (processOne hs st o) hm hnew
      rwa [processOne_now] at hq

/-- Recording an own block queues every fresh pool insertion as well. -/
theorem recordOwn_pool_insertion_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (m : SA.Vote sp.n) (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (recordOwn st o hs).node.ac.pool m.slot) :
    (st.now, m) ∈ (recordOwn st o hs).voteForwards := by
  unfold recordOwn at hnew ⊢
  split at hnew
  · exact False.elim (hold hnew)
  · split at hnew
    · exact onBlock_pool_insertion_queued st _ m hold hnew
    · exact False.elim (hold hnew)
  · exact False.elim (hold hnew)

/-- Every fresh public AC-tick insertion belongs to its forwarding queue. -/
theorem nodeTick_pool_insertion_queued {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (m : SA.Vote sp.n) (hold : m ∉ st.node.ac.pool m.slot)
    (hnew : m ∈ (nodeTick st).node.ac.pool m.slot) :
    (st.now, m) ∈ (nodeTick st).voteForwards := by
  unfold nodeTick at hnew ⊢
  split_ifs at hnew ⊢
  · refine apply_voteForward_of_admission st _ m ⟨.tick, Node.frame st.node,
      ((goldilocksNode sp ro).step st.self st.node.ac (Node.frame st.node) st.now .tick).2⟩
      (by simp [Node.acCall]) ?_ hold hnew
    exact Compose.step_pool_insertion_source st.self st.node.ac (Node.frame st.node)
      st.now .tick (by simp) m hold hnew
  · exact False.elim (hold hnew)

private theorem voteStamped_apply {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (t : Time) (st : State sp ro) r
    (h : VoteQueueStamped t st) : VoteQueueStamped t (apply st r) := by
  refine ⟨h.1, ?_⟩
  intro q hq
  by_cases hold : q ∈ st.voteForwards
  · exact h.2 q hold
  · exact ((apply_voteForward_fresh st r q.1 q.2 hq hold).1).trans h.1

private theorem voteStamped_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (t : Time) (st : State sp ro) o hs
    (h : VoteQueueStamped t st) : VoteQueueStamped t (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact voteStamped_apply t st _ h
    · exact h
  · exact h

private theorem voteStamped_propose {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (t : Time) (st : State sp ro) s
    (h : VoteQueueStamped t st) : VoteQueueStamped t (propose st s).1 := by
  unfold propose
  dsimp only
  split <;> exact h

private theorem voteStamped_nodeTick {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (t : Time) (st : State sp ro)
    (h : VoteQueueStamped t st) : VoteQueueStamped t (nodeTick st) := by
  unfold nodeTick
  split
  · exact voteStamped_apply t st _ h
  · exact h

private theorem voteStamped_poll {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (t : Time) (st : State sp ro) u
    (h : VoteQueueStamped t st) : VoteQueueStamped t (poll st u).1 := by
  refine ⟨(poll_now st u).trans h.1, ?_⟩
  intro q hq
  rw [poll_voteForwards] at hq
  cases hq

private theorem voteStamped_process {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (t : Time) (st : State sp ro) o hs
    (h : VoteQueueStamped t st) : VoteQueueStamped t (process st o hs) := by
  refine ⟨(process_now st o hs).trans h.1, ?_⟩
  intro q hq
  rcases foldl_processOne_voteForward_stamp hs (delivered sp o) st q.1 q.2 hq with hq | ht
  · exact h.2 q hq
  · exact ht.trans h.1

omit [DecidableEq V] in
private theorem poll_candidate_vote_stamp (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (u : Nat)
    {t : Time} {m : SA.Vote (Fintype.card V)}
    (ho : Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.signedCandidate v (.poll u)
        ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll u)).2) :
    ∃ q ∈ (shapeOf S hn nd).voteForwards, q.1 = t ∧ q.2 = m := by
  obtain ⟨body, cs, hm, _, he⟩ := rho.mem_signedCandidate.mp ho
  have hmsg := congrArg Model.Obj.msg he
  have hcar := congrArg Model.Obj.carried he
  rw [act_poll_snd S hn, (poll_outbox _ _).2] at hm
  rcases List.mem_append.mp hm with hpre | hvote
  · rcases List.mem_append.mp hpre with hbody | hblock
    · cases hh : (pollPre (shapeOf S hn nd)).outbox.head? with
      | none =>
        rw [hh] at hbody
        exact False.elim (List.not_mem_nil hbody)
      | some b =>
        rw [hh] at hbody
        have heq : (body, cs) = (.data b, []) := List.mem_singleton.mp hbody
        cases heq
        cases hcar
    · obtain ⟨q, _, hq⟩ := List.mem_map.mp hblock
      cases hq
      cases hmsg
  · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hvote
    cases heq
    have heq := Body.voteForward.inj (Model.Msg.data.inj hmsg)
    have hm := congrArg (decodeVote (Fintype.card V)) heq.2
    simp only [decodeVote_encodeVote] at hm
    exact ⟨q, hq, heq.1.symm, Option.some.inj hm.symm⟩

omit [DecidableEq V] in
private theorem duty_vote_stamp (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (u : Time)
    (hs : VoteQueueStamped u (shapeOf S hn nd)) {t : Time} {m : SA.Vote (Fintype.card V)}
    (ho : Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈
        rho.signedCandidate v d ((Model.protoOf (compiled (goldilocks S)) E).act nd.st d).2) :
    t = u := by
  cases d with
  | poll n =>
    obtain ⟨q, hq, ht, -⟩ := poll_candidate_vote_stamp S rho hn v nd n ho
    exact ht.symm.trans (hs.2 q hq)
  | act s k => exact k.elim
  | propose s hpos =>
    obtain ⟨body, cs, _, _, he⟩ := rho.mem_signedCandidate.mp ho
    have ha := congrArg Model.Obj.auth he
    cases ha
  | pollPropose n =>
    have hempty : ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose n)).2 =
        [] := by
      simp only [Model.protoOf, compiled, compile, goldilocks, dite_eq_left hn, goldilocksShape]
      rfl
    obtain ⟨body, cs, hm, _, _⟩ := rho.mem_signedCandidate.mp ho
    rw [hempty] at hm
    cases hm

omit [DecidableEq V] in
private theorem duty_vote_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (hp : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      q.2 ∈ (shapeOf S hn nd).node.ac.pool q.2.slot)
    {t : Time} {m : SA.Vote (Fintype.card V)}
    (ho : Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈
        rho.signedCandidate v d ((Model.protoOf (compiled (goldilocks S)) E).act nd.st d).2) :
    m ∈ (shapeOf S hn nd).node.ac.pool m.slot := by
  cases d with
  | poll n =>
    obtain ⟨q, hq, -, hqm⟩ := poll_candidate_vote_stamp S rho hn v nd n ho
    exact hqm ▸ hp q hq
  | act s k => exact k.elim
  | propose s hpos =>
    obtain ⟨body, cs, _, _, he⟩ := rho.mem_signedCandidate.mp ho
    have ha := congrArg Model.Obj.auth he
    cases ha
  | pollPropose n =>
    have hempty : ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose n)).2 =
        [] := by
      simp only [Model.protoOf, compiled, compile, goldilocks, dite_eq_left hn, goldilocksShape]
      rfl
    obtain ⟨body, cs, hm, _, _⟩ := rho.mem_signedCandidate.mp ho
    rw [hempty] at hm
    cases hm

private theorem dutyBatches_vote_stamp (v : V) (u : Time) :
    ∀ (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)),
    VoteQueueStamped u (shapeOf S hn nd) →
    ∀ b ∈ dutyBatches rho v nd ds, ∀ t (m : SA.Vote (Fintype.card V)),
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ b.candidates → t = u := by
  intro ds
  induction ds with
  | nil => intro nd hs b hb; rw [dutyBatches_nil] at hb; cases hb
  | cons d ds ih =>
    intro nd hs b hb t m ho
    rw [dutyBatches_cons] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · split at ho
      · exact duty_vote_stamp S rho hn v nd d u hs ho
      · cases ho
    · exact ih _ (dutyStep_pres S rho hn (VoteQueueStamped u)
        (voteStamped_recordOwn u) (voteStamped_propose u) (voteStamped_nodeTick u)
        (voteStamped_poll u) v nd d hs) b hb t m ho

private theorem dutyBatches_vote_pool (v : V) :
    ∀ (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)),
    (∀ q ∈ (shapeOf S hn nd).voteForwards,
      q.2 ∈ (shapeOf S hn nd).node.ac.pool q.2.slot) →
    ∀ b ∈ dutyBatches rho v nd ds, ∀ t (m : SA.Vote (Fintype.card V)),
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ b.candidates →
      m ∈ (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool m.slot := by
  intro ds
  induction ds with
  | nil => intro nd hp b hb; rw [dutyBatches_nil] at hb; cases hb
  | cons d ds ih =>
    intro nd hp b hb t m ho
    rw [dutyBatches_cons] at hb
    rw [rho.runDuties_cons]
    rcases List.mem_cons.mp hb with rfl | hb
    · have hm : m ∈ (shapeOf S hn nd).node.ac.pool m.slot := by
        split at ho
        · exact duty_vote_pool S rho hn v nd d hp ho
        · cases ho
      exact runDuties_pool_subset S rho hn v _ ds m.slot
        (dutyStep_pool_subset S rho hn v nd d m.slot hm)
    · exact ih _ (dutyStep_voteForward_in_pool S rho hn v nd d hp) b hb t m ho

include hn in
/-- Every released vote envelope carries the actual sending event's time, including
ticks and recursively processed deliveries. No first-release premise is used. -/
theorem released_voteForward_stamp (hv : rho.ExecutionValid) {i : Nat} {v : V} {u t : Time}
    (he : rho.SendsAt v i u) (m : SA.Vote (Fintype.card V))
    (ho : Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i) : t = u := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho he ho
  have hg : ∀ nd, Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉
        Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd u := by
    intro nd h
    obtain ⟨mc, _, heq⟩ := Model.mem_gossipCandidates.mp h
    have ha := congrArg Model.Obj.auth heq
    cases ha
  rcases he with he | ⟨receipt, he⟩
  · rw [eventBatches_eq, he] at hb
    simp only at hb
    split at hb
    · rcases List.mem_append.mp hb with hb | hb
      · apply dutyBatches_vote_stamp S rho hn v u _ _ ?_ b hb t m ho
        change VoteQueueStamped u { (rho.stateBefore i v).st.1 hn with now := u }
        rw [← stateAt_eq S rho hn v i]
        refine ⟨rfl, ?_⟩
        intro q hq
        change q ∈ (stateAt S rho hn v i).voteForwards at hq
        rw [voteForwards_empty S rho hn hv v i] at hq
        cases hq
      · obtain rfl := List.mem_singleton.mp hb
        exact False.elim (hg _ ho)
    · cases hb
  · rw [eventBatches_eq, he] at hb
    rcases List.mem_append.mp hb with hb | hb
    · apply dutyBatches_vote_stamp S rho hn v u _ _ ?_ b hb t m ho
      change VoteQueueStamped u
        (process ((rho.stateBefore i v).st.1 hn) receipt (Model.digests rho.hash receipt))
      rw [← stateAt_eq S rho hn v i]
      apply voteStamped_process
      refine ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he), ?_⟩
      intro q hq
      rw [voteForwards_empty S rho hn hv v i] at hq
      cases hq
    · obtain rfl := List.mem_singleton.mp hb
      exact False.elim (hg _ ho)

include hn in
/-- Every released vote envelope is backed by its sender's pool at the end of
the sending event, for ticks as well as recursive deliveries. -/
theorem released_voteForward_pool (hv : rho.ExecutionValid) {i : Nat} {v : V} {u t : Time}
    (he : rho.SendsAt v i u) (m : SA.Vote (Fintype.card V))
    (ho : Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i) :
    m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho he ho
  have hg : ∀ nd, Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉
        Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd u := by
    intro nd h
    obtain ⟨mc, _, heq⟩ := Model.mem_gossipCandidates.mp h
    have ha := congrArg Model.Obj.auth heq
    cases ha
  rcases he with he | ⟨receipt, he⟩
  · rw [eventBatches_eq, he] at hb
    simp only at hb
    split at hb
    · rename_i hawake
      rcases List.mem_append.mp hb with hb | hb
      · rw [stateAt_tick S rho hn v he]
        simp only [Model.Run.tick, hawake, ↓reduceIte]
        rw [gossip_node_eq]
        apply dutyBatches_vote_pool S rho hn v _ _ ?_ b hb t m ho
        intro q hq
        change q ∈ ((rho.stateBefore i v).st.1 hn).voteForwards at hq
        rw [← stateAt_eq S rho hn v i] at hq
        rw [voteForwards_empty S rho hn hv v i] at hq
        cases hq
      · obtain rfl := List.mem_singleton.mp hb
        exact False.elim (hg _ ho)
    · cases hb
  · rw [eventBatches_eq, he] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [stateAt_deliver S rho hn v he]
      simp only [Model.Run.deliver]
      rw [gossip_node_eq]
      apply dutyBatches_vote_pool S rho hn v _ _ ?_ b hb t m ho
      have h := delivery_voteForward_in_pool S rho hn hv v i receipt
      rw [stateAt_eq] at h
      exact h
    · obtain rfl := List.mem_singleton.mp hb
      exact False.elim (hg _ ho)

omit [DecidableEq V] in
/-- Vote envelopes drain after the actual ordinary/block release prefix when their canonical
votes are held there. No success assumption is imposed on the prefix candidates themselves. -/
theorem releaseAll_voteForward_suffix (hash : Blocks.Header Info → Nat)
    (x : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (pre : List (Model.protoOf (compiled (goldilocks S)) E).Object)
    (vs : List (Time × SA.Vote (Fintype.card V)))
    (hheld : ∀ tv ∈ vs, voteObj tv.2 ∈ Model.closure
      (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) hash x nd pre).1.seen) :
    let cs : List (Model.protoOf (compiled (goldilocks S)) E).Object := vs.map fun tv =>
      .mk (.signed x .poll) (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2]
    (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) hash x nd (pre ++ cs)).2 =
      (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) hash x nd pre).2 ++ cs := by
  dsimp only
  erw [Model.releaseAll_append (P := Model.protoOf (compiled (goldilocks S)) E)]
  dsimp only
  congr 1
  apply (releaseAll_of_prefix_guards (Model.protoOf (compiled (goldilocks S)) E)
    hash x _ _ ?_).1
  intro i o hi
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hi)
  refine ⟨releasable_voteForward S x _ tv.1 tv.2 ?_,
    protects_voteForward S x x _ tv.1 tv.2, dependencies_voteForward _ x tv.1 tv.2⟩
  exact Model.closure_mono (fun _ h => List.mem_append_left _ h) (hheld tv htv)

omit [DecidableEq V] in
/-- The actual poll releases its vote envelopes when their canonical votes are held after
the ordinary/block prefix. This permits an own vote first released by this very poll. -/
theorem dutyStep_poll_voteForward_of_prefix (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hheld : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      voteObj tv.2 ∈ Model.closure
        (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v)
          ⟨((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll t)).1, nd.seen⟩
          (((poll (shapeOf S hn nd) t).2.toList.map fun q =>
            Model.Obj.mk (.signed (rho.ownKey v) .poll) (.data q.1) q.2) ++
            pendingWrappers (shapeOf S hn nd))).1.seen) :
    ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈
          (rho.dutyStep v nd (.poll t)).2 := by
  intro tv htv
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [signedCandidate_poll_eq S rho hn v nd t hsel hself]
  erw [releaseAll_voteForward_suffix S rho.hash (rho.ownKey v)
    ⟨((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll t)).1, nd.seen⟩ _ _ hheld]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨tv, htv, rfl⟩)

omit [DecidableEq V] in
/-- A selected poll publishes every queued envelope whose canonical vote is already held.
The intervening ordinary/block candidates preserve these holdings even if their guards fail. -/
theorem dutyStep_poll_voteForward (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hheld : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      voteObj tv.2 ∈ Model.closure nd.seen) :
    ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈
          (rho.dutyStep v nd (.poll t)).2 := by
  apply dutyStep_poll_voteForward_of_prefix S rho hn v nd t hsel hself
  intro q hq
  erw [Model.releaseAll_seen]
  exact Model.closure_mono (fun _ h => List.mem_append_left _ h) (hheld q hq)

omit [DecidableEq V] in
/-- A canonical vote at the head of the actual ordinary poll output supplies its own
envelope's dependency. Other queued votes need only be held already; block guards may fail. -/
theorem dutyStep_poll_voteForward_of_own_vote (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (m : SA.Vote (Fintype.card V)) (hm : m.val = rho.ownKey v)
    (hout : (pollPre (shapeOf S hn nd)).outbox.head? = some (.vote (encodeVote m)))
    (hheld : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 = m ∨ voteObj tv.2 ∈ Model.closure nd.seen) :
    ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈
          (rho.dutyStep v nd (.poll t)).2 := by
  apply dutyStep_poll_voteForward_of_prefix S rho hn v nd t hsel hself
  intro tv htv
  rcases hheld tv htv with he | he
  · rw [he]
    erw [Model.releaseAll_seen]
    apply Model.mem_closure_of_mem
    apply List.mem_append_right
    rw [(poll_outbox _ _).2, hout]
    simp only [Option.map_some, Option.toList_some, List.map_singleton, List.singleton_append]
    have heq : Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.vote (encodeVote m))) [] = voteObj m := by
      simp only [voteObj, hm]
    rw [heq]
    erw [Model.releaseAll.eq_def]
    dsimp only
    split
    · exact List.mem_cons_self
    · rename_i h
      exfalso
      apply h
      apply Bool.and_eq_true_iff.mpr
      refine ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩
      · rfl
      · exact protects_of_not_att S _ _ _ (fun k w h => by cases h)
      · rfl
  · erw [Model.releaseAll_seen]
    exact Model.closure_mono (fun _ h => List.mem_append_left _ h) he

/-- A poll with at most one ordinary pending body releases its vote queue when
each dependency is held or pending. The FG update appends only an attestation. -/
theorem dutyStep_poll_voteForward_of_available (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i p : Nat}
    {nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)}
    (hc : EngineDutyCut S rho v i p nd) (t : Nat)
    (hlen : (shapeOf S hn nd).outbox.length ≤ 1)
    (hav : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      voteObj q.2 ∈ Model.closure nd.seen ∨
        Body.vote (encodeVote q.2) ∈ (shapeOf S hn nd).outbox) :
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t)).2 := by
  have hself := cut_self S rho hn hc
  by_cases hh : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      voteObj q.2 ∈ Model.closure nd.seen
  · exact dutyStep_poll_voteForward S rho hn v nd t (poll_selected S rho hv v) hself hh
  · push Not at hh
    obtain ⟨q, hq, hnot⟩ := hh
    have hmem := (hav q hq).resolve_left hnot
    have hlist : (shapeOf S hn nd).outbox = [.vote (encodeVote q.2)] := by
      cases ho : (shapeOf S hn nd).outbox with
      | nil => simp [ho] at hmem
      | cons b bs =>
        have hb : bs = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [ho, List.length_cons] at hlen
          omega
        subst bs
        have hb := List.mem_singleton.mp (ho ▸ hmem)
        exact congrArg (fun b => [b]) hb.symm
    have hhead : (pollPre (shapeOf S hn nd)).outbox.head? = some (.vote (encodeVote q.2)) := by
      rw [pollPre_eq]
      split
      · rcases fgUpdate_outbox (shapeOf S hn nd) with h | ⟨a, h⟩ <;> rw [h, hlist] <;> rfl
      · rw [hlist]; rfl
    apply dutyStep_poll_voteForward_of_own_vote S rho hn v nd t
      (poll_selected S rho hv v) hself q.2
      (duty_cut_vote_signer S rho hn hv hv' hc q.2 hmem) hhead
    intro r hr
    rcases hav r hr with h | h
    · exact Or.inr h
    · rw [hlist, List.mem_singleton] at h
      have hd := congrArg (decodeVote (Fintype.card V)) (Body.vote.inj h)
      exact Or.inl (by simpa only [decodeVote_encodeVote, Option.some.injEq] using hd)

/-- At an actual tick prefix with at most one pending ordinary body, a poll
releases every queued vote envelope. Holdings are supplied by reachable inventory. -/
theorem tick_prefix_voteForward_poll (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i p : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : p ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length) :
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      (((Model.protoOf (compiled (goldilocks S)) E).duties t).take p)).1
    (shapeOf S hn nd).outbox.length ≤ 1 →
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
  intro nd hlen
  apply dutyStep_poll_voteForward_of_available S rho hn hv hv' (.tick he hw hp) t.toNat hlen
  intro q hq
  apply tick_prefix_pool_available S rho hn hv hv' he hw hp q.2.slot q.2
  apply runDuties_voteForward_in_pool S rho hn v _ _ ?_ q hq
  intro r hr
  change r ∈ ((rho.stateBefore i v).st.1 hn).voteForwards at hr
  rw [← stateAt_eq S rho hn v i] at hr
  rw [voteForwards_empty S rho hn hv v i] at hr
  cases hr

/-- The tick's first trailing poll has the required one-body bound and releases
all vote envelopes queued by the node tick and the optional own proposal. -/
theorem tick_trailing_voteForward_poll (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    let pre : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ (skeleton (pubOf E)).proposeAt t
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
  intro pre nd
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hd : (Model.protoOf (compiled (goldilocks S)) E).duties t =
      pre ++ [.poll t.toNat, .poll t.toNat] := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  have htake : ((Model.protoOf (compiled (goldilocks S)) E).duties t).take pre.length = pre := by
    rw [hd, List.take_left]
  have hlen : pre.length ≤ ((Model.protoOf (compiled (goldilocks S)) E).duties t).length := by
    rw [hd, List.length_append]
    omega
  have h := tick_prefix_voteForward_poll S rho hn hv hv' he hw hlen
  rw [htake] at h
  apply h
  dsimp only [nd, pre]
  erw [runDuties_fst_append]
  apply outbox_after_pre S rho hn v (stateAt S rho hn v i) t ht
    (fgDue_eq_false S rho hn v i)
  · rw [outbox_empty S rho hn hv v hv' i]; simp
  · rw [stateAt_eq]
    exact pre_shape S rho hn v (rho.stateBefore i v) t (poll_selected S rho hv v)

omit [DecidableEq V] in
/-- Through the optional proposal, every newly pooled vote is queued at the unchanged clock. -/
theorem proposal_pool_insertion_queued (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time)
    (m : SA.Vote (Fintype.card V))
    (hbase : m ∈ (shapeOf S hn nd).node.ac.pool m.slot →
      ((shapeOf S hn nd).now, m) ∈ (shapeOf S hn nd).voteForwards) :
    let out := (rho.runDuties v nd ((skeleton (pubOf E)).proposeAt t)).1
    m ∈ (shapeOf S hn out).node.ac.pool m.slot →
      ((shapeOf S hn nd).now, m) ∈ (shapeOf S hn out).voteForwards := by
  let Q := fun st : State (S.params (pubOf E) hn) (S.ro _) =>
    st.now = (shapeOf S hn nd).now ∧
      (m ∈ st.node.ac.pool m.slot → ((shapeOf S hn nd).now, m) ∈ st.voteForwards)
  have hrec : ∀ st o hs, Q st → Q (recordOwn st o hs) := by
    intro st o hs h
    refine ⟨(recordOwn_now st o hs).trans h.1, ?_⟩
    intro hm
    by_cases hold : m ∈ st.node.ac.pool m.slot
    · exact recordOwn_voteForwards_subset st o hs (h.2 hold)
    · rw [← h.1]
      exact recordOwn_pool_insertion_queued st o hs m hold hm
  have hprop : ∀ st s, Q st → Q (propose st s).1 := by
    intro st s h
    have hp : (propose st s).1.node.ac.pool = st.node.ac.pool := by
      have hp : (Node.acProposal st.node st.now).1.ac.pool = st.node.ac.pool := by
        change (SA.acProposal _ st.node.ac (Node.frame st.node) st.now).1.pool = _
        unfold SA.acProposal
        split_ifs <;> rfl
      unfold propose
      dsimp only
      split <;> exact hp
    refine ⟨(propose_now st s).trans h.1, ?_⟩
    rw [hp, propose_voteForwards]
    exact h.2
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with ⟨h, -⟩ | ⟨s, hs, h, -⟩
  · rw [h]; exact hbase
  · rw [h]
    exact (dutyStep_propose_pres S rho hn Q hrec hprop v nd s hs ⟨rfl, hbase⟩).2

/-- Envelopes queued before the tick's trailing polls are released by that tick. -/
theorem tick_voteForward_released (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    let pre : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ (skeleton (pubOf E)).proposeAt t
    let nd := (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1
    ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈ rho.releasesAt i := by
  intro pre nd q hq
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hrel := tick_trailing_voteForward_poll S rho hn hv hv' he q hq
  simp only [Model.Run.releasesAt, he]
  rw [rho.tick_of_awake _ _ _ (hv.tick_awake v t (List.mem_of_getElem? he))]
  apply List.mem_append_left
  have hd : (Model.protoOf (compiled (goldilocks S)) E).duties t =
      pre ++ .poll t.toNat :: [.poll t.toNat] := by
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  rw [hd]
  exact duty_release_in_runDuties S rho v _ pre _ _ _ hrel

/-- A tick's aggregate pool difference is queued before its trailing polls and released. -/
theorem tick_pool_insertion_released (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i := by
  have hsel := poll_selected S rho hv v
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have hbase : m ∈ (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node.ac.pool m.slot →
      (t, m) ∈ (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).voteForwards := by
    rw [atProposal_shape S rho hn v _ t hsel]
    rw [← stateAt_eq S rho hn v i]
    let st := (poll (poll { stateAt S rho hn v i with now := t } t.toNat).1 t.toNat).1
    have hn' : st.node = (stateAt S rho hn v i).node := by
      dsimp only [st]
      rw [poll_node_of_fgDue _ _ (poll_fgDue _ _)]
      exact poll_node_of_fgDue { stateAt S rho hn v i with now := t } _
        (fgDue_eq_false S rho hn v i)
    have ht' : st.now = t := by dsimp only [st]; rw [poll_now, poll_now]
    intro hm
    have hq := nodeTick_pool_insertion_queued st m (hn' ▸ hold) hm
    rwa [ht'] at hq
  have hpool : m ∈ (shapeOf S hn (rho.runDuties v
      (atProposal S rho v (rho.stateBefore i v) t)
      ((skeleton (pubOf E)).proposeAt t)).1).node.ac.pool m.slot := by
    rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw hsel,
      poll_pool_eq, poll_pool_eq] at hnew
    exact hnew
  have hq := proposal_pool_insertion_queued S rho hn v
    (atProposal S rho v (rho.stateBefore i v) t) t m
    (by rw [atProposal_now S rho hn v _ t hsel]; exact hbase) hpool
  rw [atProposal_now S rho hn v _ t hsel] at hq
  apply tick_voteForward_released S rho hn hv hv' he (t, m)
  erw [runDuties_fst_append]
  rw [atProposal_eq] at hq
  exact hq

/-- Every envelope actually queued during delivery is released in that same engine event.
Canonical dependencies are derived from reachable inventory and the actual ordinary prefix. -/
theorem delivery_voteForward_released (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (tv : Time × SA.Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈ rho.releasesAt i := by
  have hv' := hv.honest_only _ (List.mem_of_getElem? he)
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  let nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
    ⟨(Model.protoOf (compiled (goldilocks S)) E).process (rho.stateBefore i v).st o
      (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
  have hshape : shapeOf S hn nd =
      process (stateAt S rho hn v i) o (Model.digests rho.hash o) := by
    rw [stateAt_eq]
    rfl
  have hself : (shapeOf S hn nd).self = rho.ownKey v := by
    rw [hshape]
    exact (process_self _ _ _).trans (stateAt_self S rho hn v i)
  have hfg : (shapeOf S hn nd).fgDue = false := by
    rw [hshape]
    exact (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
  have hpre : pollPre (shapeOf S hn nd) = shapeOf S hn nd := by
    rw [pollPre_eq, hfg]; rfl
  have hav : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      voteObj q.2 ∈ Model.closure nd.seen ∨
        (shapeOf S hn nd).outbox.head? = some (.vote (encodeVote q.2)) := by
    intro q hq
    rw [hshape]
    exact delivery_voteForward_held_or_head S rho hn hv he q (hshape ▸ hq)
  have hrel : ∀ q ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward q.1 (encodeVote q.2))) [voteObj q.2] ∈
          (rho.dutyStep v nd (.poll t.toNat)).2 := by
    by_cases hh : ∀ q ∈ (shapeOf S hn nd).voteForwards, voteObj q.2 ∈ Model.closure nd.seen
    · exact dutyStep_poll_voteForward S rho hn v nd t.toNat (poll_selected S rho hv v) hself hh
    · push Not at hh
      obtain ⟨q, hq, hnot⟩ := hh
      have hhead := (hav q hq).resolve_left hnot
      have hsign := delivery_outbox_vote_signer S rho hn hv hv' i o q.2
        (List.mem_of_mem_head? (Option.mem_def.mpr (hshape ▸ hhead)))
      apply dutyStep_poll_voteForward_of_own_vote S rho hn v nd t.toNat
        (poll_selected S rho hv v) hself q.2 hsign (by rw [hpre]; exact hhead)
      intro r hr
      rcases hav r hr with h | h
      · exact Or.inr h
      · left
        have heq := Body.vote.inj (Option.some.inj (h.symm.trans hhead))
        have hd := congrArg (decodeVote (Fintype.card V)) heq
        simpa only [decodeVote_encodeVote, Option.some.injEq] using hd
  have hout := hrel tv (hshape ▸ htv)
  simp only [Model.Run.releasesAt, he]
  unfold Model.Run.deliver
  rw [deliverDuties_eq S t ht]
  apply List.mem_append_left
  erw [Model.Run.runDuties_cons]
  exact List.mem_append_left _ hout

/-- A delivery's aggregate pool difference suffices for same-event forwarding,
without identifying which nested message or block handler made the insertion. -/
theorem delivery_pool_insertion_released (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) (m : SA.Vote (Fintype.card V))
    (hold : m ∉ (stateAt S rho hn v i).node.ac.pool m.slot)
    (hnew : m ∈ (stateAt S rho hn v (i + 1)).node.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i := by
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  have hnode : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node =
      (stateAt S rho hn v (i + 1)).node := by
    rw [node_of_deliver S rho hn hv v (hv.honest_only _ (List.mem_of_getElem? he)) i o t he]
    unfold process
    erw [foldl_processOne_node (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) (digestOf S rho)]
    rw [stateAt_self, hnow]
  apply delivery_voteForward_released S rho hn hv he (t, m)
  rw [← hnow]
  unfold process
  exact foldl_processOne_pool_insertion_queued (sp := S.params (pubOf E) hn)
    (ro := S.ro _) (Model.digests rho.hash o) _ (stateAt S rho hn v i) m hold
    (show m ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node.ac.pool m.slot
      from hnode.symm ▸ hnew)

/-- An honest emission cut cannot be a restart, even though `EmitAt` permits that call
syntactically. This uses the actual cut law and the run's nonnegative clock. -/
theorem simTrace_emission_not_restart (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho) {k : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hc : (simTrace S rho hn).CallAt y k (.ac ℓ))
    {e : SA.Em (S.params (pubOf E) hn) (List (FG.Att (Fintype.card V)))}
    (he : e ∈ ℓ.emits) : ℓ.call ≠ .restart := by
  intro hr
  have hrun := simTrace_goldilocksRun S rho hn hv
  have hstep := (hrun.cutLaw y hy k _ hc).2.1
  rw [hr] at hstep
  have hnil := restart_emits_nil (S.ro _) y (simTrace S rho hn |>.state y k).ac
    ℓ.frame ((simTrace S rho hn).time k) (hrun.time_nonneg k)
  have hemits := congrArg Prod.snd hstep
  rw [hnil] at hemits
  have hempty : ℓ.emits = [] := hemits.symm
  rw [hempty] at he
  exact List.not_mem_nil he

/-- The first trace cut of a public tick is its actual AC-tick call. -/
theorem tick_boundary_call (hv : rho.ExecutionValid) {v : V}
    (hv' : v ∈ rho.honest) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (simTrace S rho hn).CallAt (rho.ownKey v) (cutMap S rho hn i)
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).2 ∧
      (simTrace S rho hn).time (cutMap S rho hn i) = t := by
  have hg := (simTrace_tick_public_group S rho hn hv v hv' i t he hp).1
  have hstate := simTrace_state S rho hn hv v hv' i
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  have hlen : 0 < (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
    exact List.length_pos_iff.mpr hg.1
  obtain ⟨hnode, htime, -, -, hlabel⟩ := hg.2.1 0 hlen
  have hget : (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2[0]'hlen =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).2 := by
    change (Node.acCall (rho.ownKey v)
      ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .tick).2 = _
    rw [hstate]
  rw [hget] at hlabel
  exact ⟨⟨by simpa only [Nat.add_zero] using hnode,
    by simpa only [Nat.add_zero] using hlabel⟩, by simpa only [Nat.add_zero] using htime⟩

/-- A trace restart is produced by an actual engine restart, never by tick or
recursive delivery processing. The interval identifies its exact engine event. -/
theorem simTrace_restart_event {y : Fin (Fintype.card V)} {k : Nat}
    (hr : (simTrace S rho hn).RestartAt y k) :
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.events[i]? = some (.restart (rho.key y) ((simTrace S rho hn).time k)) := by
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hr
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, hlo, hhi, hidx, hn', ht, -, hlab'⟩ :=
    simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he (List.mem_of_getElem? hidx) hrl hcall
  have hkey : v = rho.key y := by
    have hk := congrArg rho.key (hn'.symm.trans hnode)
    exact (rho.key.apply_symm_apply v).symm.trans hk
  exact ⟨i, hlo, hhi, by simpa only [hkey, ht, Model.Event.time] using he⟩

/-- An engine interval without this node's restarts contains no restart cuts for
that node. This supplies the cut-level premise needed for pool monotonicity. -/
theorem simTrace_noRestart_between {y : Fin (Fintype.card V)} {a b k : Nat}
    (hnr : ∀ i, a ≤ i → i < b → ∀ t,
      rho.events[i]? ≠ some (.restart (rho.key y) t))
    (ha : cutMap S rho hn a ≤ k) (hb : k < cutMap S rho hn b) :
    ¬ (simTrace S rho hn).RestartAt y k := by
  intro hr
  obtain ⟨i, hlo, hhi, he⟩ := simTrace_restart_event S rho hn hr
  have hai : a ≤ i := by
    by_contra h
    have hm := cutMap_mono S rho hn (show i + 1 ≤ a by omega)
    omega
  have hib : i < b := by
    by_contra h
    have hm := cutMap_mono S rho hn (show b ≤ i by omega)
    omega
  exact hnr i hai hib _ he

/-- Restarts precede all sending events at a fixed time, so none can intervene
between two such events, even for a different node. -/
theorem noRestart_between_same_time_sends (hv : rho.ExecutionValid)
    {v : V} {a b : Nat} {t : Time} (ha : rho.SendsAt v a t) (hb : rho.SendsAt v b t)
    {j : Nat} (haj : a ≤ j) (hjb : j < b) (w : V) (u : Time) :
    rho.events[j]? ≠ some (.restart w u) := by
  intro hr
  have haj' : a < j := by
    rcases haj.lt_or_eq with h | rfl
    · exact h
    · rcases ha with ha | ⟨o, ha⟩ <;> rw [hr] at ha <;> cases ha
  have hle : u ≤ t := by
    rcases hb with hb | ⟨o, hb⟩ <;>
      rcases keyLe_of_index_lt S rho hv hr hb hjb with h | h
    all_goals first | exact h.le | exact h.1.le
  rcases ha with ha | ⟨o, ha⟩ <;>
    rcases keyLe_of_index_lt S rho hv ha hr haj' with h | h
  all_goals first
    | exact (not_lt_of_ge hle) h
    | simpa only [Model.Event.phase, Nat.reduceLeDiff] using h.2

/-- Retention also covers the later sending event's own cuts: its event cannot
be a restart. This is the interval needed for a fresh admission inside that event. -/
theorem pool_mono_through_same_time_send (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {a b : Nat} {t : Time} (ha : rho.SendsAt (rho.key y) a t)
    (hb : rho.SendsAt (rho.key y) b t) {k l : Nat}
    (hak : cutMap S rho hn a ≤ k) (hkl : k ≤ l)
    (hlb : l ≤ cutMap S rho hn (b + 1)) (σ : Nat) :
    ((simTrace S rho hn).state y k).ac.pool σ ⊆
      ((simTrace S rho hn).state y l).ac.pool σ := by
  have hr := simTrace_goldilocksRun S rho hn hv
  have hnr : ∀ i, a ≤ i → i < b + 1 → ∀ u,
      rho.events[i]? ≠ some (.restart (rho.key y) u) := by
    intro i hai hib u he
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hib) with hib | rfl
    · exact noRestart_between_same_time_sends S rho hv ha hb hai hib _ u he
    · rcases hb with hb | ⟨o, hb⟩ <;> rw [he] at hb <;> cases hb
  have hm := Compose.pool_mono hr hy hkl (fun j hkj hjl =>
    simTrace_noRestart_between S rho hn hnr (hak.trans hkj) (hjl.trans_le hlb)) σ
  simpa only [Compose.projAC_state hr.toLocalRun hy] using hm

/-- Freshness at any sending-event cut gives an aggregate boundary pool insertion.
Non-restart retention covers both sides of the source cut. -/
theorem sending_event_pool_insertion (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap S rho hn i ≤ k) (hhi : k < cutMap S rho hn (i + 1))
    (hc : (simTrace S rho hn).IsCall y k)
    (hold : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot)
    (hnew : m ∈ ((simTrace S rho hn).post k).ac.pool m.slot) :
    m ∉ (stateAt S rho hn (rho.key y) i).node.ac.pool m.slot ∧
      m ∈ (stateAt S rho hn (rho.key y) (i + 1)).node.ac.pool m.slot := by
  have hi : i < rho.events.length := by
    rcases hs with h | ⟨o, h⟩ <;> exact (List.getElem?_eq_some_iff.mp h).1
  have hstate (j : Nat) (hj : j ≤ rho.events.length) :
      (stateAt S rho hn (rho.key y) j).node =
        (simTrace S rho hn).state y (cutMap S rho hn j) := by
    simpa only [Model.Run.ownKey, Equiv.symm_apply_apply] using
      simTrace_state S rho hn hv (rho.key y) ((mem_honestKeys_iff S rho y).mp hy) j hj
  constructor
  · rw [hstate i hi.le]
    intro hm
    exact hold (pool_mono_through_same_time_send S rho hn hv hy hs hs le_rfl hlo hhi.le _ hm)
  · rw [hstate (i + 1) (by omega)]
    apply pool_mono_through_same_time_send S rho hn hv hy hs hs
      (hlo.trans (Nat.le_succ k)) (by omega) le_rfl m.slot
    obtain ⟨c, hc⟩ := hc
    rwa [(simTrace S rho hn).state_succ_of_call hc]

/-- Fresh admission rules out an earlier exact envelope once every earlier release
is backed by a pool cut in its event. Only that release-to-pool supplier remains
explicit; stamp authentication and restart-free retention are proved here. -/
theorem admission_voteForward_first_of_release_pool (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap S rho hn i ≤ k) (hhi : k < cutMap S rho hn (i + 1))
    (hf : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot)
    (hpool : ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt j →
      ∃ c, cutMap S rho hn j ≤ c ∧ c ≤ cutMap S rho hn (j + 1) ∧
        m ∈ ((simTrace S rho hn).state y c).ac.pool m.slot) :
    ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉ rho.releasesAt j := by
  intro j hji hj
  obtain ⟨u, hsend⟩ := voteForward_release_sender S rho hj
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
  have ht : t = u := released_voteForward_stamp S rho hn hv hsend m (by simpa only [hkey] using hj)
  subst u
  obtain ⟨c, hjc, hcj, hm⟩ := hpool j hji hj
  have hck := hcj.trans ((cutMap_mono S rho hn (Nat.succ_le_of_lt hji)).trans hlo)
  exact hf (pool_mono_through_same_time_send S rho hn hv hy hsend hs hjc hck hhi.le m.slot hm)

/-- A fresh admission's exact signed envelope has no earlier release, even when
the original vote signer is faulty. Event pool provenance discharges the supplier. -/
theorem admission_voteForward_first (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {i k : Nat} {t : Time} {m : SA.Vote (Fintype.card V)}
    (hs : rho.SendsAt (rho.key y) i t)
    (hlo : cutMap S rho hn i ≤ k) (hhi : k < cutMap S rho hn (i + 1))
    (hf : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot) :
    ∀ j < i, Model.Obj.mk (.signed y .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∉ rho.releasesAt j := by
  apply admission_voteForward_first_of_release_pool S rho hn hv hy hs hlo hhi hf
  intro j _ hj
  obtain ⟨u, hsend⟩ := voteForward_release_sender S rho hj
  have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
  have hm := released_voteForward_pool S rho hn hv hsend m (by simpa only [hkey] using hj)
  have hjlen : j + 1 ≤ rho.events.length := by
    rcases hsend with he | ⟨o, he⟩ <;>
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp he).1
  rw [simTrace_state S rho hn hv (rho.key y) ((mem_honestKeys_iff S rho y).mp hy)
    (j + 1) hjlen, hkey] at hm
  exact ⟨cutMap S rho hn (j + 1), cutMap_mono S rho hn (Nat.le_succ j), le_rfl, hm⟩

/-- Every non-restart AC cut lies in a sending engine event of the same node and time.
This is interval transport only; it does not assume the publication supplier. -/
theorem simTrace_call_sending_event {y : Fin (Fintype.card V)} {k : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hc : (simTrace S rho hn).CallAt y k (.ac ℓ)) (hnr : ℓ.call ≠ .restart) :
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTrace S rho hn).time k) := by
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hc.2]; simp
  obtain ⟨r, i, ev, -, he, hlo, hhi, hidx, hnode, ht, -, hlabel⟩ :=
    simTrace_cut S rho hn hl
  have hkey : rho.key y = ev.node := by
    rw [← hc.1, hnode]
    exact rho.key.apply_symm_apply ev.node
  refine ⟨i, hlo, hhi, ?_⟩
  rw [hkey, ht]
  cases ev with
  | tick v t => exact Or.inl he
  | deliver v o t => exact Or.inr ⟨o, he⟩
  | restart v t =>
    have hr := List.mem_of_getElem? hidx
    rw [eventCuts_restart S rho hn i v t he] at hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hj' := hj
    rw [length_groupRecs] at hj'
    have hj0 : j = 0 := by
      simpa only [Node.exec, Node.restart, List.length_singleton, Nat.lt_one_iff] using hj'
    subst j
    have hrl := (getElem_groupRecs _ _ _ _ _ _ _ 0 hj).2.2.2.2
    have heq := Option.some.inj (hlabel.symm.trans hc.2)
    rw [hrl] at heq
    have hcall := congrArg (fun c => match c with | .ac l => l.call | _ => .restart) heq
    exact False.elim (hnr hcall.symm)

/-- A vote carried by an actual receipt is processed at a cut of that same event.
No fresh insertion, honest signer, or pool-cap premise is required. -/
theorem received_vote_processAt {i : Nat} {v : V}
    {receipt : Wire (Fintype.card V)} {u : Time} {m : SA.Vote (Fintype.card V)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt (voteObj m)) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTrace S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTrace S rho hn).time k = u := by
  obtain ⟨r, hr, ℓ, hl, hm⟩ := deliverRecs_message_call (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash receipt) (rho.ownKey v) u i m
    (delivered _ receipt) (stateAt S rho hn v i).node 0
    ⟨voteObj m, by simpa only [delivered, Model.Obj.Contains] using hc,
      canonEvent_voteObj (sp := S.params (pubOf E) hn) (ro := S.ro _)
        (Model.digests rho.hash receipt) m⟩
  obtain ⟨hn', ht', _⟩ := mem_deliverRecs (sp := S.params (pubOf E) hn)
    (ro := S.ro _) (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (Model.digests rho.hash receipt) u i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt u he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  refine ⟨cutMap S rho hn i + j, Nat.le_add_right _ _, ?_, ?_, ?_⟩
  · rw [cutMap_succ]
    omega
  · refine ⟨ℓ, Compose.projAC_callAt.mpr ⟨?_, ?_⟩, Or.inl hm⟩
    · simpa only [simTrace_node, hk, Option.elim_some] using hn'
    · simp [simTrace_label, hk, hl]
  · simpa only [simTrace_time, hk, Option.elim_some] using ht'

/-- An AC block cut in an actual delivery comes from that receipt's canonical block.
Consequently its payload votes also receive explicit message processing in that event. -/
theorem delivery_block_payload_processAt {i : Nat} {v : V}
    {receipt : Wire (Fintype.card V)} {u : Time}
    {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    {B : Blk (S.params (pubOf E) hn)} {m : SA.Vote (Fintype.card V)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hr : r ∈ eventCuts S rho hn i) (hl : r.label = .ac ℓ)
    (hb : ℓ.call = .block B) (hm : m ∈ SA.blockVotes B) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTrace S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTrace S rho hn).time k = u := by
  rw [eventCuts_deliver S rho hn i v receipt u he] at hr
  obtain ⟨o, e, st, ho, hce, q, hq, hlabel, _⟩ :=
    mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hr
  have hcut := List.getElem_mem hq
  rw [← hlabel, hl] at hcut
  have heq : e = .block B := by
    cases e with
    | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
    | block B' =>
      simp only [Node.exec, Node.onBlock] at hcut
      split_ifs at hcut
      · simp at hcut
      · split at hcut <;> simp [Node.acCall] at hcut
        subst ℓ
        cases hb
        rfl
    | message m' =>
      simp only [Node.exec, Node.onMessage, Node.acCall, List.mem_singleton,
        Cut.ac.injEq] at hcut
      subst ℓ
      cases hb
    | attestation => simp [Node.exec, Node.onAttestation] at hcut
    | restart =>
      simp only [Node.exec, Node.restart, Node.acCall, List.mem_singleton,
        Cut.ac.injEq] at hcut
      subst ℓ
      cases hb
  subst e
  obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
  have hp : voteObj m ∈ payloadObjs B.fgPayload B.acPayload :=
    List.mem_append_right _ (List.mem_map.mpr ⟨m, List.mem_append_left _ hm, rfl⟩)
  exact received_vote_processAt S rho hn he
    ((contains_of_mem_delivered ho).trans (Model.Obj.Contains.step hp (.refl _)))

/-- An authenticated vote envelope received after its globally first release yields
processing no earlier than that release. The first-release premise is essential:
the wire timestamp alone does not authenticate a fresh source occurrence. -/
theorem received_voteForward_processAt (hv : rho.ExecutionValid)
    {source i : Nat} {x : Fin (Fintype.card V)} {v : V} {τ u : Time}
    {receipt : Wire (Fintype.card V)} {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∈ rho.honest) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m])) :
    ∃ k, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (simTrace S rho hn).projAC.ProcessAt (rho.ownKey v) k m ∧
      (simTrace S rho hn).time k = u ∧ τ ≤ u := by
  obtain ⟨j, s, hji, hsend, hrel⟩ := hv.unforgeable i v receipt u he _ hc
    (rho.key x) hx rfl
  have hsj : source ≤ j := by
    by_contra h
    exact hfirst j (Nat.lt_of_not_ge h) hrel
  have hsi : source < i := hsj.trans_lt hji
  have htime : τ ≤ u := by
    rcases hs with hs | ⟨o, hs⟩ <;>
      rcases keyLe_of_lt S rho hv hs he hsi with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
    · exact h.le
    · exact h.le
  obtain ⟨k, hlo, hhi, hp, ht⟩ := received_vote_processAt S rho hn he
    (hc.trans (Model.Obj.Contains.step (List.mem_singleton_self _) (.refl _)))
  exact ⟨k, hlo, hhi, hp, ht, htime⟩

/-- Holdings of a first-release vote envelope either belong to its source or give
an actual recipient processing cut between source time and the holding time.
The source alternative is not itself a fresh-processing claim. -/
theorem held_voteForward_source_or_process (hv : rho.ExecutionValid)
    {source : Nat} {x y : Fin (Fintype.card V)} {τ d : Time}
    {m : SA.Vote (Fintype.card V)}
    (hx : rho.key x ∈ rho.honest) (hs : rho.SendsAt (rho.key x) source τ)
    (hfirst : ∀ j < source,
      Model.Obj.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m] ∉
        rho.releasesAt j)
    (hh : rho.log.Held rho.point (rho.key y)
      (.mk (.signed x .poll) (.data (.voteForward τ (encodeVote m))) [voteObj m]) d) :
    y = x ∨ ∃ k, (simTrace S rho hn).projAC.ProcessAt y k m ∧
      τ ≤ (simTrace S rho hn).time k ∧ (simTrace S rho hn).time k ≤ d := by
  obtain ⟨u, hud, hsend | hrecv, _⟩ := hh
  · obtain ⟨i, hi, hrel⟩ := hsend
    have hxy : x = rho.ownKey (rho.key y) := by
      rcases hi with he | ⟨o, he⟩
      · simp only [Model.Run.releasesAt, he] at hrel
        rcases rho.tick_auth _ _ _ hrel with h | ⟨r, h, _⟩
        · cases h
        · exact (Model.Auth.signed.inj h).1
      · simp only [Model.Run.releasesAt, he] at hrel
        rcases rho.deliver_auth _ _ _ _ hrel with h | ⟨r, h, _⟩
        · cases h
        · exact (Model.Auth.signed.inj h).1
    exact Or.inl (hxy.trans (rho.key.symm_apply_apply y)).symm
  · obtain ⟨i, hi⟩ := hrecv
    obtain ⟨k, _, _, hp, ht, hτ⟩ := received_voteForward_processAt S rho hn hv hx hs
      hfirst hi (.refl _)
    have hkey : rho.ownKey (rho.key y) = y := rho.key.symm_apply_apply y
    rw [hkey] at hp
    exact Or.inr ⟨k, hp, ht ▸ hτ, ht ▸ hud⟩

/-- Option C's publication supplier: actual same-event release and first release,
not merely candidate construction or pool membership. -/
theorem simTrace_vote_forwarded (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k (m : SA.Vote (Fintype.card V)),
    let tr := simTrace S rho hn
    (tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (goldilocks S)) E).Object :=
      .mk (.signed y .poll) (.data (.voteForward (tr.time k) (encodeVote m))) [voteObj m]
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i (tr.time k) ∧ envelope ∈ rho.releasesAt i ∧
      ∀ j < i, envelope ∉ rho.releasesAt j := by
  intro y hy k m
  dsimp only
  intro hsource
  have hevent : ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTrace S rho hn).time k) := by
    rcases hsource with ⟨ℓ, hc, e, he, -⟩ | ⟨hc, -, -⟩
    · exact simTrace_call_sending_event S rho hn hc
        (simTrace_emission_not_restart S rho hn hv hy hc he)
    · rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, -⟩
      · exact simTrace_call_sending_event S rho hn hc (by rw [hm]; simp)
      · exact simTrace_call_sending_event S rho hn hc (by rw [hb]; simp)
  obtain ⟨i, hlo, hhi, hs⟩ := hevent
  have hfresh : m ∉ ((simTrace S rho hn).state y k).ac.pool m.slot := by
    rcases hsource with hem | ⟨-, hf, -⟩
    · have hr := simTrace_goldilocksRun S rho hn hv
      obtain ⟨ℓ, hc, e, he, hev⟩ := hem
      have hΦ : FrameOK ℓ.frame :=
        (hr.cutLaw y hy k _ hc).1 ▸
          (Store.frame_realization _ _ _ _ (Compose.fg_reachable hr.toLocalRun hy k)).1
      have hsign := SA.step_emission_signer y _ ℓ.frame _ ℓ.call
        hΦ
        (hr.time_nonneg k) (by
          rw [(hr.cutLaw y hy k _ hc).2.1]
          exact he)
      have hm : m.val = y := hev ▸ hsign
      have hf := Compose.emitted_slot_not_pooled hr hy hy (Nat.le_refl k)
        ⟨ℓ, hc, e, he, hev⟩ hm rfl m.slot
      simpa only [Compose.projAC_state hr.toLocalRun hy] using hf
    · exact hf
  have hcall : (simTrace S rho hn).IsCall y k := by
    rcases hsource with ⟨ℓ, hc, -⟩ | ⟨hc, -⟩
    · exact ⟨_, hc⟩
    · rcases hc with ⟨ℓ, hc, -⟩ | ⟨ℓ, B, hc, -⟩ <;> exact ⟨_, hc⟩
  have hpost : m ∈ ((simTrace S rho hn).post k).ac.pool m.slot := by
    rcases hsource with hem | ⟨-, -, hpost⟩
    · exact Compose.emitted_vote_mem_post (simTrace_goldilocksRun S rho hn hv) hy hem
    · exact hpost
  obtain ⟨hold, hnew⟩ := sending_event_pool_insertion S rho hn hv hy hs hlo hhi
    hcall hfresh hpost
  refine ⟨i, hlo, hhi, hs, ?_, admission_voteForward_first S rho hn hv hy hs hlo hhi hfresh⟩
  rcases hs with he | ⟨o, he⟩
  · have hr := tick_pool_insertion_released S rho hn hv
      ((mem_honestKeys_iff S rho y).mp hy) he m hold hnew
    simp only [Model.Run.ownKey, Equiv.symm_apply_apply] at hr
    exact hr
  · have hr := delivery_pool_insertion_released S rho hn hv he m hold hnew
    simp only [Model.Run.ownKey, Equiv.symm_apply_apply] at hr
    exact hr

/-- The simulating trace and cut map of a valid engine run simulate it. -/
theorem simTrace_simulates (hv : rho.ExecutionValid) :
    Simulates S rho hn (simTrace S rho hn) (cutMap S rho hn) where
  run := simTrace_goldilocksRun S rho hn hv
  ι_zero := cutMap_zero S rho hn
  ι_mono := cutMap_mono S rho hn
  covered := simTrace_covered S rho hn
  state := simTrace_state S rho hn hv
  now := now_eq_lastClock S rho hn hv
  tick_public := simTrace_tick_public_group S rho hn hv
  tick_other := simTrace_tick_other S rho hn hv
  deliver := simTrace_deliver S rho hn hv
  restart := simTrace_restart S rho hn hv
  awake_of := simTrace_awake_of S rho hn hv
  awake_to := simTrace_awake_to S rho hn hv
  block_released := simTrace_block_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
  vote_released := simTrace_vote_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
  att_released := simTrace_att_released S rho hn hv (simTrace_goldilocksRun S rho hn hv)
  block_relayed := simTrace_block_relayed S rho hn hv
  vote_forwarded := simTrace_vote_forwarded S rho hn hv
  att_relayed := simTrace_att_relayed S rho hn hv

variable (V) in
/-- **The engine simulates the node** (`EngineSimulatesNode`): every valid engine run of the
family is simulated by `simTrace` with `cutMap`. -/
theorem engineSimulatesNode : EngineSimulatesNode V S :=
  (engineSimulatesNode_iff V S).mpr
    fun _ rho hn hv => ⟨simTrace S rho hn, cutMap S rho hn, simTrace_simulates S rho hn hv⟩

end Consensus.Goldilocks.Simulation

end
