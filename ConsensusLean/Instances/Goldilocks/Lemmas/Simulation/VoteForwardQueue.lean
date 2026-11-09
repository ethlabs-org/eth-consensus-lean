module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: vote-forward envelopes up to their release

The engine's vote-forward queue: a fresh vote-pool insertion of a handler queues an envelope at
the current clock (`onBlock_pool_insertion_queued`, `nodeTick_pool_insertion_queued`), a released
envelope carries its release time and a pooled vote (`released_voteForward_stamp`,
`released_voteForward_pool`), and the poll steps and the tick's leading and trailing polls release
the queued envelopes (`dutyStep_poll_voteForward`, `tick_prefix_voteForward_poll`,
`tick_trailing_voteForward_poll`, `proposal_pool_insertion_queued`). `Core` derives the releases at
a tick or a delivery from them. -/

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
    (hv' : v ∉ rho.faultyAt 0) {i p : Nat}
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
theorem tick_prefix_voteForward_poll (hconst : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hv' : v ∉ rho.faultyAt 0) {i p : Nat} {t : Time}
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
  apply tick_prefix_pool_available S rho hn hconst hv hv' he hw hp q.2.slot q.2
  apply runDuties_voteForward_in_pool S rho hn v _ _ ?_ q hq
  intro r hr
  change r ∈ ((rho.stateBefore i v).st.1 hn).voteForwards at hr
  rw [← stateAt_eq S rho hn v i] at hr
  rw [voteForwards_empty S rho hn hv v i] at hr
  cases hr

/-- The tick's first trailing poll has the required one-body bound and releases
all vote envelopes queued by the node tick and the optional own proposal. -/
theorem tick_trailing_voteForward_poll (hconst : rho.point.ConstantFaults)
    (hv : rho.ExecutionValid) {v : V} (hv' : v ∉ rho.faultyAt 0) {i : Nat} {t : Time}
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
  have h := tick_prefix_voteForward_poll S rho hn hconst hv hv' he hw hlen
  rw [htake] at h
  apply h
  dsimp only [nd, pre]
  erw [runDuties_fst_append]
  apply outbox_after_pre S rho hn v (stateAt S rho hn v i) t ht
    (fgDue_eq_false S rho hn v i)
  · rw [outbox_empty S rho hn hv v i]; simp
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

end Consensus.Goldilocks.Simulation

end
