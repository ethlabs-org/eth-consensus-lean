module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # Goldilocks Refinement: the engine simulates the node

`EngineSimulatesNode` (`Statements/Refinement`) assembled from its steps: the trace `simTrace`
with the cut map `cutMap` (`Trace`), a Goldilocks run by `simTrace_goldilocksRun` and agreeing
with the engine by the `Simulates` steps (`Run`). Signed fresh-admission publication remains
an explicit open supplier below; simulation inherits that obligation. -/

namespace Consensus.Goldilocks.Refinement

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Vote envelopes drain after the actual ordinary/block release prefix when their canonical
votes are held there. No success assumption is imposed on the prefix candidates themselves. -/
theorem releaseAll_voteForward_suffix (hash : Blocks.Header Info → Nat)
    (x : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (pre : List (Model.protoOf (compiled (family S)) E).Object)
    (vs : List (Time × SA.Vote (Fintype.card V)))
    (hheld : ∀ tv ∈ vs, voteObj tv.2 ∈ Model.closure
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) hash x nd pre).1.seen) :
    let cs : List (Model.protoOf (compiled (family S)) E).Object := vs.map fun tv =>
      .mk (.signed x .poll) (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2]
    (Model.releaseAll (Model.protoOf (compiled (family S)) E) hash x nd (pre ++ cs)).2 =
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) hash x nd pre).2 ++ cs := by
  dsimp only
  erw [Model.releaseAll_append (P := Model.protoOf (compiled (family S)) E)]
  dsimp only
  congr 1
  apply (releaseAll_of_prefix_guards (Model.protoOf (compiled (family S)) E)
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hheld : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      voteObj tv.2 ∈ Model.closure
        (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v)
          ⟨((Model.protoOf (compiled (family S)) E).act nd.st (.poll t)).1, nd.seen⟩
          (((poll (shapeOf S hn nd) t).2.toList.map fun q =>
            Model.Obj.mk (.signed (rho.ownKey v) .poll) (.data q.1) q.2) ++
            pendingWrappers (shapeOf S hn nd))).1.seen) :
    ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      Model.Obj.mk (.signed (rho.ownKey v) .poll)
        (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈
          (rho.dutyStep v nd (.poll t)).2 := by
  intro tv htv
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (family S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  rw [signedCandidate_poll_eq S rho hn v nd t hsel hself]
  erw [releaseAll_voteForward_suffix S rho.hash (rho.ownKey v)
    ⟨((Model.protoOf (compiled (family S)) E).act nd.st (.poll t)).1, nd.seen⟩ _ _ hheld]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨tv, htv, rfl⟩)

omit [DecidableEq V] in
/-- A selected poll publishes every queued envelope whose canonical vote is already held.
The intervening ordinary/block candidates preserve these holdings even if their guards fail. -/
theorem dutyStep_poll_voteForward (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Nat)
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
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Nat)
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

/-- Every envelope actually queued during delivery is released in that same engine event.
Canonical dependencies are derived from reachable inventory and the actual ordinary prefix. -/
theorem delivery_voteForward_released (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (tv : Time × SA.Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward tv.1 (encodeVote tv.2))) [voteObj tv.2] ∈ rho.releasesAt i := by
  have hv' := hv.honest_only _ (List.mem_of_getElem? he)
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  let nd : Model.Node (Model.protoOf (compiled (family S)) E) :=
    ⟨(Model.protoOf (compiled (family S)) E).process (rho.stateBefore i v).st o
      (Model.digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
  have hshape : shapeOf S hn nd =
      process (stateAt S rho hn v i) o (Model.digests rho.hash o) := rfl
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

/-- A fresh wire admission anywhere in the actual delivery traversal publishes its exact
admission-time envelope in the same event. Prefix-state identification is explicit here. -/
theorem delivery_message_admission_released (hv : rho.ExecutionValid) {v : V}
    {i : Nat} {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (pre post : List (Wire (Fintype.card V))) (m : SA.Vote (Fintype.card V))
    (hparts : delivered (S.params (pubOf E) hn) o = pre ++ voteObj m :: post)
    (hold : m ∉ (pre.foldl (processOne (Model.digests rho.hash o))
      (stateAt S rho hn v i)).node.ac.pool m.slot)
    (hnew : m ∈ (Node.onMessage
      (pre.foldl (processOne (Model.digests rho.hash o)) (stateAt S rho hn v i)).self
      (pre.foldl (processOne (Model.digests rho.hash o)) (stateAt S rho hn v i)).node
      t m).1.ac.pool m.slot) :
    Model.Obj.mk (.signed (rho.ownKey v) .poll)
      (.data (.voteForward t (encodeVote m))) [voteObj m] ∈ rho.releasesAt i := by
  have hnow : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
  apply delivery_voteForward_released S rho hn hv he (t, m)
  have hq := process_message_voteForward (stateAt S rho hn v i) o
    (Model.digests rho.hash o) pre post m hparts hold (by simpa only [hnow] using hnew)
  simpa only [hnow] using hq

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

/-- An upcoming honest emission is absent from every honest engine pool at an earlier
event boundary, including boundaries after restart replay. No collision premise is needed. -/
theorem stateAt_emission_slot_fresh (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {v : V} (hv' : v ∈ rho.honest) {k i : Nat} (hi : i ≤ rho.events.length)
    (hik : cutMap S rho hn i ≤ k) {m w : SA.Vote (Fintype.card V)}
    (hem : (simTrace S rho hn).EmitAt y k m) (hw : w.val = y) (hs : w.slot = m.slot)
    (σ : Nat) : w ∉ (stateAt S rho hn v i).node.ac.pool σ := by
  have hrun := simTrace_goldilocksRun S rho hn hv
  have hx : rho.ownKey v ∈ honestKeys S rho := by
    simpa [honestKeys, Model.Run.ownKey] using hv'
  have hf := Compose.emitted_slot_not_pooled hrun hy hx hik hem hw hs σ
  rw [Compose.projAC_state hrun.toLocalRun hx] at hf
  rw [simTrace_state S rho hn hv v hv' i hi]
  exact hf

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

/-- Option C's outstanding publication supplier: actual same-event release and first release,
not merely candidate construction or pool membership. -/
theorem simTrace_vote_forwarded (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k (m : SA.Vote (Fintype.card V)),
    let tr := simTrace S rho hn
    (tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (family S)) E).Object :=
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
  refine ⟨i, hlo, hhi, hs, ?_⟩
  -- Remaining: fresh handler queueing, actual prefix holdings, and global first release.
  sorry

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
  fun _ rho hn hv => ⟨simTrace S rho hn, cutMap S rho hn, simTrace_simulates S rho hn hv⟩

end Consensus.Goldilocks.Refinement

end
