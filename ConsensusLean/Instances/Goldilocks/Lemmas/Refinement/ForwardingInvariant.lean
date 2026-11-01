module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outbox

public section

/-! # Reachable forwarding inventory

Runtime queue shape and prefix holdings used to connect block acceptance to publication.
-/

namespace Consensus.Goldilocks.Refinement

open Shape Blocks
open Consensus.Model

/-- Pending block payloads have the canonical parent/child shape. This says nothing about
whether their guards succeed or whether the parent has already been published. -/
def ForwardQueueCanonical {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) : Prop :=
  ∀ q ∈ st.forwards, ∃ p : Option (Wire sp.n), ∃ B, q.2 = p.toList ++ [blockObj sp B]

/-- Expose only the queue-shape proposition, not the definition body. -/
theorem forwardQueueCanonical_iff {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) :
    ForwardQueueCanonical st ↔
      ∀ q ∈ st.forwards, ∃ p : Option (Wire sp.n), ∃ B,
        q.2 = p.toList ++ [blockObj sp B] := by rfl

/-- Every new acceptance queues one canonical child with its exact optional parent. -/
theorem forwardQueueCanonical_queueAccepted {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp)
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (queueAccepted st B) := by
  rw [forwardQueueCanonical_iff] at h ⊢
  intro q hq
  rcases queueAccepted_forward_origin st B q hq with hq | ⟨root, p, _, _, he⟩
  · exact h q hq
  · exact ⟨p, B, congrArg Prod.snd he⟩

/-- The handler's acceptance fold preserves canonical payload shape. -/
theorem forwardQueueCanonical_apply {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) r
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (apply st r) := by
  rw [forwardQueueCanonical_iff] at h ⊢
  intro q hq
  rcases apply_forward_origin st r q hq with hq | ⟨B, p, _, he⟩
  · exact h q hq
  · exact ⟨p, B, congrArg Prod.snd he⟩

/-- Canonical queue payloads become canonical signed forwarding objects. -/
theorem forwardQueueCanonical_pending {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (h : ForwardQueueCanonical st) :
    ∀ o ∈ pendingWrappers st, ∃ t p B, o = forwardObj sp st.self t p B := by
  rw [forwardQueueCanonical_iff] at h
  intro o ho
  rw [pendingWrappers_eq] at ho
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ho
  obtain ⟨p, B, he⟩ := h q hq
  exact ⟨q.1, p, B, by simp only [he, forwardObj]⟩

private theorem canonical_recordOwn {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact forwardQueueCanonical_apply st _ h
    · exact h
  · exact h

private theorem canonical_processOne {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) o hs
    (h : ForwardQueueCanonical st) : ForwardQueueCanonical (processOne hs st o) := by
  unfold processOne
  split
  · unfold relayIf
    dsimp only
    split <;> exact forwardQueueCanonical_apply st _ h
  · exact forwardQueueCanonical_apply st _ h
  · unfold relayIf
    simp only [↓reduceIte]
    exact forwardQueueCanonical_apply st _ h
  · exact h

private theorem canonical_poll {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) t :
    ForwardQueueCanonical (poll st t).1 := by
  rw [forwardQueueCanonical_iff, (poll_wrappers st t).2]
  exact fun q h => False.elim (List.not_mem_nil h)

/-- The actual event-boundary queue always has canonical block payload shape. This
structural invariant needs no execution-validity or publication-success premise. -/
theorem stateAt_forwardQueueCanonical {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) : ∀ i, ForwardQueueCanonical (stateAt S rho hn v i)
  | 0 => by
    rw [forwardQueueCanonical_iff]
    exact fun q h => False.elim (List.not_mem_nil h)
  | i + 1 => by
    have ih := stateAt_forwardQueueCanonical S rho hn v i
    cases he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact ih
    | some ev =>
      by_cases hnode : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_tick S rho hn v he]
          apply tick_pres S rho hn ForwardQueueCanonical canonical_recordOwn
            (fun st s h => by unfold propose; dsimp only; split <;> exact h)
            (fun st h => by
              unfold nodeTick
              split
              · exact forwardQueueCanonical_apply st _ h
              · exact h)
            (fun st t _ => canonical_poll st t)
          exact ih
        | deliver w o t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_deliver S rho hn v he]
          apply deliver_pres S rho hn ForwardQueueCanonical (fun st t _ => canonical_poll st t)
            (fun st m cs hs h => canonical_recordOwn st _ hs h)
          have hf : ∀ xs : List (Wire (Fintype.card V)),
              ∀ st : State (S.params (pubOf E) hn) (S.ro _), ForwardQueueCanonical st →
                ForwardQueueCanonical (xs.foldl (processOne (digests rho.hash o)) st) := by
            intro xs
            induction xs with
            | nil => exact fun _ h => h
            | cons x xs hx => exact fun st h => hx _ (canonical_processOne st x _ h)
          exact hf _ _ ih
        | restart w t =>
          simp only [Model.Event.node] at hnode
          subst w
          rw [stateAt_restart S rho hn v he]
          exact ih
      · rw [state_of_other S rho hn v i ev he hnode]; exact ih

/-- The selected poll discharges pending accounting into holdings and leaves an empty,
therefore ready, block queue. The later vote suffix needs no success premise. -/
theorem dutyStep_poll_inventory {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel .poll) (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ForwardQueueCanonical (shapeOf S hn nd)) :
    let result := (rho.dutyStep v nd (.poll t)).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  have hshape := forwardQueueCanonical_pending (shapeOf S hn nd) hc
  rw [hself] at hshape
  constructor
  · rw [wrappersAccounted_iff]
    intro root o hw
    exact Or.inl (dutyStep_poll_wrappers_held S rho hn v nd t hsel hself ha hr hshape root o hw)
  · rw [dutyStep_poll S rho hn v nd t hsel, pendingWrappers_eq,
      (poll_wrappers _ _).2, List.map_nil]
    apply (pendingReady_iff _ []).mpr
    intro i o hi
    simp only [List.getElem?_nil] at hi
    cases hi

/-- The queue-shape component survives every actual duty, including failed releases. -/
theorem dutyStep_forwardQueueCanonical {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E))
    (d : (protoOf (compiled (family S)) E).Duty)
    (hc : ForwardQueueCanonical (shapeOf S hn nd)) :
    ForwardQueueCanonical (shapeOf S hn (rho.dutyStep v nd d).1) := by
  apply dutyStep_pres S rho hn ForwardQueueCanonical canonical_recordOwn
    (fun st s h => by unfold propose; dsimp only; split <;> exact h)
    (fun st h => by
      unfold nodeTick
      split
      · exact forwardQueueCanonical_apply st _ h
      · exact h)
    (fun st t _ => canonical_poll st t) v nd d hc

/-- All actual duties preserve the holdings/pending invariant. Empty committee duties
are impossible; the poll-proposal step cannot enqueue block wrappers. -/
theorem dutyStep_forwardInventory {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E))
    (d : (protoOf (compiled (family S)) E).Duty)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ForwardQueueCanonical (shapeOf S hn nd)) :
    let result := (rho.dutyStep v nd d).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  cases d with
  | propose s hs => exact dutyStep_propose_pendingReady S rho hn v nd s hs ha hr
  | act s k => exact k.elim
  | poll t =>
    by_cases hsel : rho.ownKey v ∈ rho.sel .poll
    · exact dutyStep_poll_inventory S rho hn v nd t hsel hself ha hr hc
    · simpa only [Model.Run.dutyStep,
        show (protoOf (compiled (family S)) E).role (.poll t) = .poll from rfl,
        hsel, ↓reduceIte] using And.intro ha hr
  | pollPropose t =>
    have hempty : ((protoOf (compiled (family S)) E).act nd.st (.pollPropose t)).2 = [] := by
      change (Option.map _ ((family S (pubOf E)).pollPropose nd.st.1 t).2).toList = []
      simp only [family, dite_eq_left hn]
      rfl
    unfold Model.Run.dutyStep
    split
    · simp only [hempty, Model.Run.signedCandidate, List.map_nil, ite_self, Model.releaseAll]
      change WrappersAccounted _ (((protoOf (compiled (family S)) E).act nd.st
        (.pollPropose t)).1.1 hn) ∧ PendingReady _ (pendingWrappers
          (((protoOf (compiled (family S)) E).act nd.st (.pollPropose t)).1.1 hn))
      rw [shapeOf_act_pollPropose S hn]
      unfold nodeTick
      split
      · simpa only [wrappersAccounted_iff, pendingWrappers_eq, Node.acCall, apply,
          List.foldl_cons, List.foldl_nil] using And.intro ha hr
      · exact ⟨ha, hr⟩
    · exact ⟨ha, hr⟩

/-- Fold actual duties while threading their intermediate holdings and queue state. -/
theorem runDuties_forwardInventory {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E))
    (ds : List (protoOf (compiled (family S)) E).Duty)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ForwardQueueCanonical (shapeOf S hn nd)) :
    let result := (rho.runDuties v nd ds).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  induction ds generalizing nd with
  | nil => exact ⟨ha, hr⟩
  | cons d ds ih =>
    rw [runDuties_fst_cons S rho]
    have hi := dutyStep_forwardInventory S rho hn v nd d hself ha hr hc
    apply ih _ ?_ hi.1 hi.2 (dutyStep_forwardQueueCanonical S rho hn v nd d hc)
    apply dutyStep_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h)
      (fun st h => (nodeTick_self st).trans h)
      (fun st t h => (poll_self st t).trans h) v nd d hself

/-- Unsigned gossip cannot record a proposer item, so it preserves both components. -/
theorem gossip_forwardInventory {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (origin : Fin (Fintype.card V)) (nd : Model.Node (protoOf (compiled (family S)) E))
    (t : Time)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd))) :
    let result := (Model.releaseAll (protoOf (compiled (family S)) E) rho.hash origin nd
      (Model.gossipCandidates (protoOf (compiled (family S)) E) nd.st t)).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  apply releaseAll_pendingReady S hn rho.hash origin nd _ ha hr
  intro o ho k s hd cs he
  obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
  cases he

/-- Tick execution threads the same invariant through its clock, actual duties and gossip. -/
theorem tick_forwardInventory {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (t : Time)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ForwardQueueCanonical (shapeOf S hn nd)) :
    let result := (rho.tick nd v t).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  unfold Model.Run.tick
  let start : Model.Node (protoOf (compiled (family S)) E) :=
    ⟨(protoOf (compiled (family S)) E).clock nd.st t (mempool rho.inbox v t), nd.seen⟩
  have ha' : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ start.seen.flatMap Obj.parts) (shapeOf S hn start) := by
    simpa only [wrappersAccounted_iff, pendingWrappers_eq, start, shapeOf,
      shapeOf_clock S hn] using ha
  have hr' : PendingReady start.seen (pendingWrappers (shapeOf S hn start)) := by
    simpa only [pendingWrappers_eq, start, shapeOf, shapeOf_clock S hn] using hr
  split
  · apply gossip_forwardInventory S rho hn
    · exact (runDuties_forwardInventory S rho hn v start _ hself ha' hr' hc).1
    · exact (runDuties_forwardInventory S rho hn v start _ hself ha' hr' hc).2
  · exact ⟨ha', hr'⟩

/-- Receipt processing starts with the received object's full recursive closure already
held, then the actual delivery duties and gossip preserve inventory. -/
theorem deliver_forwardInventory {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E))
    (o : (protoOf (compiled (family S)) E).Object) (t : Time)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (ha : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd))
    (hr : PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)))
    (hc : ForwardQueueCanonical (shapeOf S hn nd)) :
    let result := (rho.deliver nd v o t).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ result.seen.flatMap Obj.parts) (shapeOf S hn result) ∧
      PendingReady result.seen (pendingWrappers (shapeOf S hn result)) := by
  let seen : List (Wire (Fintype.card V)) := nd.seen ++ [o]
  have hmono : ∀ c ∈ nd.seen.flatMap Obj.parts, c ∈ seen.flatMap Obj.parts := by
    intro c hc
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨a, List.mem_append_left _ ha, hc⟩
  have ha' : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ seen.flatMap Obj.parts) (shapeOf S hn nd) := by
    rw [wrappersAccounted_iff] at ha ⊢
    exact fun root c hw => (ha root c hw).imp (hmono c) id
  have hp := pendingReady_process (sp := S.params (pubOf E) hn) seen (shapeOf S hn nd)
    (digests (P := protoOf (compiled (family S)) E) rho.hash o) o ha'
    (pendingReady_mono hmono hr) (fun c hc =>
      List.mem_flatMap.mpr ⟨o, List.mem_append_right _ (List.mem_singleton_self o), hc⟩)
  have hcanon : ForwardQueueCanonical
      (process (shapeOf S hn nd) o (digests rho.hash o)) := by
    have hf : ∀ xs : List (Wire (Fintype.card V)),
        ∀ st : State (S.params (pubOf E) hn) (S.ro _), ForwardQueueCanonical st →
          ForwardQueueCanonical (xs.foldl (processOne (digests rho.hash o)) st) := by
      intro xs
      induction xs with
      | nil => exact fun _ h => h
      | cons c cs ih => exact fun st h => ih _ (canonical_processOne st c _ h)
    exact hf _ _ hc
  unfold Model.Run.deliver
  apply gossip_forwardInventory S rho hn
  all_goals
    have hi := runDuties_forwardInventory S rho hn v
      ⟨(protoOf (compiled (family S)) E).process nd.st o (digests rho.hash o), seen⟩
      ((protoOf (compiled (family S)) E).deliverDuties t)
      ((process_self _ _ _).trans hself) hp.1 hp.2 hcanon
    first | exact hi.1 | exact hi.2

/-- Reachable engine states account for each durable wrapper by an actual holding or
an exact pending candidate, and every pending child is ready at its ordered prefix. -/
theorem stateBefore_forwardInventory {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) : ∀ i,
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ (rho.stateBefore i v).seen.flatMap Obj.parts) (stateAt S rho hn v i) ∧
      PendingReady (rho.stateBefore i v).seen (pendingWrappers (stateAt S rho hn v i))
  | 0 => by
    constructor
    · rw [wrappersAccounted_iff]
      intro root o ho
      cases ho
    · change PendingReady ([] : List (Wire (Fintype.card V)))
        (pendingWrappers (stateAt S rho hn v 0))
      rw [pendingWrappers_eq]
      change PendingReady ([] : List (Wire (Fintype.card V))) []
      rw [pendingReady_iff]
      intro i o hi
      cases hi
  | i + 1 => by
    have ih := stateBefore_forwardInventory S rho hn v i
    cases he : rho.events[i]? with
    | none =>
      have heq : rho.stateBefore (i + 1) = rho.stateBefore i := by
        have ht : rho.events.take (i + 1) = rho.events.take i := by
          have hl := List.getElem?_eq_none_iff.mp he
          rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
        simp only [Model.Run.stateBefore, ht]
      rw [stateAt_succ_none S rho hn v he, heq]
      exact ih
    | some ev =>
      rw [show stateAt S rho hn v (i + 1) =
        shapeOf S hn (rho.stateBefore (i + 1) v) from rfl, rho.stateBefore_succ he]
      by_cases hn' : ev.node = v
      · cases ev with
        | tick w t =>
          simp only [Model.Event.node] at hn'
          subst w
          simp only [Model.Run.step, Function.update_self]
          exact tick_forwardInventory S rho hn v _ t (self_eq_ownKey S rho hn v i)
            ih.1 ih.2 (stateAt_forwardQueueCanonical S rho hn v i)
        | deliver w o t =>
          simp only [Model.Event.node] at hn'
          subst w
          simp only [Model.Run.step, Function.update_self]
          exact deliver_forwardInventory S rho hn v _ o t (self_eq_ownKey S rho hn v i)
            ih.1 ih.2 (stateAt_forwardQueueCanonical S rho hn v i)
        | restart w t =>
          simp only [Model.Event.node] at hn'
          subst w
          have hs : shapeOf S hn
              (rho.step (rho.stateBefore i) (.restart v t) v) =
              restore (rho.ownKey v) (stateAt S rho hn v i) t := by
            rw [← rho.stateBefore_succ he]
            exact stateAt_restart S rho hn v he
          rw [hs]
          simpa only [Model.Run.step, Function.update_self, wrappersAccounted_iff,
            pendingWrappers_eq, restore, apply, Node.restart, Node.acCall,
            List.foldl_cons, List.foldl_nil, self_eq_ownKey S rho hn v i] using ih
      · cases ev <;> simp only [Model.Event.node] at hn' <;>
          simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hn'), stateAt] using ih

/-- At valid event boundaries the queue has drained, so durable wrappers are actual
holdings. This does not identify their first publication or order acceptance cuts. -/
theorem stateBefore_wrappers_held {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (i root : Nat) (o : Wire (Fintype.card V))
    (hw : (stateAt S rho hn v i).wrappers root = some o) :
    o ∈ (rho.stateBefore i v).seen.flatMap Obj.parts := by
  have ha := (stateBefore_forwardInventory S rho hn v i).1
  rw [wrappersAccounted_iff] at ha
  rcases ha root o hw with h | h
  · exact h
  · rw [pendingWrappers_eq, forwards_empty S rho hn hv v i, List.map_nil] at h
    exact False.elim (List.not_mem_nil h)

end Consensus.Goldilocks.Refinement
