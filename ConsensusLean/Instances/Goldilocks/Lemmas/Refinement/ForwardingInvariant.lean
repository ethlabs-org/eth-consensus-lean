module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Outbox
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Release
import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps

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

/-- The delivery poll's immutable input is ready directly from the reachable inventory.
The received object's recursive children are held before any of its calls run. -/
theorem delivery_pendingReady {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (i : Nat) (o : (protoOf (compiled (family S)) E).Object) :
    PendingReady ((rho.stateBefore i v).seen ++ [o])
      (pendingWrappers (process (stateAt S rho hn v i) o (digests rho.hash o))) := by
  obtain ⟨ha, hr⟩ := stateBefore_forwardInventory S rho hn v i
  let seen : List (Wire (Fintype.card V)) := (rho.stateBefore i v).seen ++ [o]
  have hm : ∀ c ∈ (rho.stateBefore i v).seen.flatMap Obj.parts,
      c ∈ seen.flatMap Obj.parts := by
    intro c hc
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    exact List.mem_flatMap.mpr ⟨a, List.mem_append_left _ ha, hc⟩
  have ha' : WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ seen.flatMap Obj.parts) (stateAt S rho hn v i) := by
    rw [wrappersAccounted_iff] at ha ⊢
    exact fun root c hw => (ha root c hw).imp (hm c) id
  exact (pendingReady_process (sp := S.params (pubOf E) hn) seen
    (stateAt S rho hn v i) (digests rho.hash o) o ha' (pendingReady_mono hm hr)
    (fun c hc => List.mem_flatMap.mpr
      ⟨o, List.mem_append_right _ (List.mem_singleton_self o), hc⟩)).2

/-- Every block wrapper pending after an actual receipt passes the delivery poll.
This is release completeness for the queue, not yet completeness for acceptance cuts. -/
theorem delivery_pending_released {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {o : (protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (c : Wire (Fintype.card V))
    (hc : c ∈ pendingWrappers
      (process (stateAt S rho hn v i) o (digests rho.hash o))) :
    c ∈ rho.releasesAt i := by
  let nd : Model.Node (protoOf (compiled (family S)) E) :=
    ⟨(protoOf (compiled (family S)) E).process (rho.stateBefore i v).st o
      (digests rho.hash o), (rho.stateBefore i v).seen ++ [o]⟩
  have hself : (shapeOf S hn nd).self = rho.ownKey v :=
    (process_self _ _ _).trans (self_eq_ownKey S rho hn v i)
  have hcanon : ForwardQueueCanonical (shapeOf S hn nd) := by
    have hf : ∀ xs : List (Wire (Fintype.card V)),
        ∀ st : State (S.params (pubOf E) hn) (S.ro _), ForwardQueueCanonical st →
          ForwardQueueCanonical (xs.foldl (processOne (digests rho.hash o)) st) := by
      intro xs
      induction xs with
      | nil => exact fun _ h => h
      | cons a as ih => exact fun st h => ih _ (canonical_processOne st a _ h)
    exact hf _ _ (stateAt_forwardQueueCanonical S rho hn v i)
  have hs := forwardQueueCanonical_pending (shapeOf S hn nd) hcanon
  rw [hself] at hs
  have hp := dutyStep_poll_pending S rho hn v nd t.toNat (poll_selected S rho hv v)
    hself (delivery_pendingReady S rho hn v i o) hs c hc
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  simp only [Model.Run.releasesAt, he, Model.Run.deliver]
  rw [deliverDuties_eq S t ht]
  apply List.mem_append_left
  exact hp

/-- A real batch release has a successful candidate occurrence at its actual prefix.
The index counts rejected candidates too, so it is suitable for publication order. -/
theorem releaseAll_successful_index {pub : Public} {O : Type} (P : Protocol pub O)
    (hash : P.Item → Nat) (x : Key pub) (nd : Model.Node P) (cs : List P.Object)
    (o : P.Object) (ho : o ∈ (Model.releaseAll P hash x nd cs).2) :
    ∃ i, cs[i]? = some o ∧
      let pre := (Model.releaseAll P hash x nd (cs.take i)).1
      Model.releasable pre.seen o = true ∧ Model.protects P x pre.seen o = true ∧
        P.dependencies.ready (Model.closure pre.seen) o = true := by
  induction cs generalizing nd with
  | nil => simp [Model.releaseAll] at ho
  | cons c cs ih =>
    simp only [Model.releaseAll] at ho
    split at ho
    next hg =>
      rcases List.mem_cons.mp ho with he | ho
      · subst o
        refine ⟨0, rfl, ?_⟩
        simpa only [List.take_zero, Model.releaseAll, Bool.and_eq_true,
          and_assoc] using hg
      · obtain ⟨i, hi, hs⟩ := ih _ ho
        refine ⟨i + 1, hi, ?_⟩
        simpa only [List.take_succ_cons, Model.releaseAll, hg, ↓reduceIte] using hs
    next hg =>
      obtain ⟨i, hi, hs⟩ := ih _ ho
      refine ⟨i + 1, hi, ?_⟩
      simpa only [List.take_succ_cons, Model.releaseAll, hg, Bool.false_eq_true,
        ↓reduceIte] using hs

/-- A release from an indexed actual batch gives a concrete publication occurrence,
including its successful candidate prefix. No abstract publication premise is needed. -/
theorem publication_of_batch_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (v : V) (i j : Nat)
    (t : Time) (he : rho.SendsAt v i t)
    (b : ReleaseBatch (protoOf (compiled (family S)) E))
    (hb : (eventBatches rho i)[j]? = some b)
    (o : (protoOf (compiled (family S)) E).Object)
    (ho : o ∈ (Model.releaseAll (protoOf (compiled (family S)) E)
      rho.hash (rho.ownKey v) b.before b.candidates).2) :
    ∃ r, (publisherExecution S rho).actual r ∧ r.event = i ∧ r.batch = j ∧
      r.origin = rho.ownKey v ∧ r.object = o := by
  obtain ⟨k, hk, hg⟩ := releaseAll_successful_index _ _ _ _ _ _ ho
  let r : Publication (protoOf (compiled (family S)) E) :=
    ⟨i, j, k, rho.ownKey v, b.before, b.candidates, o, hk⟩
  refine ⟨r, ?_, rfl, rfl, rfl, rfl⟩
  rw [publisherExecution_actual_iff]
  refine ⟨?_, hg⟩
  rw [executedPublication_iff]
  change (eventBatches rho i)[j]? = some ⟨b.before, b.candidates⟩ ∧
    ∃ u, rho.SendsAt (rho.key (rho.ownKey v)) i u
  have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
  exact ⟨hb, t, by rwa [hk]⟩

/-- Inverting duty releases retains the successful batch output, not just candidate
membership, so rejected duplicate candidates cannot become publication witnesses. -/
theorem runDuties_released_batch {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (v : V) :
    ∀ ds (nd : Model.Node (protoOf (compiled (family S)) E)) o,
    o ∈ (rho.runDuties v nd ds).2 →
    ∃ b ∈ dutyBatches rho v nd ds,
      o ∈ (Model.releaseAll (protoOf (compiled (family S)) E)
        rho.hash (rho.ownKey v) b.before b.candidates).2 := by
  intro ds
  induction ds with
  | nil =>
    intro nd o ho
    rw [rho.runDuties_nil] at ho
    exact False.elim (List.not_mem_nil ho)
  | cons d ds ih =>
    intro nd o ho
    rw [rho.runDuties_cons] at ho
    rcases List.mem_append.mp ho with ho | ho
    · rw [dutyBatches_cons]
      unfold Model.Run.dutyStep at ho
      split at ho
      · rename_i hsel
        refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [hsel, ↓reduceIte]
        exact ho
      · exact False.elim (List.not_mem_nil ho)
    · obtain ⟨b, hb, ho⟩ := ih _ o ho
      rw [dutyBatches_cons]
      exact ⟨b, List.mem_cons_of_mem _ hb, ho⟩

/-- Every event release has an actual publication occurrence in that event. -/
theorem publication_of_release {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) {v : V} {i : Nat} {t : Time}
    (he : rho.SendsAt v i t) (o : (protoOf (compiled (family S)) E).Object)
    (ho : o ∈ rho.releasesAt i) :
    ∃ r, (publisherExecution S rho).actual r ∧ r.event = i ∧
      r.origin = rho.ownKey v ∧ r.object = o := by
  have hb : ∃ b ∈ eventBatches rho i,
      o ∈ (Model.releaseAll (protoOf (compiled (family S)) E)
        rho.hash (rho.ownKey v) b.before b.candidates).2 := by
    rcases he with he | ⟨receipt, he⟩
    · rw [eventBatches_eq, he]
      simp only [Model.Run.releasesAt, he, Model.Run.tick] at ho
      split at ho
      · rename_i hw
        simp only [hw, ↓reduceIte]
        rcases List.mem_append.mp ho with ho | ho
        · obtain ⟨b, hb, ho⟩ := runDuties_released_batch S rho v _ _ o ho
          exact ⟨b, List.mem_append_left _ hb, ho⟩
        · exact ⟨_, List.mem_append_right _ List.mem_cons_self, ho⟩
      · exact False.elim (List.not_mem_nil ho)
    · rw [eventBatches_eq, he]
      simp only [Model.Run.releasesAt, he, Model.Run.deliver] at ho
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨b, hb, ho⟩ := runDuties_released_batch S rho v _ _ o ho
        exact ⟨b, List.mem_append_left _ hb, ho⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, ho⟩
  obtain ⟨b, hb, ho⟩ := hb
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨r, hr, hi, _, hx, ho⟩ := publication_of_batch_release S rho v i j t he b hj o ho
  exact ⟨r, hr, hi, hx, ho⟩

/-- Receipt-queued wrappers have concrete same-event publication witnesses. -/
theorem delivery_pending_publication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {o : (protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (c : (protoOf (compiled (family S)) E).Object)
    (hc : c ∈ pendingWrappers
      (process (stateAt S rho hn v i) o (digests rho.hash o))) :
    ∃ r, (publisherExecution S rho).actual r ∧ r.event = i ∧
      r.origin = rho.ownKey v ∧ r.object = c := by
  exact publication_of_release S rho (Or.inr ⟨o, he⟩) c
    (delivery_pending_released S rho hn hv he c hc)

/-- Enqueuing a new acceptance never removes an earlier pending block wrapper. -/
theorem queueAccepted_forwards_mono {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) (B : Blk sp) :
    st.forwards ⊆ (queueAccepted st B).forwards := by
  unfold queueAccepted
  split
  · exact List.Subset.refl _
  · rename_i root _
    cases hp : (if root = sp.genesisRoot then some none else
        (st.wrappers root).map some) with
    | none => exact List.Subset.refl _
    | some p => exact fun _ h => List.mem_append_left _ h

/-- Handler folds retain pending block wrappers even when later calls refuse input. -/
theorem apply_forwards_mono {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) r :
    st.forwards ⊆ (apply st r).forwards := by
  have hf : ∀ cs : List (Cut (goldilocksNode sp ro)), ∀ s : State sp ro,
      s.forwards ⊆ (cs.foldl (fun s c => match c with
        | .fg (.block B true) => queueAccepted s B | _ => s) s).forwards := by
    intro cs
    induction cs with
    | nil => exact fun _ => List.Subset.refl _
    | cons c cs ih =>
      intro s
      simp only [List.foldl_cons]
      cases c with
      | ac _ => exact ih s
      | fg c =>
        cases c with
        | attest _ _ => exact ih s
        | attestation _ => exact ih s
        | block B b =>
          cases b
          · exact ih s
          · exact fun q h => ih _ (queueAccepted_forwards_mono s B h)
  exact hf r.2 st

/-- Recursive receipt calls retain every wrapper already queued in this event. -/
theorem processOne_forwards_mono {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) hs o :
    st.forwards ⊆ (processOne hs st o).forwards := by
  unfold processOne
  split
  · unfold relayIf
    dsimp only
    split <;> exact apply_forwards_mono st _
  · exact apply_forwards_mono st _
  · unfold relayIf
    simp only [↓reduceIte]
    exact apply_forwards_mono st _
  · exact List.Subset.refl _

/-- A wrapper queued at an intermediate receipt cut survives the remaining traversal. -/
theorem process_fold_forwards_mono {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (hs : List (Header Info × Nat))
    (xs : List (Wire sp.n)) (st : State sp ro) :
    st.forwards ⊆ (xs.foldl (processOne hs) st).forwards := by
  induction xs generalizing st with
  | nil => exact List.Subset.refl _
  | cons o os ih => exact fun q h => ih _ (processOne_forwards_mono st hs o h)

/-- A successful block call in a receipt leaves its exact stamped child in the final
queue, even when subsequent calls are refused or queue further children. -/
theorem processOne_acceptance_pending {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro) hs o (B : Blk sp)
    (tail : List (Wire sp.n)) (hcover : WrappersCover st)
    (he : canonEvent sp ro hs o = some (.block B))
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2) :
    ∃ p : Option (Wire sp.n), (st.now, p.toList ++ [blockObj sp B]) ∈
      (tail.foldl (processOne hs) (processOne hs st o)).forwards := by
  obtain ⟨p, hp⟩ := onBlock_queues_acceptance st B hcover ha
  refine ⟨p, process_fold_forwards_mono hs tail _ ?_⟩
  have hm : (st.now, p.toList ++ [blockObj sp B]) ∈
      (apply st (Node.onBlock st.self st.node st.now B)).forwards := by
    rw [hp]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  simp only [processOne, he]
  unfold relayIf
  split <;> exact hm

/-- Every successful block record in a recursive receipt traversal leaves a matching
stamped child in its final queue. Coverage is threaded through actual intermediate states. -/
theorem deliverRecs_acceptance_pending {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)) (hs : List (Header Info × Nat))
    (event : Nat) (xs : List (Wire sp.n)) (st : State sp ro) (sub : Nat)
    (hcover : WrappersCover st) (r : CutRec sp ro) (B : Blk sp)
    (hr : r ∈ deliverRecs proposer dg hs st.self st.now event xs st.node sub)
    (hb : r.label = .fg (.block B true)) :
    ∃ p : Option (Wire sp.n), (st.now, p.toList ++ [blockObj sp B]) ∈
      (xs.foldl (processOne hs) st).forwards := by
  induction xs generalizing st sub with
  | nil => simp only [deliverRecs_nil, List.not_mem_nil] at hr
  | cons o os ih =>
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hr
      simpa only [List.foldl_cons, processOne, he] using ih st (sub + 1) hcover hr
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hr
        have hl := (getElem_groupRecs proposer dg st.self st.node st.now
          (Nat.pair event sub) e k hk).2.2.2.2
        have ha : .fg (.block B true) ∈ (Node.exec proposer dg st.self st.node st.now e).2 := by
          rw [hkr, hb] at hl
          exact hl.symm ▸ List.getElem_mem _
        rcases canonEvent_cases (ro := ro) hs o with hn | ⟨C, hc⟩ | ⟨m, hm⟩ | ⟨a, ha'⟩
        · rw [hn] at he; cases he
        · have ee := Option.some.inj (he.symm.trans hc)
          subst e
          have hBC : B = C := by
            have h := ha
            simp only [Node.exec, Node.onBlock] at h
            split at h
            · simp at h
            · split at h
              · simp at h
              · simpa [Node.acCall] using h
          subst C
          exact processOne_acceptance_pending st hs o B os hcover hc ha
        · have ee := Option.some.inj (he.symm.trans hm)
          subst e
          simp [Node.exec, Node.onMessage, Node.acCall] at ha
        · have ee := Option.some.inj (he.symm.trans ha')
          subst e
          simp [Node.exec, Node.onAttestation] at ha
      · have hc := wrappersCover_processOne st o hs hcover
        have hh : r ∈ deliverRecs proposer dg hs (processOne hs st o).self
            (processOne hs st o).now event os (processOne hs st o).node (sub + 1) := by
          simpa only [processOne_self, processOne_now, processOne_node proposer dg, he] using hr
        simpa only [List.foldl_cons, processOne_now] using ih _ (sub + 1) hc hh

/-- An actual receipt acceptance produces a publication in that same engine event.
The coverage and release-readiness premises are discharged by reachable invariants. -/
theorem delivery_acceptance_publication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {o : (protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true)) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B := by
  have ht : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he)
  rw [eventCuts_deliver S rho hn i v o t he] at hr
  have hr' : r ∈ deliverRecs (runProposer S rho hn) (digestOf S rho)
      (digests rho.hash o) (stateAt S rho hn v i).self (stateAt S rho hn v i).now i
      (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node 0 := by
    simpa only [self_eq_ownKey, ht] using hr
  obtain ⟨p, hp⟩ := deliverRecs_acceptance_pending (runProposer S rho hn) (digestOf S rho)
    (digests rho.hash o) i _ _ 0 (stateAt_wrappersCover S rho hn v i) r B hr' hb
  have hc : forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∈
      pendingWrappers (process (stateAt S rho hn v i) o (digests rho.hash o)) := by
    rw [pendingWrappers_eq]
    refine List.mem_map.mpr ⟨_, hp, ?_⟩
    have hself : (process (stateAt S rho hn v i) o (digests rho.hash o)).self =
        rho.ownKey v := (process_self _ _ _).trans (self_eq_ownKey S rho hn v i)
    simp only [ht, forwardObj]
    rw [hself]
  obtain ⟨q, hq, hi, hx, ho⟩ := delivery_pending_publication S rho hn hv he _ hc
  exact ⟨p, q, hq, hi, hx, ho⟩

/-- Every intermediate duty prefix of a tick inherits the reachable forwarding inventory.
No release-success premise is supplied by the caller. -/
theorem tick_duty_prefix_inventory {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (i : Nat) (t : Time)
    (ds : List (protoOf (compiled (family S)) E).Duty) :
    let nd := (rho.runDuties v
      ⟨(protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
        (mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ ds).1
    WrappersAccounted (sp := S.params (pubOf E) hn)
      (fun c => c ∈ nd.seen.flatMap Obj.parts) (shapeOf S hn nd) ∧
      PendingReady nd.seen (pendingWrappers (shapeOf S hn nd)) := by
  obtain ⟨ha, hr⟩ := stateBefore_forwardInventory S rho hn v i
  apply runDuties_forwardInventory S rho hn
  · exact self_eq_ownKey S rho hn v i
  · simpa only [wrappersAccounted_iff, pendingWrappers_eq, shapeOf,
      shapeOf_clock S hn, stateAt] using ha
  · simpa only [pendingWrappers_eq, shapeOf, shapeOf_clock S hn, stateAt] using hr
  · exact stateAt_forwardQueueCanonical S rho hn v i

/-- A poll following any actual tick-duty prefix releases all its queued block wrappers.
Neither the ordinary emission nor the later vote suffix adds a caller guard premise. -/
theorem tick_duty_prefix_poll_released {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (i : Nat) (t : Time)
    (ds : List (protoOf (compiled (family S)) E).Duty) :
    let nd := (rho.runDuties v
      ⟨(protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
        (mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ ds).1
    ∀ c ∈ pendingWrappers (shapeOf S hn nd),
      c ∈ (rho.dutyStep v nd (.poll t.toNat)).2 := by
  let start : Model.Node (protoOf (compiled (family S)) E) :=
    ⟨(protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
      (mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
  have hself : (shapeOf S hn (rho.runDuties v start ds).1).self = rho.ownKey v := by
    apply runDuties_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h)
      (fun st h => (nodeTick_self st).trans h)
      (fun st t h => (poll_self st t).trans h)
    exact self_eq_ownKey S rho hn v i
  have hc : ForwardQueueCanonical (shapeOf S hn (rho.runDuties v start ds).1) := by
    apply runDuties_pres S rho hn ForwardQueueCanonical canonical_recordOwn
      (fun st s h => by unfold propose; dsimp only; split <;> exact h)
      (fun st h => by
        unfold nodeTick
        split
        · exact forwardQueueCanonical_apply st _ h
        · exact h)
      (fun st t _ => canonical_poll st t)
    exact stateAt_forwardQueueCanonical S rho hn v i
  have hs := forwardQueueCanonical_pending _ hc
  rw [hself] at hs
  exact dutyStep_poll_pending S rho hn v _ _ (poll_selected S rho hv v) hself
    (tick_duty_prefix_inventory S rho hn v i t ds).2 hs

/-- A release in a duty after a prefix is retained by the enclosing duty run. -/
theorem duty_release_in_runDuties {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (v : V)
    (nd : Model.Node (protoOf (compiled (family S)) E))
    (pre post : List (protoOf (compiled (family S)) E).Duty)
    (d : (protoOf (compiled (family S)) E).Duty)
    (c : (protoOf (compiled (family S)) E).Object)
    (hc : c ∈ (rho.dutyStep v (rho.runDuties v nd pre).1 d).2) :
    c ∈ (rho.runDuties v nd (pre ++ d :: post)).2 := by
  induction pre generalizing nd with
  | nil =>
    rw [List.nil_append, rho.runDuties_cons]
    exact List.mem_append_left _ hc
  | cons a pre ih =>
    rw [List.cons_append, rho.runDuties_cons]
    apply List.mem_append_right
    apply ih
    simpa only [rho.runDuties_cons] using hc

/-- A queued wrapper at any poll position of a real tick has a same-event publication.
This discharges publication existence once acceptance has been located before that poll. -/
theorem tick_pending_publication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (pre post : List (protoOf (compiled (family S)) E).Duty)
    (hd : (protoOf (compiled (family S)) E).duties t = pre ++ .poll t.toNat :: post)
    (c : (protoOf (compiled (family S)) E).Object)
    (hc : c ∈ pendingWrappers (shapeOf S hn (rho.runDuties v
      ⟨(protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
        (mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ pre).1)) :
    ∃ r, (publisherExecution S rho).actual r ∧ r.event = i ∧
      r.origin = rho.ownKey v ∧ r.object = c := by
  apply publication_of_release S rho (Or.inl he) c
  simp only [Model.Run.releasesAt, he]
  rw [rho.tick_of_awake _ _ _ (hv.tick_awake v t (List.mem_of_getElem? he))]
  apply List.mem_append_left
  rw [hd]
  exact duty_release_in_runDuties S rho v _ pre post _ c
    (tick_duty_prefix_poll_released S rho hn hv v i t pre c hc)

/-- Recording a successfully decoded own canonical block runs precisely its block handler. -/
theorem recordOwn_decoded_block {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (hs : List (Header Info × Nat)) (o : Wire sp.n) (B : Blk sp)
    (hd : decodeBlock sp hs o = some B) :
    recordOwn st o hs = apply st (Node.onBlock st.self st.node st.now B) := by
  unfold decodeBlock at hd
  split at hd <;> try { cases hd }
  split at hd <;> try { cases hd }
  dsimp only at hd
  split_ifs at hd
  all_goals
    simp_all only [Option.some.injEq]
    subst B
    simp_all [recordOwn]

/-- A released own canonical block that the node accepts queues its exact wrapper.
This local bridge keeps acceptance distinct from mere release of a refused block. -/
theorem recordOwn_acceptance_pending {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))} (st : State sp ro)
    (hs : List (Header Info × Nat)) (o : Wire sp.n) (B : Blk sp)
    (hd : decodeBlock sp hs o = some B) (hcover : WrappersCover st)
    (ha : .fg (.block B true) ∈ (Node.onBlock st.self st.node st.now B).2) :
    ∃ p : Option (Wire sp.n),
      forwardObj sp st.self st.now p B ∈ pendingWrappers (recordOwn st o hs) := by
  rw [recordOwn_decoded_block st hs o B hd]
  obtain ⟨p, hp⟩ := onBlock_queues_acceptance st B hcover ha
  refine ⟨p, ?_⟩
  rw [pendingWrappers_eq, hp]
  refine List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  simp only [apply_self, forwardObj]

/-- A successful singleton batch really records its sole candidate. -/
theorem releaseAll_singleton_recorded {pub : Public} {O : Type} (P : Protocol pub O)
    (hash : P.Item → Nat) (x : Key pub) (nd : Model.Node P) (o : P.Object)
    (ho : o ∈ (Model.releaseAll P hash x nd [o]).2) :
    (Model.releaseAll P hash x nd [o]).1 =
      ⟨P.recordOwn nd.st o (digests hash o), nd.seen ++ [o]⟩ := by
  unfold Model.releaseAll at ho ⊢
  split
  · rfl
  · rename_i h
    simp only [h, Bool.false_eq_true, ↓reduceIte, Model.releaseAll, List.not_mem_nil] at ho

/-- Coverage is available after every tick-duty prefix, including immediately before
the own proposal is recorded. It is derived from reachable state, not an endpoint premise. -/
theorem tick_duty_prefix_wrappersCover {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (i : Nat) (t : Time)
    (ds : List (protoOf (compiled (family S)) E).Duty) :
    WrappersCover (shapeOf S hn (rho.runDuties v
      ⟨(protoOf (compiled (family S)) E).clock (rho.stateBefore i v).st t
        (mempool rho.inbox v t), (rho.stateBefore i v).seen⟩ ds).1) := by
  apply runDuties_wrappersCover S rho hn
  simpa only [wrappersCover_iff, shapeOf, shapeOf_clock S hn, stateAt] using
    stateAt_wrappersCover S rho hn v i

/-- A released singleton proposal that its actual recording handler accepts queues a
wrapper before the following poll. This uses the post-propose, pre-record state. -/
theorem dutyStep_propose_acceptance_pending {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (o : (protoOf (compiled (family S)) E).Object) (B : Blk (S.params (pubOf E) hn))
    (hsel : rho.ownKey v ∈ rho.sel (.proposer s))
    (hcs : rho.signedCandidate v (.propose s hs)
      ((protoOf (compiled (family S)) E).act nd.st (.propose s hs)).2 = [o])
    (ho : o ∈ (rho.dutyStep v nd (.propose s hs)).2)
    (hd : decodeBlock (S.params (pubOf E) hn) (digests rho.hash o) o = some B)
    (hc : WrappersCover (propose (shapeOf S hn nd) s).1)
    (ha : .fg (.block B true) ∈
      (Node.onBlock (propose (shapeOf S hn nd) s).1.self
        (propose (shapeOf S hn nd) s).1.node (propose (shapeOf S hn nd) s).1.now B).2) :
    ∃ p, forwardObj (S.params (pubOf E) hn) (shapeOf S hn nd).self
      (shapeOf S hn nd).now p B ∈
        pendingWrappers (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) := by
  have hrole : (protoOf (compiled (family S)) E).role (.propose s hs) = .proposer s := rfl
  simp only [Model.Run.dutyStep, hrole, hsel, ↓reduceIte, hcs] at ho ⊢
  rw [releaseAll_singleton_recorded _ _ _ _ _ ho]
  change ∃ p, forwardObj (S.params (pubOf E) hn) (shapeOf S hn nd).self
    (shapeOf S hn nd).now p B ∈ pendingWrappers
      (recordOwn (((protoOf (compiled (family S)) E).act nd.st (.propose s hs)).1.1 hn)
        o (digests rho.hash o))
  rw [shapeOf_act_propose S hn]
  simpa only [propose_self, propose_now] using
    recordOwn_acceptance_pending (propose (shapeOf S hn nd) s).1 _ o B hd hc ha

/-- A successful proposal-step block cut releases its canonical block in that duty.
The carried-object premise is the existing proposal release contract. -/
theorem dutyStep_propose_accepted_release {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {runProposer S rho hn s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (pubOf E) hn).toParams.slotTime s)
    (hrel : rho.ownKey v ∈ rho.sel (.proposer s) →
      ∀ par info cs, (propose (shapeOf S hn nd) s).2 = some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure nd.seen)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
      (encodeTxs nd.st.2) .proposal).2) :
    blockObj (S.params (pubOf E) hn) B ∈ (rho.dutyStep v nd (.propose s hs)).2 := by
  rw [(dutyStep_propose_full S rho hn v nd s hs hsel hself hslot hst hrel).1]
  exact mem_blockObjs.mpr ⟨B, true, ha, rfl⟩

/-- A proposal duty that releases a given object had exactly that singleton candidate.
This rules out confusing its release with a rejected duplicate at another index. -/
theorem dutyStep_propose_candidate_eq {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (v : V)
    (nd : Model.Node (protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (o : (protoOf (compiled (family S)) E).Object)
    (ho : o ∈ (rho.dutyStep v nd (.propose s hs)).2) :
    rho.ownKey v ∈ rho.sel (.proposer s) ∧
      rho.signedCandidate v (.propose s hs)
        ((protoOf (compiled (family S)) E).act nd.st (.propose s hs)).2 = [o] := by
  have hl := act_candidates_length S nd.st (.propose s hs) (fun _ h => by cases h)
  unfold Model.Run.dutyStep at ho
  split at ho
  · rename_i hsel
    refine ⟨hsel, ?_⟩
    have hm := Model.releaseAll_subset _ _ _ _ o ho
    have hlen : (rho.signedCandidate v (.propose s hs)
        ((protoOf (compiled (family S)) E).act nd.st (.propose s hs)).2).length ≤ 1 := by
      simp only [Model.Run.signedCandidate]
      split
      · simpa only [List.length_map] using hl
      · simpa only [List.length_map] using hl
    generalize rho.signedCandidate v (.propose s hs)
      ((protoOf (compiled (family S)) E).act nd.st (.propose s hs)).2 = cs at hm hlen ⊢
    cases cs with
    | nil => exact False.elim (List.not_mem_nil hm)
    | cons a as =>
      have hz : as = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst as
      exact congrArg (fun x => [x]) (List.mem_singleton.mp hm).symm
  · exact False.elim (List.not_mem_nil ho)

/-- An accepting proposal cut is the own block handler run after `acProposal`.
The proposal duty itself does not change the handler's clock or validator. -/
theorem proposal_acceptance_recording_handler {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (s : Slot)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
      (encodeTxs nd.st.2) .proposal).2) :
    .fg (.block B true) ∈
      (Node.onBlock (propose (shapeOf S hn nd) s).1.self
        (propose (shapeOf S hn nd) s).1.node (propose (shapeOf S hn nd) s).1.now B).2 := by
  simp only [Node.tickStep] at ha
  split at ha
  · rcases hr : (Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2
        with _ | ⟨d, p⟩
    · erw [hr] at ha
      simp only [Node.acProposal, List.mem_singleton, reduceCtorEq] at ha
    · erw [hr] at ha
      simp only [List.mem_cons, Node.acProposal, reduceCtorEq, false_or,
        Node.proposeBlock] at ha
      have heq : Node.mkBlock (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _))
          (digestOf S rho) (rho.ownKey v)
          (Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
          (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p = B := by
        unfold Node.onBlock at ha
        split at ha
        · simp at ha
        · split at ha <;> simp_all [Node.acCall, Node.acProposal]
      simp only [Node.acProposal] at heq
      simp only [Node.acProposal] at hr
      simpa only [propose, hr, hself, Node.acProposal, heq] using ha
  · exact False.elim (List.not_mem_nil ha)

/-- Own recording reconstructs a non-genesis canonical block with the engine digest.
Unlike receipt decoding, own recording has no payload-validation guard. -/
theorem recordOwn_canonical_block {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (st : State (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hpar : B.parent ≠ none) (hroot : B.RootOk (digestOf S rho)) :
    recordOwn st (blockObj (S.params (pubOf E) hn) B)
        (digests rho.hash (blockObj (S.params (pubOf E) hn) B)) =
      apply st (Node.onBlock st.self st.node st.now B) := by
  have hb : blockOf (S.params (pubOf E) hn)
      (rho.hash (headerOf (S.params (pubOf E) hn) B))
      (headerOf (S.params (pubOf E) hn) B) B.proposer B.fgPayload B.acPayload = B := by
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hpar
    change B.root = digestOf S rho B.parent B.slot B.input B.fgPayload B.acPayload at hroot
    simp only [digestOf, dgOf] at hroot
    cases B
    simp_all only [blockOf, headerOf, parentRoot_parentRef]
  simp only [blockObj, recordOwn, headerOf, decodeInfo_encodeInfo]
  erw [rootOf_digests_item]
  exact congrArg (fun b => apply st (Node.onBlock st.self st.node st.now b)) hb

/-- A released canonical proposal accepted by its actual proposal step enters the
forward queue. Receipt-decoder validity is not a premise of this own-recording bridge. -/
theorem dutyStep_propose_accepted_pending {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (B : Blk (S.params (pubOf E) hn))
    (hpar : B.parent ≠ none) (hroot : B.RootOk (digestOf S rho))
    (ho : blockObj (S.params (pubOf E) hn) B ∈ (rho.dutyStep v nd (.propose s hs)).2)
    (hc : WrappersCover (propose (shapeOf S hn nd) s).1)
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
      (encodeTxs nd.st.2) .proposal).2) :
    ∃ p, forwardObj (S.params (pubOf E) hn) (shapeOf S hn nd).self
      (shapeOf S hn nd).now p B ∈
        pendingWrappers (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) := by
  obtain ⟨hsel, hcs⟩ := dutyStep_propose_candidate_eq S rho v nd s hs _ ho
  have hrole : (protoOf (compiled (family S)) E).role (.propose s hs) = .proposer s := rfl
  simp only [Model.Run.dutyStep, hrole, hsel, ↓reduceIte, hcs] at ho ⊢
  rw [releaseAll_singleton_recorded _ _ _ _ _ ho]
  change ∃ p, forwardObj (S.params (pubOf E) hn) (shapeOf S hn nd).self
    (shapeOf S hn nd).now p B ∈ pendingWrappers
      (recordOwn (((protoOf (compiled (family S)) E).act nd.st (.propose s hs)).1.1 hn)
        (blockObj _ B) (digests rho.hash (blockObj _ B)))
  rw [shapeOf_act_propose S hn, recordOwn_canonical_block S rho hn _ B hpar hroot]
  have hh := proposal_acceptance_recording_handler S rho hn v nd s hself B ha
  obtain ⟨p, hp⟩ := onBlock_queues_acceptance _ B hc hh
  refine ⟨p, ?_⟩
  rw [pendingWrappers_eq, hp]
  refine List.mem_map.mpr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  simp only [apply_self, propose_self, propose_now, forwardObj]

/-- Proposal cuts carry the digest and parent of the block just constructed by the node. -/
theorem proposal_acceptance_block_fields {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    (B : Blk sp)
    (ha : .fg (.block B true) ∈ (Node.tickStep proposer dg self st t x .proposal).2) :
    B.RootOk dg ∧ B.parent ≠ none := by
  simp only [Node.tickStep] at ha
  split at ha
  · split at ha
    · simp [Node.acProposal] at ha
    · simp only [Node.proposeBlock, Node.onBlock] at ha
      split at ha
      · simp [Node.acProposal] at ha
      · split at ha <;> simp [Node.acCall, Node.acProposal] at ha
        obtain ⟨rfl, _⟩ := ha
        exact ⟨rfl, by simp [Node.mkBlock]⟩
  · exact False.elim (List.not_mem_nil ha)

/-- With the existing proposal release contract, acceptance queues the exact canonical
wrapper. Its root, parent, release, and recording acceptance are derived, not assumed. -/
theorem dutyStep_propose_acceptance_queued {V : Type} [Fintype V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (v : V) (nd : Model.Node (protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {runProposer S rho hn s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (pubOf E) hn).toParams.slotTime s)
    (hrel : rho.ownKey v ∈ rho.sel (.proposer s) →
      ∀ par info cs, (propose (shapeOf S hn nd) s).2 = some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure nd.seen)
    (hc : WrappersCover (propose (shapeOf S hn nd) s).1)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
      (encodeTxs nd.st.2) .proposal).2) :
    ∃ p, forwardObj (S.params (pubOf E) hn) (shapeOf S hn nd).self
      (shapeOf S hn nd).now p B ∈
        pendingWrappers (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) := by
  obtain ⟨hroot, hpar⟩ := proposal_acceptance_block_fields _ _ _ _ _ _ B ha
  exact dutyStep_propose_accepted_pending S rho hn v nd s hs hself B hpar hroot
    (dutyStep_propose_accepted_release S rho hn v nd s hs hsel hself hslot hst hrel B ha)
    hc ha

/-- At an honest scheduled tick, an accepting proposal cut queues its exact wrapper.
Coverage and carried-object readiness come from the reachable engine prefix. -/
theorem tick_proposal_acceptance_queued {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (hh : v ∈ rho.honest) (i : Nat) (t : Time)
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
    exact self_eq_ownKey S rho hn v i
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
      proposal_releasable S rho hn hv v hh i t he s par info cs hs hone hselected hprop)
    hcover B (by simpa only [hnow, atProposal_mempool] using ha)
  exact ⟨p, by simpa only [hself, hnow] using hp⟩

/-- An accepted scheduled proposal has an actual wrapper publication in that same tick.
The witness is a successful publisher candidate, not just a queue entry. -/
theorem tick_proposal_acceptance_publication {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (v : V) (hh : v ∈ rho.honest) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node
      t (encodeTxs (mempool rho.inbox v t)) .proposal).2) :
    ∃ p r, (publisherExecution S rho).actual r ∧ r.event = i ∧
      r.origin = rho.ownKey v ∧
      r.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B := by
  obtain ⟨p, hp⟩ := tick_proposal_acceptance_queued S rho hn hv v hh i t he s hs hone ht B ha
  refine ⟨p, ?_⟩
  apply tick_pending_publication S rho hn hv he
    ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ [.propose s hs])
    [.poll t.toNat]
  · rw [duties_eq S t (hv.in_horizon _ (List.mem_of_getElem? he)).1]
    simp only [dutiesInit, hone]
    rfl
  · erw [runDuties_fst_append, runDuties_fst_cons, runDuties_fst_nil]
    rwa [atProposal_eq] at hp

end Consensus.Goldilocks.Refinement
