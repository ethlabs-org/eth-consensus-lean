module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape
public import ConsensusLean.Lemmas.Model.Objects

public section

/-! # Goldilocks Refinement: the engine-side steps

What a valid engine run (`ExecutionValid`) does to the shape's state at each event, stated on
`stateAt`: the node state inside the shape's state after an event of an honest node is the
node's handler applied to the node state before it (a tick at a public time with the encoded
mempool, a delivery one `canonEvent` after the other, a restart), the shape's clock is the time of
the node's last tick or restart, and the obligations the #92 interface listed: at most two bodies
pending at a tick, a proposal carries only released objects (so `releasable` admits it), the
own-object guard `protects` never blocks an honest node, and the digests the engine passes with a
block object map its header to its root.

The route to the node state across a tick: the engine's tick runs the duties of the time (two
poll steps, the node's tick, the slot proposal if due, two poll steps) and then the gossip, each
through `releaseAll` of the candidates it signs. A poll step's own candidate is a data body that
`recordOwn` ignores, the gossip's candidates are unsigned, so only the proposal duty changes the
node state through its released block. `atProposal` names the engine node at that duty (after the
clock, the two leading poll steps and the node's tick); `proposal_releasable` is stated on it,
because the proposal the engine releases is `propose` of that node, not of the node before the
tick. `node_of_tick_public` then matches `tick_node_eq` against the node's `onTick`.

The remaining `sorry` theorems are the open obligations. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-! ## Shape-level preservation -/

/-- `apply` keeps the key. -/
theorem apply_self (st : State sp ro) r : (apply st r).self = st.self := rfl
/-- `apply` keeps the clock. -/
theorem apply_now (st : State sp ro) r : (apply st r).now = st.now := rfl
/-- `apply` keeps the FG-due flag. -/
theorem apply_fgDue (st : State sp ro) r : (apply st r).fgDue = st.fgDue := rfl
/-- `apply` installs the node state of its handler result. -/
theorem apply_node (st : State sp ro) r : (apply st r).node = r.1 := rfl

/-- `relayIf` keeps the key. -/
theorem relayIf_self (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).self = st.self := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the clock. -/
theorem relayIf_now (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).now = st.now := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the FG-due flag. -/
theorem relayIf_fgDue (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).fgDue = st.fgDue := by unfold relayIf; split <;> rfl
/-- `relayIf` keeps the node state. -/
theorem relayIf_node (st : State sp ro) (c : Prop) [Decidable c] o :
    (relayIf st c o).node = st.node := by unfold relayIf; split <;> rfl

/-- Processing one delivered object keeps the key. -/
theorem processOne_self hs (st : State sp ro) o : (processOne hs st o).self = st.self := by
  unfold processOne; split <;> simp [relayIf_self, apply_self]
/-- Processing one delivered object keeps the clock. -/
theorem processOne_now hs (st : State sp ro) o : (processOne hs st o).now = st.now := by
  unfold processOne; split <;> simp [relayIf_now, apply_now]
/-- Processing one delivered object keeps the FG-due flag. -/
theorem processOne_fgDue hs (st : State sp ro) o : (processOne hs st o).fgDue = st.fgDue := by
  unfold processOne; split <;> simp [relayIf_fgDue, apply_fgDue]

/-- Processing a list of delivered objects keeps the key. -/
theorem foldl_processOne_self hs (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).self = st.self := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_self]
/-- Processing a list of delivered objects keeps the clock. -/
theorem foldl_processOne_now hs (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).now = st.now := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_now]
/-- Processing a list of delivered objects keeps the FG-due flag. -/
theorem foldl_processOne_fgDue hs (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).fgDue = st.fgDue := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih => simp [List.foldl_cons, ih, processOne_fgDue]

/-- A delivery keeps the key. -/
theorem process_self (st : State sp ro) o hs : (process st o hs).self = st.self :=
  foldl_processOne_self hs _ st
/-- A delivery keeps the clock. -/
theorem process_now (st : State sp ro) o hs : (process st o hs).now = st.now :=
  foldl_processOne_now hs _ st
/-- A delivery keeps the FG-due flag. -/
theorem process_fgDue (st : State sp ro) o hs : (process st o hs).fgDue = st.fgDue :=
  foldl_processOne_fgDue hs _ st

/-- Recording an own object keeps the key. -/
theorem recordOwn_self (st : State sp ro) o hs : (recordOwn st o hs).self = st.self := by
  unfold recordOwn; split <;> (try split) <;> rfl
/-- Recording an own object keeps the clock. -/
theorem recordOwn_now (st : State sp ro) o hs : (recordOwn st o hs).now = st.now := by
  unfold recordOwn; split <;> (try split) <;> rfl
/-- Recording an own object keeps the FG-due flag. -/
theorem recordOwn_fgDue (st : State sp ro) o hs : (recordOwn st o hs).fgDue = st.fgDue := by
  unfold recordOwn; split <;> (try split) <;> rfl

/-- The node's tick keeps the key. -/
theorem nodeTick_self (st : State sp ro) : (nodeTick st).self = st.self := by
  unfold nodeTick; split <;> rfl
/-- The node's tick keeps the clock. -/
theorem nodeTick_now (st : State sp ro) : (nodeTick st).now = st.now := by
  unfold nodeTick; split <;> rfl

/-- The slot proposal keeps the key. -/
theorem propose_self (st : State sp ro) s : (propose st s).1.self = st.self := by
  unfold propose; split
  · simp only; split <;> rfl
  · rfl
/-- The slot proposal keeps the clock. -/
theorem propose_now (st : State sp ro) s : (propose st s).1.now = st.now := by
  unfold propose; split
  · simp only; split <;> rfl
  · rfl
/-- The slot proposal keeps the FG-due flag. -/
theorem propose_fgDue (st : State sp ro) s : (propose st s).1.fgDue = st.fgDue := by
  unfold propose; split
  · simp only; split <;> rfl
  · rfl

/-- The FG update keeps the key. -/
theorem fgUpdate_self (st : State sp ro) : (fgUpdate st).self = st.self := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl
/-- The FG update keeps the clock. -/
theorem fgUpdate_now (st : State sp ro) : (fgUpdate st).now = st.now := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl
/-- The FG update clears the FG-due flag. -/
theorem fgUpdate_fgDue (st : State sp ro) : (fgUpdate st).fgDue = false := by
  unfold fgUpdate; simp only; split
  · rfl
  · split <;> rfl

/-- A poll step keeps the key. -/
theorem poll_self (st : State sp ro) t : (poll st t).1.self = st.self := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_self]
/-- A poll step keeps the clock. -/
theorem poll_now (st : State sp ro) t : (poll st t).1.now = st.now := by
  unfold poll; simp only; split <;> split <;> simp [fgUpdate_now]
/-- After a poll step the FG update is not due: the step ran it if it was. -/
theorem poll_fgDue (st : State sp ro) t : (poll st t).1.fgDue = false := by
  unfold poll; simp only; split <;> split <;> simp_all [fgUpdate_fgDue]

/-- A restore sets the key to the restored one. -/
theorem restore_self (k : Fin sp.n) (d : State sp ro) t : (restore k d t).self = k := rfl
/-- A restore sets the clock to the restart time. -/
theorem restore_now (k : Fin sp.n) (d : State sp ro) t : (restore k d t).now = t := rfl
/-- A restore clears the FG-due flag. -/
theorem restore_fgDue (k : Fin sp.n) (d : State sp ro) t : (restore k d t).fgDue = false := rfl

end Consensus.Goldilocks.Refinement

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-- The shape's state at `hn` inside an engine node. -/
abbrev shapeOf (nd : Model.Node (Model.protoOf (compiled (family S)) E)) :
    State (S.params (pubOf E) hn) (S.ro _) :=
  nd.st.1 hn

omit [DecidableEq V] in
/-- `recordOwn` of the engine node is the shape's `recordOwn`. -/
theorem shapeOf_recordOwn (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (c : (Model.protoOf (compiled (family S)) E).Object) (hs) :
    shapeOf S hn ⟨(Model.protoOf (compiled (family S)) E).recordOwn nd.st c hs, nd.seen ++ [c]⟩ =
      recordOwn (shapeOf S hn nd) c hs := rfl

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn` is preserved by `releaseAll`: the
engine records each released object with `recordOwn` and drops the rest. -/
theorem releaseAll_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs)) (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (cs : List (Model.protoOf (compiled (family S)) E).Object), Q (shapeOf S hn nd) →
      Q (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd cs).1)
  | _, [], h => h
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · exact releaseAll_pres Q hrec k _ cs (hrec _ _ _ h)
    · exact releaseAll_pres Q hrec k nd cs h

omit [DecidableEq V] in
/-- The engine's `propose` duty is the shape's `propose`. -/
theorem shapeOf_act_propose (st : (Model.protoOf (compiled (family S)) E).State) (s : Slot)
    (h : 0 < s) :
    ((Model.protoOf (compiled (family S)) E).act st (.propose s h)).1.1 hn =
      (propose (st.1 hn) s).1 := by
  change ((family S (pubOf E)).propose st.1 s).1 hn = _
  simp only [family, dite_eq_left hn]
  rfl

omit [DecidableEq V] in
/-- The engine's `pollPropose` duty is the shape's `nodeTick`. -/
theorem shapeOf_act_pollPropose (st : (Model.protoOf (compiled (family S)) E).State) (t : Nat) :
    ((Model.protoOf (compiled (family S)) E).act st (.pollPropose t)).1.1 hn =
      nodeTick (st.1 hn) := by
  change ((family S (pubOf E)).pollPropose st.1 t).1 hn = _
  simp only [family, dite_eq_left hn]
  rfl

omit [DecidableEq V] in
/-- The engine's `poll` duty is the shape's `poll`. -/
theorem shapeOf_act_poll (st : (Model.protoOf (compiled (family S)) E).State) (t : Nat) :
    ((Model.protoOf (compiled (family S)) E).act st (.poll t)).1.1 hn =
      (poll (st.1 hn) t).1 := by
  change ((family S (pubOf E)).poll st.1 t).1 hn = _
  simp only [family, dite_eq_left hn]
  rfl

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn`, `propose`, `nodeTick` and `poll` is
preserved by every duty step of the engine. -/
theorem dutyStep_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (htick : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty) (h : Q (shapeOf S hn nd)) :
    Q (shapeOf S hn (rho.dutyStep v nd d).1) := by
  unfold Model.Run.dutyStep
  apply releaseAll_pres S rho hn Q hrec
  cases d with
  | propose s hs =>
    have := hprop _ s h
    rw [← shapeOf_act_propose S hn nd.st s hs] at this
    exact this
  | act s k => exact k.elim
  | pollPropose t =>
    have := htick _ h
    rw [← shapeOf_act_pollPropose S hn nd.st t] at this
    exact this
  | poll t =>
    have := hpoll _ t h
    rw [← shapeOf_act_poll S hn nd.st t] at this
    exact this

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn`, `propose`, `nodeTick` and `poll` is
preserved by running a list of duties. -/
theorem runDuties_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (htick : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (ds : List (Model.protoOf (compiled (family S)) E).Duty) (h : Q (shapeOf S hn nd)) :
    Q (shapeOf S hn (rho.runDuties v nd ds).1) := by
  unfold Model.Run.runDuties
  suffices ∀ acc : Model.Node (Model.protoOf (compiled (family S)) E) ×
      List (Model.protoOf (compiled (family S)) E).Object, Q (shapeOf S hn acc.1) →
      Q (shapeOf S hn (ds.foldl (fun r d => let s := rho.dutyStep v r.1 d; (s.1, r.2 ++ s.2))
        acc).1) from this (nd, []) h
  induction ds with
  | nil => intro acc h; exact h
  | cons d ds ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (dutyStep_pres S rho hn Q hrec hprop htick hpoll v acc.1 d h)

omit [DecidableEq V] in
/-- The engine's `clock` sets the shape's clock to the tick time. -/
theorem shapeOf_clock (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time)
    (xs : List Tx) :
    ((Model.protoOf (compiled (family S)) E).clock nd.st t xs).1 hn =
      { nd.st.1 hn with now := t } := rfl

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn`, `propose`, `nodeTick` and `poll` holds
after an engine tick if it holds for the clocked state before it: an asleep node's tick leaves the
state clocked, an awake node's runs the duties and the gossip. -/
theorem tick_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (htick : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time)
    (h : Q { nd.st.1 hn with now := t }) :
    Q (shapeOf S hn (rho.tick nd v t).1) := by
  unfold Model.Run.tick
  simp only
  split
  · exact releaseAll_pres S rho hn Q hrec _ _ _
      (runDuties_pres S rho hn Q hrec hprop htick hpoll v _ _ h)
  · exact h

omit [DecidableEq V] in
/-- The engine's `process` is the shape's `process`. -/
theorem shapeOf_process (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (o : (Model.protoOf (compiled (family S)) E).Object) (hs) :
    ((Model.protoOf (compiled (family S)) E).process nd.st o hs).1 hn =
      process (nd.st.1 hn) o hs := rfl

omit [DecidableEq V] in
/-- The engine's `restore` of the durable state is the shape's `restore`. -/
theorem shapeOf_restore (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time) :
    ((Model.protoOf (compiled (family S)) E).restore k
      ((Model.protoOf (compiled (family S)) E).durable nd.st) t).1 hn =
      restore k (nd.st.1 hn) t := rfl

/-! ## `stateAt` across an event -/

/-- The shape's state before the first event is its initial state at the own key. -/
theorem stateAt_zero (v : V) :
    stateAt S rho hn v 0 = (goldilocksShape _ _).init (rho.ownKey v) := rfl

/-- The shape's state after event `i` is the engine's `step` on the state before it. -/
theorem stateAt_succ (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some e) :
    stateAt S rho hn v (i + 1) = (rho.step (rho.stateBefore i) e v).st.1 hn := by
  simp only [stateAt, rho.stateBefore_succ he]

/-- Past the last event the shape's state is constant. -/
theorem stateAt_succ_none (v : V) {i : Nat} (he : rho.events[i]? = none) :
    stateAt S rho hn v (i + 1) = stateAt S rho hn v i := by
  have : rho.events.take (i + 1) = rho.events.take i := by
    have hl := List.getElem?_eq_none_iff.1 he
    rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
  simp only [stateAt, Model.Run.stateBefore, this]

/-- An event of another node leaves the shape's state unchanged. -/
theorem state_of_other (v : V) (i : Nat)
    (e : Model.Event V (Model.protoOf (compiled (family S)) E).Object)
    (he : rho.events[i]? = some e) (hne : e.node ≠ v) :
    stateAt S rho hn v (i + 1) = stateAt S rho hn v i := by
  rw [stateAt_succ S rho hn v he]
  cases e <;> simp only [Model.Event.node] at hne <;>
    simp only [Model.Run.step, Function.update_of_ne (Ne.symm hne)] <;> rfl

/-- The shape's state after a tick of `v` is the shape of the engine's `tick`. -/
theorem stateAt_tick (v : V) {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t)) :
    stateAt S rho hn v (i + 1) = shapeOf S hn (rho.tick (rho.stateBefore i v) v t).1 := by
  rw [stateAt_succ S rho hn v he]
  simp only [Model.Run.step, Function.update_self]

/-- The shape's state after a delivery to `v` is the shape's `process` of the delivered object with
the engine's digests. -/
theorem stateAt_deliver (v : V) {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) :
    stateAt S rho hn v (i + 1) =
      process (stateAt S rho hn v i) o (Model.digests rho.hash o) := by
  rw [stateAt_succ S rho hn v he]
  simp only [Model.Run.step, Function.update_self]
  rfl

/-- The shape's state after a restart of `v` is the shape's `restore` at the own key. -/
theorem stateAt_restart (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    stateAt S rho hn v (i + 1) = restore (rho.ownKey v) (stateAt S rho hn v i) t := by
  rw [stateAt_succ S rho hn v he]
  simp only [Model.Run.step, Function.update_self]
  rfl


/-! ## Invariants of every engine cut -/

/-- The shape's key at every cut is the node's own key. -/
theorem self_eq_ownKey (v : V) : ∀ i, (stateAt S rho hn v i).self = rho.ownKey v
  | 0 => rfl
  | i + 1 => by
    match he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact self_eq_ownKey v i
    | some e =>
      by_cases hv : e.node = v
      · cases e with
        | tick v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_tick S rho hn _ he]
          exact tick_pres S rho hn (fun st => st.self = rho.ownKey v')
            (fun st o hs h => (recordOwn_self st o hs).trans h)
            (fun st s h => (propose_self st s).trans h) (fun st h => (nodeTick_self st).trans h)
            (fun st t h => (poll_self st t).trans h) v' _ t (self_eq_ownKey v' i)
        | deliver v' o t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_deliver S rho hn _ he]
          exact (process_self _ _ _).trans (self_eq_ownKey v' i)
        | restart v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_restart S rho hn _ he]; rfl
      · rw [state_of_other S rho hn v i e he hv]; exact self_eq_ownKey v i

/-- `lastClock` after a tick of `v` is the tick time. -/
theorem lastClock_succ_tick (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) : lastClock S rho v (i + 1) = t := by
  simp [lastClock, he]

/-- `lastClock` after a restart of `v` is the restart time. -/
theorem lastClock_succ_restart (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) : lastClock S rho v (i + 1) = t := by
  simp [lastClock, he]

/-- `lastClock` is unchanged by a delivery. -/
theorem lastClock_succ_deliver (v : V) {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) :
    lastClock S rho v (i + 1) = lastClock S rho v i := by
  simp [lastClock, he]

/-- `lastClock` is constant past the last event. -/
theorem lastClock_succ_none (v : V) {i : Nat} (he : rho.events[i]? = none) :
    lastClock S rho v (i + 1) = lastClock S rho v i := by
  simp [lastClock, he]

/-- `lastClock` of `v` is unchanged by an event of another node. -/
theorem lastClock_succ_other (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some e) (hne : e.node ≠ v) :
    lastClock S rho v (i + 1) = lastClock S rho v i := by
  cases e <;> simp only [Model.Event.node] at hne <;> simp [lastClock, he, hne]

/-- **`Simulates.now`.** The shape's clock before an engine cut is the time of the node's last tick
or restart before it. -/
theorem now_eq_lastClock (_hv : rho.ExecutionValid) (v : V) :
    ∀ i, (stateAt S rho hn v i).now = lastClock S rho v i
  | 0 => rfl
  | i + 1 => by
    match he : rho.events[i]? with
    | none =>
      rw [stateAt_succ_none S rho hn v he, lastClock_succ_none S rho v he]
      exact now_eq_lastClock _hv v i
    | some e =>
      by_cases hv : e.node = v
      · cases e with
        | tick v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_tick S rho hn _ he, lastClock_succ_tick S rho _ he]
          exact tick_pres S rho hn (fun st => st.now = t)
            (fun st o hs h => (recordOwn_now st o hs).trans h)
            (fun st s h => (propose_now st s).trans h) (fun st h => (nodeTick_now st).trans h)
            (fun st t h => (poll_now st t).trans h) v' _ t rfl
        | deliver v' o t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_deliver S rho hn _ he, lastClock_succ_deliver S rho _ he]
          exact (process_now _ _ _).trans (now_eq_lastClock _hv v' i)
        | restart v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_restart S rho hn _ he, lastClock_succ_restart S rho _ he]; rfl
      · rw [state_of_other S rho hn v i e he hv, lastClock_succ_other S rho v he hv]
        exact now_eq_lastClock _hv v i

/-! ## The duties of a tick -/

/-- The duties of a tick at `t ≥ 0` but the last: two poll steps, the node's tick, the slot
proposal if due, one poll step. -/
abbrev dutiesInit (t : Time) : List (Model.protoOf (compiled (family S)) E).Duty :=
  [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++
    (skeleton (Fintype.card V) S.proposer).proposeAt E.Δ t ++ [.poll t.toNat]

omit [DecidableEq V] in
/-- The duties of a tick at `t ≥ 0`: `dutiesInit` and one more poll step. -/
theorem duties_eq (t : Time) (ht : 0 ≤ t) :
    (Model.protoOf (compiled (family S)) E).duties t = dutiesInit S t ++ [.poll t.toNat] := by
  change (skeleton (Fintype.card V) S.proposer).duties E.Δ t = _
  simp only [Skeleton.duties, Skeleton.stepAt, skeleton, ht, ite_true, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, dutiesInit]
  exact congrArg (fun l => ShapeDuty.poll t.toNat :: .poll t.toNat :: .pollPropose t.toNat :: l)
    (List.append_assoc ((skeleton (Fintype.card V) S.proposer).proposeAt E.Δ t)
      [ShapeDuty.poll t.toNat] [ShapeDuty.poll t.toNat]).symm

omit [DecidableEq V] in
/-- A tick at a negative time has no duties. -/
theorem duties_eq_nil (t : Time) (ht : t < 0) :
    (Model.protoOf (compiled (family S)) E).duties t = [] := by
  change (skeleton (Fintype.card V) S.proposer).duties E.Δ t = _
  simp [Skeleton.duties, Skeleton.stepAt, Skeleton.proposeAt, skeleton, TimeGrid.slotAt?,
    not_le.2 ht]
  rfl

omit [DecidableEq V] in
/-- Running two lists of duties in sequence is running their concatenation. -/
theorem runDuties_fst_append (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (ds ds' : List (Model.protoOf (compiled (family S)) E).Duty) :
    (rho.runDuties v nd (ds ++ ds')).1 = (rho.runDuties v (rho.runDuties v nd ds).1 ds').1 := by
  unfold Model.Run.runDuties
  rw [List.foldl_append]
  generalize ds.foldl _ _ = acc
  induction ds' generalizing acc with
  | nil => rfl
  | cons d ds' ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    conv_rhs => rw [ih]

/-- The FG update is never due at a cut: every tick ends with a poll step, which runs it. -/
theorem fgDue_eq_false (v : V) : ∀ i, (stateAt S rho hn v i).fgDue = false
  | 0 => rfl
  | i + 1 => by
    match he : rho.events[i]? with
    | none => rw [stateAt_succ_none S rho hn v he]; exact fgDue_eq_false v i
    | some e =>
      by_cases hv : e.node = v
      · cases e with
        | tick v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_tick S rho hn _ he]
          unfold Model.Run.tick
          simp only
          split
          · apply releaseAll_pres S rho hn (fun st => st.fgDue = false)
              (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
            rcases le_or_gt 0 t with ht | ht
            · rw [duties_eq S t ht, runDuties_fst_append]
              change ((rho.dutyStep v' _ (.poll t.toNat)).1.st.1 hn).fgDue = false
              unfold Model.Run.dutyStep
              apply releaseAll_pres S rho hn (fun st => st.fgDue = false)
                (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
              change (((Model.protoOf (compiled (family S)) E).act _
                (.poll t.toNat)).1.1 hn).fgDue = false
              rw [shapeOf_act_poll]
              exact poll_fgDue _ _
            · rw [duties_eq_nil S t ht]
              exact fgDue_eq_false v' i
          · exact fgDue_eq_false v' i
        | deliver v' o t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_deliver S rho hn _ he]
          exact (process_fgDue _ _ _).trans (fgDue_eq_false v' i)
        | restart v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_restart S rho hn _ he]; rfl
      · rw [state_of_other S rho hn v i e he hv]; exact fgDue_eq_false v i


/-! ## The clock at a delivery -/

/-- In a valid run the events are sorted by their key, so an earlier event's key is at most a later
one's. -/
theorem keyLe_of_lt (hv : rho.ExecutionValid) {j k : Nat}
    {e f : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (hj : rho.events[j]? = some e) (hk : rho.events[k]? = some f) (hjk : j < k) :
    e.keyLe f := by
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hk
  exact List.pairwise_iff_getElem.1 hv.sorted j k hj' hk' hjk

/-- `lastClock` at a cut after a tick or restart of `v` at `t` is `t` when every event between them
is at time `t`. -/
theorem lastClock_of_between (v : V) (t : Time) (j : Nat)
    (hj : rho.events[j]? = some (.tick v t) ∨ rho.events[j]? = some (.restart v t)) :
    ∀ i, j < i → (∀ k, j < k → k < i → ∀ e, rho.events[k]? = some e → e.time = t) →
      lastClock S rho v i = t
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | i + 1, hji, hb => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
    · have ih := lastClock_of_between v t j hj i hji (fun k h1 h2 => hb k h1 (by omega))
      match he : rho.events[i]? with
      | none => rw [lastClock_succ_none S rho v he]; exact ih
      | some e =>
        have ht := hb i hji (Nat.lt_succ_self i) e he
        cases e with
        | tick v' t' =>
          simp only [Model.Event.time] at ht; subst ht
          simp [lastClock, he, ih]
        | restart v' t' =>
          simp only [Model.Event.time] at ht; subst ht
          simp [lastClock, he, ih]
        | deliver v' o t' => simp [lastClock, he, ih]
    · rcases hj with hj | hj
      · exact lastClock_succ_tick S rho v hj
      · exact lastClock_succ_restart S rho v hj

/-- **The clock at a delivery.** A delivery to `v` at `t` in a valid run comes after a tick of `v`
at `t` (the node is awake and the key order puts ticks first), so the shape's clock at it is `t`. -/
theorem lastClock_of_deliver (hv : rho.ExecutionValid) (v : V) {i : Nat}
    {o : (Model.protoOf (compiled (family S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) : lastClock S rho v i = t := by
  have hmem := List.mem_of_getElem? he
  have hhon := hv.honest_only _ hmem
  have hw := hv.deliver_awake v o t hmem
  have hh := hv.in_horizon _ hmem
  simp only [Model.Event.node, Model.Event.time] at hhon hh
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (hv.tick_total v hhon t hh.1 hh.2 hw)
  have hji : j < i := by
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · rw [he] at hj; cases hj
    · have := keyLe_of_lt S rho hv he hj h
      simp [Model.Event.keyLe, Model.Event.time, Model.Event.phase] at this
  apply lastClock_of_between S rho v t j (Or.inl hj) i hji
  intro k h1 h2 e hk
  have h₁ := keyLe_of_lt S rho hv hj hk h1
  have h₂ := keyLe_of_lt S rho hv hk he h2
  simp only [Model.Event.keyLe] at h₁ h₂
  change t < e.time ∨ t = e.time ∧ 1 ≤ e.phase at h₁
  change e.time < t ∨ e.time = t ∧ e.phase ≤ 2 at h₂
  rcases h₂ with h₂ | ⟨h₂, _⟩
  · rcases h₁ with h₁ | ⟨h₁, _⟩
    · exact absurd (lt_trans h₁ h₂) (lt_irrefl _)
    · exact absurd (h₁ ▸ h₂) (lt_irrefl _)
  · exact h₂

/-! ## The node state across a delivery -/

/-- The node state after a delivery of the objects `os` at time `t` from `st`: the handler of
each canonical object in order, nothing for a dropped object (the state `deliverRecs` threads). -/
noncomputable def deliverState (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) :
    List (Wire sp.n) → NodeState (goldilocksNode sp ro) → NodeState (goldilocksNode sp ro)
  | [], st => st
  | o :: os, st =>
      match canonEvent sp ro hs o with
      | some e => deliverState dg hs self t os (exec dg self st t e).1
      | none => deliverState dg hs self t os st

/-- The canonical event of a wire object, if any, is a block, a message or an attestation. -/
theorem canonEvent_cases hs (o : Wire sp.n) :
    canonEvent sp ro hs o = none ∨ (∃ B, canonEvent sp ro hs o = some (.block B)) ∨
      (∃ v, canonEvent sp ro hs o = some (.message v)) ∨
      (∃ a, canonEvent sp ro hs o = some (.attestation a)) := by
  unfold canonEvent
  split <;> simp

/-- Processing one delivered object runs the handler of its canonical event, nothing if it has none.
-/
theorem processOne_node (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) hs (st : State sp ro)
    o :
    (processOne hs st o).node =
      match canonEvent sp ro hs o with
      | some e => (exec dg st.self st.node st.now e).1
      | none => st.node := by
  rcases canonEvent_cases (ro := ro) hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩ <;>
    simp [processOne, h, relayIf_node, apply_node, exec]

/-- Processing a list of delivered objects runs `deliverState` on the node state. -/
theorem foldl_processOne_node (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) hs
    (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).node = deliverState dg hs st.self st.now os st.node := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih =>
    rw [List.foldl_cons, ih, processOne_self, processOne_now, processOne_node dg]
    rcases canonEvent_cases (ro := ro) hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩ <;>
      simp only [deliverState, h]

/-- **`Simulates.deliver`'s node step.** An engine delivery to an honest node runs the handlers of
the delivered canonical objects in order on the node state before it, with the digests the engine
passes. -/
theorem node_of_deliver (hv : rho.ExecutionValid) (v : V) (_hv' : v ∈ rho.honest) (i : Nat)
    (o : (Model.protoOf (compiled (family S)) E).Object) (t : Time)
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v (i + 1)).node =
      deliverState (digestOf S rho) (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node := by
  rw [stateAt_deliver S rho hn v he]
  unfold process
  refine (foldl_processOne_node (digestOf S rho) _ _ _).trans ?_
  rw [self_eq_ownKey, now_eq_lastClock S rho hn hv, lastClock_of_deliver S rho hv v he]

/-- **`Simulates.restart`'s node step.** An engine restart of an honest node runs the node's restart
on the node state before it. -/
theorem node_of_restart (_hv : rho.ExecutionValid) (v : V) (_hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.restart v t)) :
    (stateAt S rho hn v (i + 1)).node =
      (Node.exec (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t .restart).1 := by
  rw [stateAt_restart S rho hn v he]
  rfl

/-! ## Duty steps and the node state -/

/-- Recording an own signed data body changes nothing: the shape keeps no record of it. -/
theorem recordOwn_data (st : State sp ro) (k : Fin sp.n) (r : ShapeRole Empty) (b : Body)
    (cs : List (Wire sp.n)) hs : recordOwn st (.mk (.signed k r) (.data b) cs) hs = st := by
  cases r <;> rfl

omit [DecidableEq V] in
/-- `releaseAll` of candidates that `recordOwn` ignores leaves the shape's state unchanged. -/
theorem releaseAll_shape_eq (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (cs : List (Model.protoOf (compiled (family S)) E).Object),
      (∀ c ∈ cs, ∀ (st : State (S.params (pubOf E) hn) (S.ro _)) hs, recordOwn st c hs = st) →
      shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd cs).1 =
        shapeOf S hn nd
  | _, [], _ => rfl
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · rw [releaseAll_shape_eq k _ cs (fun c hc => h c (List.mem_cons_of_mem _ hc))]
      exact h c (List.mem_cons_self ..) _ _
    · exact releaseAll_shape_eq k nd cs (fun c hc => h c (List.mem_cons_of_mem _ hc))

omit [DecidableEq V] in
/-- A poll step's signed candidate is a data body, which `recordOwn` ignores. -/
theorem signedCandidate_poll_recordOwn (v : V) (t : Nat)
    (o : Option (Body × List (Model.protoOf (compiled (family S)) E).Object)) :
    ∀ c ∈ rho.signedCandidate v (.poll t) (o.map fun bc => (.data bc.1, bc.2)),
      ∀ (st : State (S.params (pubOf E) hn) (S.ro _)) hs, recordOwn st c hs = st := by
  cases o with
  | none => simp [Model.Run.signedCandidate]
  | some bc =>
    simp only [Option.map, Model.Run.signedCandidate]
    split
    · intro c hc
      simp only [List.mem_singleton] at hc
      subst hc
      intro st hs
      exact recordOwn_data st _ _ _ _ hs
    · simp

omit [DecidableEq V] in
/-- The engine's poll duty step is the shape's `poll`: its released body is not recorded. -/
theorem dutyStep_poll (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Nat) :
    shapeOf S hn (rho.dutyStep v nd (.poll t)).1 = (poll (shapeOf S hn nd) t).1 := by
  unfold Model.Run.dutyStep
  refine (releaseAll_shape_eq S rho hn _ _ _ ?_).trans (shapeOf_act_poll S hn nd.st t)
  exact signedCandidate_poll_recordOwn S rho hn v t _

omit [DecidableEq V] in
/-- The engine's `pollPropose` duty step is the shape's `nodeTick`: it releases nothing. -/
theorem dutyStep_pollPropose (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Nat) :
    shapeOf S hn (rho.dutyStep v nd (.pollPropose t)).1 = nodeTick (shapeOf S hn nd) := by
  unfold Model.Run.dutyStep
  have h2 : ((Model.protoOf (compiled (family S)) E).act nd.st (.pollPropose t)).2 = none := by
    change Option.map _ ((family S (pubOf E)).pollPropose nd.st.1 t).2 = none
    simp only [family, dite_eq_left hn]; rfl
  change shapeOf S hn (Model.releaseAll _ _ _
    ⟨((Model.protoOf (compiled (family S)) E).act nd.st (.pollPropose t)).1, nd.seen⟩
    (rho.signedCandidate v (.pollPropose t)
      ((Model.protoOf (compiled (family S)) E).act nd.st (.pollPropose t)).2)).1 = _
  rw [h2]
  exact shapeOf_act_pollPropose S hn nd.st t

omit [DecidableEq V] in
/-- Running a duty then a list of duties. -/
theorem runDuties_fst_cons (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (d : (Model.protoOf (compiled (family S)) E).Duty)
    (ds : List (Model.protoOf (compiled (family S)) E).Duty) :
    (rho.runDuties v nd (d :: ds)).1 = (rho.runDuties v (rho.dutyStep v nd d).1 ds).1 :=
  runDuties_fst_append S rho v nd [d] ds

omit [DecidableEq V] in
/-- Running no duties is the identity. -/
theorem runDuties_fst_nil (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E)) :
    (rho.runDuties v nd []).1 = nd := rfl

/-! ## The digests of an own object -/

/-- Looking a key up in the association list that pairs each element with its image finds the image.
-/
theorem find?_map_pair {α β : Type} [DecidableEq α] (f : α → β) (h : α) :
    ∀ l : List α, h ∈ l →
      ((l.map fun x => (x, f x)).find? fun q => q.1 == h).map (·.2) = some (f h)
  | [], hm => absurd hm List.not_mem_nil
  | x :: xs, hm => by
    by_cases hx : x = h
    · subst hx; simp
    · rw [List.mem_cons] at hm
      rcases hm with rfl | hm
      · exact absurd rfl hx
      · rw [List.map_cons, List.find?_cons_of_neg (by simp [hx])]
        exact find?_map_pair f h xs hm

omit [DecidableEq V] in
/-- The engine's digests of an object map each header among its parts to the engine's hash of it. -/
theorem rootOf_digests_of_mem (o : (Model.protoOf (compiled (family S)) E).Object)
    (h : Header Info) (hm : h ∈ o.parts.filterMap Model.Obj.item?) :
    rootOf (Model.digests rho.hash o) h = some (rho.hash h) :=
  find?_map_pair rho.hash h _ hm

omit [DecidableEq V] in
/-- The engine's digests of an item object map its header to the engine's hash of it. -/
theorem rootOf_digests_item (a : Model.Auth (Fintype.card V) (ShapeRole Empty)) (h : Header Info)
    (cs : List (Wire (Fintype.card V))) :
    rootOf (Model.digests rho.hash (.mk a (.item h) cs)) h = some (rho.hash h) :=
  rootOf_digests_of_mem S rho _ h
    (List.mem_filterMap.2 ⟨.mk a (.item h) cs, by simp [Model.Obj.parts], rfl⟩)

omit [DecidableEq V] in
/-- The digests the engine passes with a block object map the block's header to the engine's hash of
it. -/
theorem rootOf_digests_blockObj (B : Blk (S.params (pubOf E) hn)) :
    rootOf (Model.digests rho.hash (blockObj (S.params (pubOf E) hn) B))
        (headerOf (S.params (pubOf E) hn) B) =
      some (rho.hash (headerOf (S.params (pubOf E) hn) B)) :=
  rootOf_digests_item S rho _ _ _

/-- An object in a list is among the list's parts. -/
theorem mem_partsList {n : Nat} {R I B : Type} (c : Model.Obj n R I B) :
    ∀ cs : List (Model.Obj n R I B), c ∈ cs → c ∈ Model.Obj.parts.partsList cs
  | [], h => absurd h List.not_mem_nil
  | c' :: cs, h => by
    rw [List.mem_cons] at h
    simp only [Model.Obj.parts.partsList, List.mem_append]
    rcases h with rfl | h
    · left; cases c; simp [Model.Obj.parts]
    · right; exact mem_partsList c cs h

omit [DecidableEq V] in
/-- The digests the engine passes with a relay wrapper map the header of each carried block object
to the engine's hash of it. -/
theorem rootOf_digests_relay (cs : List (Wire (Fintype.card V))) (B : Blk (S.params (pubOf E) hn))
    (hB : blockObj (S.params (pubOf E) hn) B ∈ cs) :
    rootOf (Model.digests rho.hash (.mk .none (.data .relay) cs))
        (headerOf (S.params (pubOf E) hn) B) =
      some (rho.hash (headerOf (S.params (pubOf E) hn) B)) := by
  apply rootOf_digests_of_mem
  simp only [Model.Obj.parts, List.filterMap_cons, Model.Obj.item?]
  exact List.mem_filterMap.2 ⟨blockObj _ B, mem_partsList _ cs hB, rfl⟩


/-! ## Slots -/

/-- A time is in slot `s` of a grid starting at `0` exactly when it is the slot's start. -/
theorem slotAt?_zero_iff (G : TimeGrid) {Δ : Time} (hΔ : 0 < Δ) (t : Time) (s : Slot) :
    G.slotAt? Δ 0 t = some s ↔ t = G.slotTime Δ s := by
  have hL : 0 < G.slotLen Δ := by
    unfold TimeGrid.slotLen
    exact mul_pos (by exact_mod_cast G.slotDeltas.pos) hΔ
  unfold TimeGrid.slotAt? TimeGrid.slotTime
  simp only [sub_zero]
  constructor
  · intro h
    split at h
    · rename_i hc
      obtain ⟨hc1, hc2⟩ := hc
      cases h
      rw [Int.toNat_of_nonneg (Int.ediv_nonneg hc1 hL.le)]
      exact (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hc2)).symm
    · cases h
  · rintro rfl
    rw [ite_eq_left ⟨mul_nonneg (Int.natCast_nonneg s) hL.le, Int.mul_emod_left _ _⟩,
      Int.mul_ediv_cancel _ hL.ne', Int.toNat_natCast]

/-- A skeleton proposes nothing at a time that starts no positive slot, and one `propose s` duty at
the start of slot `s > 0`. -/
theorem Skeleton.proposeAt_cases {n : Nat} (sk : Skeleton n) {Δ : Time} (hΔ : 0 < Δ) (t : Time) :
    (sk.proposeAt Δ t = [] ∧ ∀ s, 0 < s → t ≠ sk.grid.slotTime Δ s) ∨
      ∃ s, ∃ h : 0 < s, sk.proposeAt Δ t = [.propose s h] ∧ t = sk.grid.slotTime Δ s := by
  unfold Skeleton.proposeAt
  match hs : sk.grid.slotAt? Δ 0 t with
  | none =>
    left
    refine ⟨rfl, fun s hs' ht => ?_⟩
    have := (slotAt?_zero_iff sk.grid hΔ t s).2 ht
    rw [hs] at this
    cases this
  | some s =>
    by_cases h : 0 < s
    · right
      exact ⟨s, h, by simp [h], (slotAt?_zero_iff sk.grid hΔ t s).1 hs⟩
    · left
      refine ⟨by simp [h], fun s' hs' ht => ?_⟩
      have := (slotAt?_zero_iff sk.grid hΔ t s').2 ht
      rw [hs] at this
      cases this
      exact h hs'

/-- Slot `s` starts no earlier than time `s`: slot lengths are at least one. -/
theorem le_slotTime (P : Params) : ∀ s : Nat, (s : Time) ≤ P.slotTime s
  | 0 => by rw [P.slotTime_zero]; rfl
  | s + 1 => by
    have h1 : ((s : Nat) : Int) ≤ (P.slotTime s : Int) := le_slotTime P s
    have h2 : (P.slotTime s : Int) < (P.slotTime (s + 1) : Int) :=
      P.slotTime_strictMono (Nat.lt_add_one s)
    change (((s + 1 : Nat)) : Int) ≤ (P.slotTime (s + 1) : Int)
    push_cast
    exact Int.add_one_le_of_lt (lt_of_le_of_lt h1 h2)

/-- The slot of a slot's start is the slot. -/
theorem slotOf_slotTime (P : Params) (s : Nat) : P.slotOf (P.slotTime s) = s := by
  unfold Params.slotOf
  rw [Nat.findGreatest_eq_iff]
  refine ⟨?_, fun _ => le_rfl, fun n hn _ h => ?_⟩
  · have h : ((s : Nat) : Int) ≤ (P.slotTime s : Int) := le_slotTime P s
    exact (Int.le_toNat (le_trans (Int.natCast_nonneg s) h)).2 h
  · exact absurd (P.slotTime_strictMono hn) (not_lt.2 h)

omit [DecidableEq V] in
/-- The setup's slot start is the skeleton grid's slot start. -/
theorem slotTime_eq (s : Nat) :
    (S.params (pubOf E) hn).toParams.slotTime s =
      (skeleton (Fintype.card V) S.proposer).grid.slotTime E.Δ s := by
  simp only [Setup.params, skeleton, TimeGrid.slotTime, TimeGrid.slotLen]
  push_cast
  ring

omit [DecidableEq V] in
/-- At the start of slot `s > 0`, a key proposes exactly when it is the slot's proposer. -/
theorem proposes_iff (self : Fin (Fintype.card V)) (s : Nat) (hs : 0 < s) :
    Proposes (P := (S.params (pubOf E) hn).toParams) self
        ((S.params (pubOf E) hn).toParams.slotTime s) ↔
      (S.params (pubOf E) hn).toParams.proposer s = self := by
  unfold Proposes
  rw [slotOf_slotTime]
  exact ⟨fun h => h.2.2, fun h => ⟨hs, rfl, h⟩⟩

omit [DecidableEq V] in
/-- A key proposes at no time that starts no positive slot. -/
theorem not_proposes (self : Fin (Fintype.card V)) (t : Time)
    (h : ∀ s, 0 < s → t ≠ (S.params (pubOf E) hn).toParams.slotTime s) :
    ¬ Proposes (P := (S.params (pubOf E) hn).toParams) self t :=
  fun hp => h _ hp.1 hp.2.1


/-! ## The selection of a valid run -/

omit [DecidableEq V] in
/-- The skeleton's proposer selection at slot `s` is the singleton of the setup's proposer. -/
theorem skeleton_proposerSel (s : Nat) :
    (family S (pubOf E)).skel.proposerSel s =
      .fixed {(S.params (pubOf E) hn).toParams.proposer s} := by
  change Model.SelSpec.fixed _ = _
  congr 1
  ext k
  constructor
  · intro hk
    exact Finset.mem_singleton.mpr (Fin.ext (Finset.mem_filter.mp hk).2)
  · intro hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, congrArg Fin.val (Finset.mem_singleton.mp hk)⟩

omit [DecidableEq V] in
/-- In an admitted run, the proposer role of slot `s` selects exactly the setup's proposer. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {(S.params (pubOf E) hn).toParams.proposer s} := by
  have h := hsel (.proposer s)
  change ((family S (pubOf E)).skel.proposerSel s).Admits _ at h
  rw [skeleton_proposerSel S hn s] at h
  exact h

/-! ## The proposal duty -/

omit [DecidableEq V] in
/-- The candidate of the engine's `propose` duty is the shape's proposal wrapped as a block item
with the node's mempool. -/
theorem act_propose_snd (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (s : Slot)
    (hs : 0 < s) :
    ((Model.protoOf (compiled (family S)) E).act nd.st (.propose s hs)).2 =
      (propose (shapeOf S hn nd) s).2.map
        (fun r => (.item ⟨r.1, s, encodeTxs nd.st.2, r.2.1⟩, r.2.2)) := by
  change Option.map _ ((family S (pubOf E)).propose nd.st.1 s).2 = _
  simp only [family, dite_eq_left hn]; rfl

omit [DecidableEq V] in
/-- The block the engine decodes from the proposal item is the node's `mkBlock` with the engine's
digests. -/
theorem blockOf_eq_mkBlock (k : Fin (Fintype.card V))
    (fg : Store (S.params (pubOf E) hn).toParams (Payload (Fintype.card V))) (t : Time)
    (x : Nat) (H : Blk (S.params (pubOf E) hn)) (p : Payload (Fintype.card V)) (s : Slot)
    (hslot : (S.params (pubOf E) hn).toParams.slotOf t = s) :
    blockOf (S.params (pubOf E) hn)
        (rho.hash ⟨parentRef (S.params (pubOf E) hn).genesisRoot (some H.root), s, x,
          encodeInfo (fg.proposalAttestations H) p⟩)
        ⟨parentRef (S.params (pubOf E) hn).genesisRoot (some H.root), s, x,
          encodeInfo (fg.proposalAttestations H) p⟩
        k (fg.proposalAttestations H) p =
      mkBlock (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (digestOf S rho) k fg t x
        H p := by
  subst hslot
  simp only [blockOf, mkBlock, digestOf, dgOf]
  rw [parentRoot_parentRef]
  rfl

omit [DecidableEq V] in
/-- **The proposal duty is the node's proposal step.** At the start of slot `s` of which the node is
the selected proposer, when the proposal carries only released objects, the engine's `propose` duty
step records the block the node's `tickStep .proposal` makes; otherwise both do nothing. -/
theorem dutyStep_propose_node (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {(S.params (pubOf E) hn).toParams.proposer s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (pubOf E) hn).toParams.slotTime s)
    (hrel : ∀ par info cs, (propose (shapeOf S hn nd) s).2 = some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure nd.seen) :
    (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).node =
      (tickStep (digestOf S rho) (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
        (encodeTxs nd.st.2) .proposal).1 := by
  have hact2 := act_propose_snd S hn nd s hs
  have hact1 := shapeOf_act_propose S hn nd.st s hs
  unfold Model.Run.dutyStep
  generalize (Model.protoOf (compiled (family S)) E).act nd.st (.propose s hs) = a at hact1 hact2
  have hP : Proposes (P := (S.params (pubOf E) hn).toParams) (rho.ownKey v)
        (shapeOf S hn nd).now ↔
      (S.params (pubOf E) hn).toParams.proposer s = (shapeOf S hn nd).self := by
    rw [hst, proposes_iff S hn _ s hs, hself]
  by_cases hp : (S.params (pubOf E) hn).toParams.proposer s = (shapeOf S hn nd).self
  · simp only [propose, hp, ite_true] at hact1 hact2 hrel
    simp only [tickStep, hP.2 hp, ite_true]
    rcases hr : (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with _ | ⟨d, p⟩
    · simp only [hr] at hact1 hact2
      rw [hact2]
      change (a.1.1 hn).node = _
      rw [hact1]
    · simp only [hr] at hact1 hact2 hrel
      rw [hact2]
      have hrole : (Model.protoOf (compiled (family S)) E).role (.propose s hs) = .proposer s := rfl
      simp only [Option.map, Model.Run.signedCandidate, hrole]
      have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
        rw [hsel]
        exact Finset.mem_singleton.2 (hp.trans hself).symm
      rw [ite_eq_left hmem]
      unfold Model.releaseAll
      rw [ite_eq_left (Bool.and_eq_true_iff.2 ⟨?_, ?_⟩)]
      · change (recordOwn (a.1.1 hn) _ _).node = _
        rw [hact1]
        simp only [recordOwn, decodeInfo_encodeInfo]
        erw [rootOf_digests_item]
        simp only [apply_node]
        have hb := blockOf_eq_mkBlock S rho hn (rho.ownKey v)
          (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg (shapeOf S hn nd).now
          (encodeTxs nd.st.2) d.head p s hslot
        erw [hb]
        simp only [hself]
        rfl
      · unfold Model.releasable
        exact List.all_eq_true.2 fun o ho => decide_eq_true (hrel _ _ _ rfl o ho)
      · exact protects_of_not_att S _ _ _ (fun k w h => by
          cases h)
  · simp only [propose, hp, ite_false] at hact1 hact2
    simp only [tickStep, hP.not.2 hp, ite_false]
    rw [hact2]
    change (a.1.1 hn).node = _
    rw [hact1]


/-! ## The node state across a tick -/

/-- Recording an unsigned own object keeps the node state. -/
theorem recordOwn_none_node (st : State sp ro) (m : Model.Msg (Header Info) Body)
    (cs : List (Wire sp.n)) hs : (recordOwn st (.mk .none m cs) hs).node = st.node := by
  cases m with
  | data b => cases b <;> rfl
  | item h => rfl

/-- A poll step with no FG update due keeps the node state. -/
theorem poll_node_of_fgDue (st : State sp ro) (t : Time) (h : st.fgDue = false) :
    (poll st t).1.node = st.node := by
  unfold poll
  simp only [h, Bool.false_eq_true, ite_false]
  split <;> rfl

/-- A poll step with the FG update due runs it on the node state. -/
theorem poll_node_of_fgDue_true (st : State sp ro) (t : Time) (h : st.fgDue = true) :
    (poll st t).1.node = (fgUpdate st).node := by
  unfold poll
  simp only [h, ite_true]
  split <;> rfl

/-- The node's tick at a public time runs the AC's tick on the node state. -/
theorem nodeTick_node_public (st : State sp ro) (h : sp.toParams.IsPublic st.now) :
    (nodeTick st).node = (Node.acCall st.self st.node st.now .tick).1 := by
  unfold nodeTick
  rw [ite_eq_left h]
  rfl

/-- The node's tick at a non-public time keeps the node state. -/
theorem nodeTick_node_other (st : State sp ro) (h : ¬ sp.toParams.IsPublic st.now) :
    (nodeTick st).node = st.node := by
  unfold nodeTick
  rw [ite_eq_right h]

/-- The shape's FG update is the node's `tickStep .fgUpdate`, for any digests and mempool: neither
reads them. -/
theorem fgUpdate_node (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat)
    (st : State sp ro) :
    (fgUpdate st).node = (Node.tickStep dg st.self st.node st.now x .fgUpdate).1 := by
  unfold fgUpdate Node.tickStep
  simp only
  rcases h : (Node.acToFG st.node st.now).2.2.1 with _ | C
  · rfl
  · unfold Node.attest
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩ <;> simp only [h']

omit [DecidableEq V] in
/-- `fgUpdate_node` with the engine's digests. -/
theorem fgUpdate_node_digestOf (st : State (S.params (pubOf E) hn) (S.ro _)) (x : Nat) :
    (fgUpdate st).node =
      (Node.tickStep (digestOf S rho) st.self st.node st.now x .fgUpdate).1 :=
  fgUpdate_node (digestOf S rho) x st

omit [DecidableEq V] in
/-- A duty keeps the mempool. -/
theorem act_mempool (st : (Model.protoOf (compiled (family S)) E).State)
    (d : (Model.protoOf (compiled (family S)) E).Duty) :
    ((Model.protoOf (compiled (family S)) E).act st d).1.2 = st.2 := by
  cases d <;> rfl

omit [DecidableEq V] in
/-- `releaseAll` keeps the mempool. -/
theorem releaseAll_mempool (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (cs : List (Model.protoOf (compiled (family S)) E).Object),
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd cs).1.st.2 = nd.st.2
  | _, [] => rfl
  | nd, c :: cs => by
    unfold Model.releaseAll
    split
    · exact releaseAll_mempool k _ cs
    · exact releaseAll_mempool k nd cs

omit [DecidableEq V] in
/-- Running duties keeps the mempool. -/
theorem runDuties_mempool (v : V) :
    ∀ (ds : List (Model.protoOf (compiled (family S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (family S)) E)),
      (rho.runDuties v nd ds).1.st.2 = nd.st.2
  | [], _ => rfl
  | d :: ds, nd => by
    rw [runDuties_fst_cons, runDuties_mempool v ds]
    unfold Model.Run.dutyStep
    rw [releaseAll_mempool]
    exact act_mempool S _ d

omit [DecidableEq V] in
/-- `releaseAll` of candidates whose `recordOwn` keeps the node state keeps the node state. -/
theorem releaseAll_node_eq (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (family S)) E))
      (cs : List (Model.protoOf (compiled (family S)) E).Object),
      (∀ c ∈ cs, ∀ (st : State (S.params (pubOf E) hn) (S.ro _)) hs,
        (recordOwn st c hs).node = st.node) →
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd
        cs).1).node = (shapeOf S hn nd).node
  | _, [], _ => rfl
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · rw [releaseAll_node_eq k _ cs (fun c hc => h c (List.mem_cons_of_mem _ hc))]
      exact h c (List.mem_cons_self ..) _ _
    · exact releaseAll_node_eq k nd cs (fun c hc => h c (List.mem_cons_of_mem _ hc))

omit [DecidableEq V] in
/-- The gossip keeps the node state: its candidates are unsigned. -/
theorem gossip_node_eq (k : Fin (Fintype.card V))
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (t : Time) :
    (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (family S)) E) nd.st t)).1).node =
      (shapeOf S hn nd).node := by
  apply releaseAll_node_eq
  intro c hc st hs
  obtain ⟨mc, _, rfl⟩ := List.mem_map.1 hc
  exact recordOwn_none_node st _ _ hs

omit [DecidableEq V] in
/-- The tick of an awake node: the duties from the clocked node, then the gossip. -/
theorem tick_of_awake (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (hw : E.awake v t = true) :
    (rho.tick nd v t).1 =
      (Model.releaseAll (Model.protoOf (compiled (family S)) E) rho.hash (rho.ownKey v)
        (rho.runDuties v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩
          ((Model.protoOf (compiled (family S)) E).duties t)).1
        (Model.gossipCandidates (Model.protoOf (compiled (family S)) E)
          (rho.runDuties v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
            (Model.mempool rho.inbox v t), nd.seen⟩
            ((Model.protoOf (compiled (family S)) E).duties t)).1.st t)).1 := by
  unfold Model.Run.tick
  simp only [hw, ite_true]

/-- The node of validator `v` at its proposal duty of a tick at `t` from `nd`: after the clock,
the two leading poll steps and the node's tick. -/
noncomputable def atProposal (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) : Model.Node (Model.protoOf (compiled (family S)) E) :=
  (rho.runDuties v ⟨(Model.protoOf (compiled (family S)) E).clock nd.st t
    (Model.mempool rho.inbox v t), nd.seen⟩
    ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
      List (Model.protoOf (compiled (family S)) E).Duty)).1

omit [DecidableEq V] in
/-- The shape at the proposal duty: `nodeTick` of two poll steps of the clocked state. -/
theorem atProposal_shape (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) :
    shapeOf S hn (atProposal S rho v nd t) =
      nodeTick (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1 := by
  change shapeOf S hn (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v _ (.poll t.toNat)).1
    (.poll t.toNat)).1 (.pollPropose t.toNat)).1 = _
  rw [dutyStep_pollPropose, dutyStep_poll, dutyStep_poll]
  rfl

omit [DecidableEq V] in
/-- The key at the proposal duty is the key before the tick. -/
theorem atProposal_self (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) : (shapeOf S hn (atProposal S rho v nd t)).self = (nd.st.1 hn).self := by
  rw [atProposal_shape, nodeTick_self, poll_self, poll_self]

omit [DecidableEq V] in
/-- The clock at the proposal duty is the tick time. -/
theorem atProposal_now (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) : (shapeOf S hn (atProposal S rho v nd t)).now = t := by
  rw [atProposal_shape, nodeTick_now, poll_now, poll_now]

omit [DecidableEq V] in
/-- At a public time the FG update is due at the proposal duty: the node's tick set it. -/
theorem atProposal_fgDue (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (shapeOf S hn (atProposal S rho v nd t)).fgDue = true := by
  rw [atProposal_shape]
  unfold nodeTick
  rw [ite_eq_left (by rw [poll_now, poll_now]; exact hp)]

omit [DecidableEq V] in
/-- The mempool at the proposal duty is the tick's mempool. -/
theorem atProposal_mempool (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) : (atProposal S rho v nd t).st.2 = Model.mempool rho.inbox v t := by
  unfold atProposal
  rw [runDuties_mempool]
  rfl

omit [DecidableEq V] in
/-- With no FG update due before the tick, the node state at the proposal duty is `nodeTick` of the
clocked state. -/
theorem atProposal_node (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (hf : (nd.st.1 hn).fgDue = false) :
    (shapeOf S hn (atProposal S rho v nd t)).node =
      (nodeTick { nd.st.1 hn with now := t }).node := by
  rw [atProposal_shape]
  have h1 : (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1.node =
      (nd.st.1 hn).node := by
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _),
      poll_node_of_fgDue { nd.st.1 hn with now := t } _ hf]
  have h2 : (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1.self =
      (nd.st.1 hn).self := by rw [poll_self, poll_self]
  have h3 : (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1.now = t := by
    rw [poll_now, poll_now]
  unfold nodeTick
  rw [h3]
  by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
  · simp only [hp, ite_true, apply_node, h1, h2]
  · simp only [hp, ite_false, h1]

omit [DecidableEq V] in
/-- The node after the whole tick, in terms of the node at the proposal duty: the proposal if
due, a poll step, a poll step, the gossip. -/
theorem tick_node_eq (v : V) (nd : Model.Node (Model.protoOf (compiled (family S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true) :
    (shapeOf S hn (rho.tick nd v t).1).node =
      (poll (poll (shapeOf S hn (rho.runDuties v (atProposal S rho v nd t)
          ((skeleton (Fintype.card V) S.proposer).proposeAt E.Δ t)).1) t.toNat).1
        t.toNat).1.node := by
  rw [tick_of_awake S rho v nd t hw, gossip_node_eq, duties_eq S t ht, runDuties_fst_append]
  erw [runDuties_fst_cons, runDuties_fst_nil, dutyStep_poll]
  unfold dutiesInit
  erw [runDuties_fst_append, runDuties_fst_append, runDuties_fst_cons, runDuties_fst_nil,
    dutyStep_poll]
  rfl

/-- **`Simulates.tick`'s node step at a non-public time.** An engine tick at a non-public time
leaves the node state unchanged: no slot starts, so no proposal, and the FG update is not due. -/
theorem node_of_tick_other (hv : rho.ExecutionValid) (v : V) (_hv' : v ∈ rho.honest)
    (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node = (stateAt S rho hn v i).node := by
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw]
  rcases Skeleton.proposeAt_cases (skeleton (Fintype.card V) S.proposer) E.Δ_pos t with
    ⟨hnil, _⟩ | ⟨s, hs, _, hts⟩
  · rw [hnil]
    erw [runDuties_fst_nil]
    have hf : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).fgDue = false := by
      rw [atProposal_shape]
      unfold nodeTick
      rw [ite_eq_right (by rw [poll_now, poll_now]; exact hp)]
      exact poll_fgDue _ _
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _), poll_node_of_fgDue _ _ hf,
      atProposal_node S rho hn v _ t (fgDue_eq_false S rho hn v i), nodeTick_node_other _ hp]
    rfl
  · exfalso
    apply hp
    rw [hts, ← slotTime_eq S hn s]
    exact (S.params (pubOf E) hn).toParams.slotTime_public s

/-- The node's `onTick` is its three tick steps in order: the AC's tick, the proposal, the FG
update. -/
theorem onTick_node (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.onTick dg self st t x).1 =
      (Node.tickStep dg self (Node.tickStep dg self (Node.tickStep dg self st t x .acTick).1 t x
        .proposal).1 t x .fgUpdate).1 := rfl

/-- The AC-tick step is the AC's tick. -/
theorem tickStep_acTick (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.tickStep dg self st t x .acTick).1 = (Node.acCall self st t .tick).1 := rfl

/-- The proposal step of a key that does not propose at `t` keeps the node state. -/
theorem tickStep_proposal_not (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    (h : ¬ Proposes (P := sp.toParams) self t) :
    (Node.tickStep dg self st t x .proposal).1 = st := by
  unfold Node.tickStep
  simp only [h, ite_false]

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn` and `propose` is preserved by the
engine's `propose` duty step. -/
theorem dutyStep_propose_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (family S)) E)) (s : Slot) (hs : 0 < s)
    (h : Q (shapeOf S hn nd)) : Q (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) := by
  unfold Model.Run.dutyStep
  apply releaseAll_pres S rho hn Q hrec
  have := hprop _ s h
  rw [← shapeOf_act_propose S hn nd.st s hs] at this
  exact this

/-- **A proposal carries only released objects**, at the node the proposal duty runs on. -/
theorem proposal_releasable (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (par : ParentRef)
    (info : Info) (cs : List (Wire (Fintype.card V)))
    (hprop : (propose (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)) s).2 =
      some (par, info, cs)) :
    ∀ o ∈ cs, o ∈ Model.closure (atProposal S rho v (rho.stateBefore i v) t).seen := by
  sorry

/-- **`Simulates.tick`'s node step at a public time.** An engine tick of an honest node at a public
time runs the node's tick with the encoded mempool on the node state before it. -/
theorem node_of_tick_public (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node =
      (exec (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).1 := by
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw]
  have hPself : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).self =
      rho.ownKey v := by
    rw [atProposal_self]; exact self_eq_ownKey S rho hn v i
  have hPnow : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).now = t :=
    atProposal_now S rho hn v _ t
  have hPfg : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).fgDue = true :=
    atProposal_fgDue S rho hn v _ t hp
  have hPnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node =
      (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node t .tick).1 := by
    rw [atProposal_node S rho hn v _ t (fgDue_eq_false S rho hn v i),
      nodeTick_node_public _ (by exact hp)]
    exact congrArg (fun k => (Node.acCall k _ t _).1) (self_eq_ownKey S rho hn v i)
  have hPmem : (atProposal S rho v (rho.stateBefore i v) t).st.2 =
      Model.mempool rho.inbox v t := atProposal_mempool S rho v _ t
  change _ = (Node.onTick _ _ _ _ _).1
  erw [onTick_node (sp := S.params (pubOf E) hn) (digestOf S rho) (rho.ownKey v) _ t
    (encodeTxs (Model.mempool rho.inbox v t)),
    tickStep_acTick (sp := S.params (pubOf E) hn) (digestOf S rho) (rho.ownKey v) _ t
    (encodeTxs (Model.mempool rho.inbox v t))]
  rcases Skeleton.proposeAt_cases (skeleton (Fintype.card V) S.proposer) E.Δ_pos t with
    ⟨hnil, hno⟩ | ⟨s, hs, hone, hts⟩
  · rw [hnil]
    erw [runDuties_fst_nil]
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _), poll_node_of_fgDue_true _ _ hPfg,
      fgUpdate_node_digestOf S rho hn _ (encodeTxs (Model.mempool rho.inbox v t)),
      hPself, hPnow, hPnode]
    have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams) (rho.ownKey v) t :=
      not_proposes S hn _ t (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    erw [tickStep_proposal_not (sp := S.params (pubOf E) hn) (digestOf S rho) (rho.ownKey v) _ t
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
        (fun par info cs hprop => proposal_releasable S rho hn hv v hv' i t he s par info cs
          hprop)]
    erw [hPnode, hPnow, hPmem]

/-! ## The open release obligations -/

/-- **At most two bodies pending at a tick.** Between two ticks an honest node queues at most
its SA vote and its attestation, so two poll steps release everything queued. -/
theorem outbox_le_two (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t)) :
    (stateAt S rho hn v i).outbox.length ≤ 2 := by
  sorry

/-- After an awake honest node's tick at a public time nothing is pending: the tick's own bodies
were released by its last poll steps. -/
theorem outbox_empty_after_tick (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t)) (hw : E.awake v t = true)
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).outbox = [] := by
  sorry

/-- **`protects` never blocks an honest node.** An honest node's own attestation in its pool
passes the own-object guard against everything it has seen: an honest signer's attestations
never conflict (`non_framing`, Lemmas/Compose/Regimes). -/
theorem protects_own_att (hv : rho.ExecutionValid) (v : V) (hv' : v ∈ rho.honest) (i : Nat)
    (a : FG.Att (Fintype.card V)) (ha : a ∈ (stateAt S rho hn v i).node.fg.atts)
    (hself : a.val = rho.ownKey v) :
    Model.protects (Model.protoOf (compiled (family S)) E) (rho.ownKey v)
      (rho.stateBefore i v).seen (attObj a) = true := by
  sorry

end Engine

end Consensus.Goldilocks.Refinement

end
