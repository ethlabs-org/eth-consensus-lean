module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape

public section

/-! # Goldilocks Simulation: the engine's state and clock at each event

What a valid engine run (`ExecutionValid`) does to the shape's state at each event, before the
node state (`EngineSteps`): every duty step, tick and delivery preserves the shape (`tick_pres`,
`deliver_pres`); a poll step's own candidate is a data body that `recordOwn` ignores; `stateAt`
steps through the events (`stateAt_tick`, `stateAt_deliver`, `stateAt_restart`); the shape's clock
is the time of the node's last tick or restart (`now_eq_lastClock`, `lastClock_of_deliver`); and
the duties of a tick are `dutiesInit` and one more poll step (`duties_eq`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Valid selection includes every validator in the poll role. -/
theorem poll_selected (hv : rho.ExecutionValid) (v : V) :
    rho.ownKey v ∈ rho.sel .poll := by
  have h := hv.selValid .poll
  change rho.sel .poll = Finset.univ at h
  rw [h]
  exact Finset.mem_univ _

/-- The shape's state at `hn` inside an engine node. -/
abbrev shapeOf (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) :
    State (S.params (pubOf E) hn) (S.ro _) :=
  nd.st.1 hn

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn` is preserved by `releaseAll`: the
engine records each released object with `recordOwn` and drops the rest. -/
theorem releaseAll_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs)) (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (cs : List (Model.protoOf (compiled (goldilocks S)) E).Object), Q (shapeOf S hn nd) →
      Q (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
          cs).1)
  | _, [], h => h
  | nd, c :: cs, h => by
    unfold Model.releaseAll
    split
    · exact releaseAll_pres Q hrec k _ cs (hrec _ _ _ h)
    · exact releaseAll_pres Q hrec k nd cs h

omit [DecidableEq V] in
/-- The engine's `propose` duty is the shape's `propose`. -/
theorem shapeOf_act_propose (st : (Model.protoOf (compiled (goldilocks S)) E).State) (s : Slot)
    (h : 0 < s) :
    ((Model.protoOf (compiled (goldilocks S)) E).act st (.propose s h)).1.1 hn =
      (propose (st.1 hn) s).1 := by
  change ((goldilocks S (pubOf E)).propose st.1 s).1 hn = _
  simp only [goldilocks, dite_eq_left hn]
  rfl

omit [DecidableEq V] in
/-- The engine's `pollPropose` duty is the shape's `nodeTick`. -/
theorem shapeOf_act_pollPropose (st : (Model.protoOf (compiled (goldilocks S)) E).State) (t : Nat) :
    ((Model.protoOf (compiled (goldilocks S)) E).act st (.pollPropose t)).1.1 hn =
      nodeTick (st.1 hn) := by
  change ((goldilocks S (pubOf E)).pollPropose st.1 t).1 hn = _
  simp only [goldilocks, dite_eq_left hn]
  rfl

omit [DecidableEq V] in
/-- The engine's `poll` duty is the shape's `poll`. -/
theorem shapeOf_act_poll (st : (Model.protoOf (compiled (goldilocks S)) E).State) (t : Nat) :
    ((Model.protoOf (compiled (goldilocks S)) E).act st (.poll t)).1.1 hn =
      (poll (st.1 hn) t).1 := by
  change ((goldilocks S (pubOf E)).pollBatch st.1 t).1 hn = _
  simp only [goldilocks, dite_eq_left hn]
  rfl

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn`, `propose`, `nodeTick` and `poll` is
preserved by every duty step of the engine. -/
theorem dutyStep_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (htick : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (h : Q (shapeOf S hn nd)) :
    Q (shapeOf S hn (rho.dutyStep v nd d).1) := by
  unfold Model.Run.dutyStep
  split
  case isFalse => exact h
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
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty) (h : Q (shapeOf S hn nd)) :
    Q (shapeOf S hn (rho.runDuties v nd ds).1) := by
  unfold Model.Run.runDuties
  suffices ∀ acc : Model.Node (Model.protoOf (compiled (goldilocks S)) E) ×
      List (Model.protoOf (compiled (goldilocks S)) E).Object, Q (shapeOf S hn acc.1) →
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
theorem shapeOf_clock (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time)
    (xs : List Tx) :
    ((Model.protoOf (compiled (goldilocks S)) E).clock nd.st t xs).1 hn =
      { nd.st.1 hn with now := t } := rfl

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn`, `propose`, `nodeTick` and `poll` holds
after an engine tick if it holds for the clocked state before it: an asleep node's tick leaves the
state clocked, an awake node's runs the duties and the gossip. -/
theorem tick_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (htick : ∀ st, Q st → Q (nodeTick st))
    (hpoll : ∀ st t, Q st → Q (poll st t).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time)
    (h : Q { nd.st.1 hn with now := t }) :
    Q (shapeOf S hn (rho.tick nd v t).1) := by
  unfold Model.Run.tick
  simp only
  split
  · exact releaseAll_pres S rho hn Q hrec _ _ _
      (runDuties_pres S rho hn Q hrec hprop htick hpoll v _ _ h)
  · exact h

omit [DecidableEq V] in
/-- Running two lists of duties in sequence is running their concatenation. -/
theorem runDuties_fst_append (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (ds ds' : List (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    (rho.runDuties v nd (ds ++ ds')).1 = (rho.runDuties v (rho.runDuties v nd ds).1 ds').1 := by
  unfold Model.Run.runDuties
  rw [List.foldl_append]
  generalize ds.foldl _ _ = acc
  induction ds' generalizing acc with
  | nil => rfl
  | cons d ds' ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    conv_rhs => rw [ih]

/-! ## Duty steps and the node state -/

/-- Recording an own signed data body changes nothing: the shape keeps no record of it. -/
theorem recordOwn_data (st : State sp ro) (k : Fin sp.n) (r : ShapeRole Empty) (b : Body)
    (cs : List (Wire sp.n)) hs : recordOwn st (.mk (.signed k r) (.data b) cs) hs = st := by
  cases r <;> rfl

omit [DecidableEq V] in
/-- `releaseAll` of candidates that `recordOwn` ignores leaves the shape's state unchanged. -/
theorem releaseAll_shape_eq (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (cs : List (Model.protoOf (compiled (goldilocks S)) E).Object),
      (∀ c ∈ cs, ∀ (st : State (S.params (pubOf E) hn) (S.ro _)) hs, recordOwn st c hs = st) →
      shapeOf S hn
          (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd cs).1 =
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
    (o : List (Body × List (Model.protoOf (compiled (goldilocks S)) E).Object)) :
    ∀ c ∈ rho.signedCandidate v (.poll t) (o.map fun bc => (.data bc.1, bc.2)),
      ∀ (st : State (S.params (pubOf E) hn) (S.ro _)) hs, recordOwn st c hs = st := by
  intro c hc st hs
  unfold Model.Run.signedCandidate at hc
  split at hc
  next hk =>
    obtain ⟨⟨m, cs⟩, hm, rfl⟩ := List.mem_map.mp hc
    obtain ⟨⟨b, bs⟩, _, he⟩ := List.mem_map.mp hm
    cases he
    exact recordOwn_data st _ _ _ _ hs
  next hk => simp at hc

omit [DecidableEq V] in
/-- The engine's poll duty step is the shape's `poll`: its released body is not recorded. -/
theorem dutyStep_poll (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    shapeOf S hn (rho.dutyStep v nd (.poll t)).1 = (poll (shapeOf S hn nd) t).1 := by
  unfold Model.Run.dutyStep
  simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t) = .poll from rfl,
    hsel, ↓reduceIte]
  refine (releaseAll_shape_eq S rho hn _ _ _ ?_).trans (shapeOf_act_poll S hn nd.st t)
  exact signedCandidate_poll_recordOwn S rho hn v t _

omit [DecidableEq V] in
/-- The engine's `pollPropose` duty step is the shape's `nodeTick`: it releases nothing. -/
theorem dutyStep_pollPropose (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Nat) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    shapeOf S hn (rho.dutyStep v nd (.pollPropose t)).1 = nodeTick (shapeOf S hn nd) := by
  unfold Model.Run.dutyStep
  simp only
      [show (Model.protoOf (compiled (goldilocks S)) E).role (.pollPropose t) = .poll from rfl,
    hsel, ↓reduceIte]
  have h2 : ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose t)).2 = [] := by
    change (Option.map _ ((goldilocks S (pubOf E)).pollPropose nd.st.1 t).2).toList = []
    simp only [goldilocks, dite_eq_left hn]; rfl
  change shapeOf S hn (Model.releaseAll _ _ _
    ⟨((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose t)).1, nd.seen⟩
    (rho.signedCandidate v (.pollPropose t)
      ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose t)).2)).1 = _
  rw [h2]
  simpa [Model.Run.signedCandidate, hsel, Model.releaseAll] using
    shapeOf_act_pollPropose S hn nd.st t

omit [DecidableEq V] in
/-- Running a duty then a list of duties. -/
theorem runDuties_fst_cons (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty)
    (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    (rho.runDuties v nd (d :: ds)).1 = (rho.runDuties v (rho.dutyStep v nd d).1 ds).1 :=
  runDuties_fst_append S rho v nd [d] ds

omit [DecidableEq V] in
/-- Running no duties is the identity. -/
theorem runDuties_fst_nil (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) :
    (rho.runDuties v nd []).1 = nd := rfl

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

omit [DecidableEq V] in
/-- The duties at a delivery at `t ≥ 0`: one poll step (`deliverOrder := [.poll]`). -/
theorem deliverDuties_eq (t : Time) (ht : 0 ≤ t) :
    (Model.protoOf (compiled (goldilocks S)) E).deliverDuties t = [.poll t.toNat] := by
  change (skeleton (pubOf E)).deliverDuties t = _
  simp [Skeleton.deliverDuties, Skeleton.stepAt, skeleton, ht]
  rfl

omit [DecidableEq V] in
/-- A delivery at a negative time has no duties. -/
theorem deliverDuties_eq_nil (t : Time) (ht : t < 0) :
    (Model.protoOf (compiled (goldilocks S)) E).deliverDuties t = [] := by
  change (skeleton (pubOf E)).deliverDuties t = _
  simp [Skeleton.deliverDuties, Skeleton.stepAt, skeleton, not_le.2 ht]
  rfl

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn` of the candidates is preserved by
`releaseAll` of them. -/
theorem releaseAll_pres_mem (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (cs : List (Model.protoOf (compiled (goldilocks S)) E).Object),
      (∀ c ∈ cs, ∀ st hs, Q st → Q (recordOwn st c hs)) → Q (shapeOf S hn nd) →
      Q (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
          cs).1)
  | _, [], _, h => h
  | nd, c :: cs, hrec, h => by
    unfold Model.releaseAll
    split
    · exact releaseAll_pres_mem Q k _ cs (fun c hc => hrec c (List.mem_cons_of_mem _ hc))
        (hrec c (List.mem_cons_self ..) _ _ h)
    · exact releaseAll_pres_mem Q k nd cs (fun c hc => hrec c (List.mem_cons_of_mem _ hc)) h

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `poll` and by `recordOwn` of unsigned objects
holds after an engine delivery if it holds for the processed state: the delivery runs one poll
step (at `t ≥ 0`) and the gossip, whose candidates are unsigned. -/
theorem deliver_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
    (hpoll : ∀ st t, Q st → Q (poll st t).1)
    (hrec : ∀ st m cs hs, Q st → Q (recordOwn st (.mk .none m cs) hs)) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (t : Time)
    (h : Q (process (nd.st.1 hn) o (Model.digests rho.hash o))) :
    Q (shapeOf S hn (rho.deliver nd v o t).1) := by
  unfold Model.Run.deliver
  simp only
  apply releaseAll_pres_mem S rho hn Q
  · intro c hc st hs hq
    obtain ⟨mc, _, rfl⟩ := List.mem_map.1 hc
    exact hrec st _ _ hs hq
  · rcases le_or_gt 0 t with ht | ht
    · rw [deliverDuties_eq S t ht]
      by_cases hsel : rho.ownKey v ∈ rho.sel .poll
      · erw [runDuties_fst_cons, runDuties_fst_nil, dutyStep_poll _ _ _ _ _ _ hsel]
        exact hpoll _ _ h
      · erw [runDuties_fst_cons, runDuties_fst_nil]
        simp only [Model.Run.dutyStep,
          show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t.toNat) = .poll from rfl,
          hsel, ↓reduceIte]
        exact h
    · rw [deliverDuties_eq_nil S t ht, runDuties_fst_nil]
      exact h

/-! ## `stateAt` across an event -/

/-- The shape's state before the first event is its initial state at the own key. -/
theorem stateAt_zero (v : V) :
    stateAt S rho hn v 0 = (goldilocksShape _ _).init (rho.ownKey v) := by
  rw [stateAt_eq]
  rfl

/-- The shape's state after event `i` is the engine's `step` on the state before it. -/
theorem stateAt_succ (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) :
    stateAt S rho hn v (i + 1) = (rho.step (rho.stateBefore i) e v).st.1 hn := by
  simp only [stateAt_eq, rho.stateBefore_succ he]

/-- Past the last event the shape's state is constant. -/
theorem stateAt_succ_none (v : V) {i : Nat} (he : rho.events[i]? = none) :
    stateAt S rho hn v (i + 1) = stateAt S rho hn v i := by
  have : rho.events.take (i + 1) = rho.events.take i := by
    have hl := List.getElem?_eq_none_iff.1 he
    rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
  simp only [stateAt_eq, Model.Run.stateBefore, this]

/-- An event of another node leaves the shape's state unchanged. -/
theorem state_of_other (v : V) (i : Nat)
    (e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object)
    (he : rho.events[i]? = some e) (hne : e.node ≠ v) :
    stateAt S rho hn v (i + 1) = stateAt S rho hn v i := by
  rw [stateAt_succ S rho hn v he]
  cases e <;> simp only [Model.Event.node] at hne <;>
    simp only [Model.Run.step, Function.update_of_ne (Ne.symm hne), stateAt_eq]

/-- The shape's state after a tick of `v` is the shape of the engine's `tick`. -/
theorem stateAt_tick (v : V) {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t)) :
    stateAt S rho hn v (i + 1) = shapeOf S hn (rho.tick (rho.stateBefore i v) v t).1 := by
  rw [stateAt_succ S rho hn v he]
  simp only [Model.Run.step, Function.update_self]

/-- The shape's state after a delivery to `v` is the shape of the engine's `deliver`: the shape's
`process` of the delivered object with the engine's digests, then the delivery's poll step and
gossip (`deliver_pres`). -/
theorem stateAt_deliver (v : V) {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) :
    stateAt S rho hn v (i + 1) = shapeOf S hn (rho.deliver (rho.stateBefore i v) v o t).1 := by
  rw [stateAt_succ S rho hn v he]
  simp only [Model.Run.step, Function.update_self]

/-- The shape's state after a restart of `v` is the shape's `restore` at the own key. -/
theorem stateAt_restart (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    stateAt S rho hn v (i + 1) = restore (rho.ownKey v) (stateAt S rho hn v i) t := by
  rw [stateAt_succ S rho hn v he]
  simp only [Model.Run.step, Function.update_self, stateAt_eq]
  rfl


/-! ## Invariants of every engine cut -/

/-- The shape's key at every cut is the node's own key. -/
theorem self_eq_ownKey (v : V) : ∀ i, (stateAt S rho hn v i).self = rho.ownKey v
  | 0 => by rw [stateAt_zero]; rfl
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
            (fun st t h => (poll_self st t).trans h) v' _ t
            (by simpa only [stateAt_eq] using self_eq_ownKey v' i)
        | deliver v' o t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_deliver S rho hn _ he]
          exact deliver_pres S rho hn (fun st => st.self = rho.ownKey v')
            (fun st t h => (poll_self st t).trans h)
            (fun st _ _ hs h => (recordOwn_self st _ hs).trans h) v' _ o t
            ((process_self _ _ _).trans (by simpa only [stateAt_eq] using self_eq_ownKey v' i))
        | restart v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_restart S rho hn _ he]; rfl
      · rw [state_of_other S rho hn v i e he hv]; exact self_eq_ownKey v i

/-- `lastClock` after a tick of `v` is the tick time. -/
theorem lastClock_succ_tick (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) : lastClock S rho v (i + 1) = t := by
  simp [lastClock_succ, he]

/-- `lastClock` after a restart of `v` is the restart time. -/
theorem lastClock_succ_restart (v : V) {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) : lastClock S rho v (i + 1) = t := by
  simp [lastClock_succ, he]

/-- `lastClock` is unchanged by a delivery. -/
theorem lastClock_succ_deliver (v : V) {i : Nat} {t : Time}
    {o : (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some (.deliver v o t)) :
    lastClock S rho v (i + 1) = lastClock S rho v i := by
  simp [lastClock_succ, he]

/-- `lastClock` is constant past the last event. -/
theorem lastClock_succ_none (v : V) {i : Nat} (he : rho.events[i]? = none) :
    lastClock S rho v (i + 1) = lastClock S rho v i := by
  simp [lastClock_succ, he]

/-- `lastClock` of `v` is unchanged by an event of another node. -/
theorem lastClock_succ_other (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) (hne : e.node ≠ v) :
    lastClock S rho v (i + 1) = lastClock S rho v i := by
  cases e <;> simp only [Model.Event.node] at hne <;> simp [lastClock_succ, he, hne]

/-- **`Simulates.now`.** The shape's clock before an engine cut is the time of the node's last tick
or restart before it. -/
theorem now_eq_lastClock (_hv : rho.ExecutionValid) (v : V) :
    ∀ i, (stateAt S rho hn v i).now = lastClock S rho v i
  | 0 => by rw [stateAt_zero, lastClock_zero]; rfl
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
          exact deliver_pres S rho hn (fun st => st.now = lastClock S rho v' i)
            (fun st t h => (poll_now st t).trans h)
            (fun st _ _ hs h => (recordOwn_now st _ hs).trans h) v' _ o t
            ((process_now _ _ _).trans (by simpa only [stateAt_eq] using now_eq_lastClock _hv v' i))
        | restart v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_restart S rho hn _ he, lastClock_succ_restart S rho _ he]; rfl
      · rw [state_of_other S rho hn v i e he hv, lastClock_succ_other S rho v he hv]
        exact now_eq_lastClock _hv v i

/-! ## The duties of a tick -/

/-- The duties of a tick at `t ≥ 0` but the last: two poll steps, the node's tick, the slot
proposal if due, one poll step. -/
abbrev dutiesInit (t : Time) : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
  [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++
    (skeleton (pubOf E)).proposeAt t ++ [.poll t.toNat]

omit [DecidableEq V] in
/-- The duties of a tick at `t ≥ 0`: `dutiesInit` and one more poll step. -/
theorem duties_eq (t : Time) (ht : 0 ≤ t) :
    (Model.protoOf (compiled (goldilocks S)) E).duties t = dutiesInit S t ++ [.poll t.toNat] := by
  change (skeleton (pubOf E)).duties t = _
  simp only [Skeleton.duties, Skeleton.stepAt, skeleton, ht, ite_true, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, dutiesInit]
  exact congrArg (fun l => ShapeDuty.poll t.toNat :: .poll t.toNat :: .pollPropose t.toNat :: l)
    (List.append_assoc ((skeleton (pubOf E)).proposeAt t)
      [ShapeDuty.poll t.toNat] [ShapeDuty.poll t.toNat]).symm

omit [DecidableEq V] in
/-- A tick at a negative time has no duties. -/
theorem duties_eq_nil (t : Time) (ht : t < 0) :
    (Model.protoOf (compiled (goldilocks S)) E).duties t = [] := by
  change (skeleton (pubOf E)).duties t = _
  simp [Skeleton.duties, Skeleton.stepAt, Skeleton.proposeAt, skeleton, TimeGrid.slotAt?,
    not_le.2 ht]
  rfl

/-- The FG update is never due at a cut: every tick ends with a poll step, which runs it. -/
theorem fgDue_eq_false (v : V) : ∀ i, (stateAt S rho hn v i).fgDue = false
  | 0 => by rw [stateAt_zero]; rfl
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
              by_cases hsel : rho.ownKey v' ∈ rho.sel .poll
              case neg =>
                have hpres : ∀ ds (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)),
                    (nd.st.1 hn).fgDue = false →
                    ((rho.runDuties v' nd ds).1.st.1 hn).fgDue = false := by
                  intro ds
                  induction ds with
                  | nil => intro nd hh; exact hh
                  | cons d ds ih =>
                    intro nd hh
                    rw [runDuties_fst_cons]
                    apply ih
                    cases d with
                    | act s k => exact k.elim
                    | propose s hs =>
                      unfold Model.Run.dutyStep
                      split
                      case isFalse => exact hh
                      apply releaseAll_pres S rho hn (fun st => st.fgDue = false)
                        (fun st o hs hh => (recordOwn_fgDue st o hs).trans hh)
                      change (((Model.protoOf (compiled (goldilocks S)) E).act nd.st
                        (.propose s hs)).1.1 hn).fgDue = false
                      rw [shapeOf_act_propose]
                      exact (propose_fgDue _ s).trans hh
                    | poll t =>
                      simp only [Model.Run.dutyStep,
                        show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t) =
                          .poll from rfl,
                        hsel, ↓reduceIte]
                      exact hh
                    | pollPropose t =>
                      simp only [Model.Run.dutyStep,
                        show (Model.protoOf (compiled (goldilocks S)) E).role (.pollPropose t) =
                          .poll from rfl,
                        hsel, ↓reduceIte]
                      exact hh
                simp only [Model.Run.dutyStep,
                  show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t.toNat) =
                    .poll from rfl,
                  hsel, ↓reduceIte]
                apply hpres
                change ((rho.stateBefore i v').st.1 hn).fgDue = false
                simpa only [stateAt_eq] using fgDue_eq_false v' i
              unfold Model.Run.dutyStep
              simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.poll t.toNat) =
                .poll from rfl, hsel, ↓reduceIte]
              apply releaseAll_pres S rho hn (fun st => st.fgDue = false)
                (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
              change (((Model.protoOf (compiled (goldilocks S)) E).act _
                (.poll t.toNat)).1.1 hn).fgDue = false
              rw [shapeOf_act_poll]
              exact poll_fgDue _ _
            · rw [duties_eq_nil S t ht]
              change ((rho.stateBefore i v').st.1 hn).fgDue = false
              simpa only [stateAt_eq] using fgDue_eq_false v' i
          · change ((rho.stateBefore i v').st.1 hn).fgDue = false
            simpa only [stateAt_eq] using fgDue_eq_false v' i
        | deliver v' o t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_deliver S rho hn _ he]
          exact deliver_pres S rho hn (fun st => st.fgDue = false)
            (fun st t _ => poll_fgDue st t)
            (fun st _ _ hs h => (recordOwn_fgDue st _ hs).trans h) v' _ o t
            ((process_fgDue _ _ _).trans (by simpa only [stateAt_eq] using fgDue_eq_false v' i))
        | restart v' t =>
          simp only [Model.Event.node] at hv; subst hv
          rw [stateAt_restart S rho hn _ he]; rfl
      · rw [state_of_other S rho hn v i e he hv]; exact fgDue_eq_false v i


/-! ## The clock at a delivery -/

/-- In a valid run the events are sorted by their key, so an earlier event's key is at most a later
one's. -/
theorem keyLe_of_lt (hv : rho.ExecutionValid) {j k : Nat}
    {e f : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
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
          simp [lastClock_succ, he, ih]
        | restart v' t' =>
          simp only [Model.Event.time] at ht; subst ht
          simp [lastClock_succ, he, ih]
        | deliver v' o t' => simp [lastClock_succ, he, ih]
    · rcases hj with hj | hj
      · exact lastClock_succ_tick S rho v hj
      · exact lastClock_succ_restart S rho v hj

/-- **The clock at a delivery.** A delivery to `v` at `t` in a valid run comes after a tick of `v`
at `t` (the node is awake and the key order puts ticks first), so the shape's clock at it is `t`. -/
theorem lastClock_of_deliver (hv : rho.ExecutionValid) (v : V) {i : Nat}
    {o : (Model.protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) : lastClock S rho v i = t := by
  have hmem := List.mem_of_getElem? he
  have hhon := hv.honest_only _ hmem
  have hw := hv.deliver_awake v o t hmem
  have hh := hv.in_horizon _ hmem
  simp only [Model.Event.node, Model.Event.time] at hhon hh
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (hv.tick_total v t hh.1 hh.2 hhon hw)
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

end Engine

end Consensus.Goldilocks.Simulation

end
