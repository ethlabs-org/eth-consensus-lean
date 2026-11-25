module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace
public import ConsensusLean.Lemmas.Model.Objects
import ConsensusLean.Lemmas.Model.DutyFold
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeInventorySchedule

public section

/-! # Projecting engine prefixes into the canonical node trace -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)} {e : Encoding F E p hN hn A}
variable {rho : Model.Run (compiled F) E}

/-- The node state after the canonical handlers of the objects visited in one delivery. -/
noncomputable def deliveryPost (e : Encoding F E p hN hn A)
    (rho : Model.Run (compiled F) E) (v : V) (t : Time) (i : Nat)
    (o : (Model.protoOf (compiled F) E).Object) : NodeState A :=
  let st := stateAt e rho v i
  let hs := Model.digests rho.hash o
  let C := receiverCodec e rho v
  (delivered C e.adapter hs st (wireOf e o)).foldl
    (fun s w => ((canonEvent C hs w).map
      (fun ev => (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) s t ev).1)).getD s)
    (e.adapter.node st)

/-- The projected state after delivery is the fold over the visited objects. -/
theorem deliveryPost_eq (v : V) (t : Time) (i : Nat)
    (o : (Model.protoOf (compiled F) E).Object) : deliveryPost e rho v t i o =
    let st := stateAt e rho v i
    let hs := Model.digests rho.hash o
    let C := receiverCodec e rho v
    (delivered C e.adapter hs st (wireOf e o)).foldl
      (fun s w => ((canonEvent C hs w).map
        (fun ev => (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) s t ev).1)).getD s)
      (e.adapter.node st) := by rfl

omit [DecidableEq V] in
/-- A selected duty with one signed, ready candidate releases and records precisely that object.
For a proposal, the instance proves the singleton signing equation and both readiness guards. -/
theorem dutyStep_release_singleton (rho : Model.Run (compiled F) E) (v : V)
    (nd : Model.Node (Model.protoOf (compiled F) E)) (d : (Model.protoOf (compiled F) E).Duty)
    (o : (Model.protoOf (compiled F) E).Object)
    (hsel : rho.ownKey v ∈ rho.sel ((Model.protoOf (compiled F) E).role d))
    (hc : rho.signedCandidate v d ((Model.protoOf (compiled F) E).act nd.st d).2 = [o])
    (hcarried : Model.releasable nd.seen o = true)
    (hready : (Model.protoOf (compiled F) E).dependencies.ready (Model.closure nd.seen) o = true) :
    rho.dutyStep v nd d =
      (⟨(Model.protoOf (compiled F) E).recordOwn
          ((Model.protoOf (compiled F) E).act nd.st d).1 o (Model.digests rho.hash o),
        nd.seen ++ [o]⟩, [o]) := by
  rw [rho.dutyStep_eq, ite_eq_left hsel, hc]
  simp only [Model.releaseAll, hcarried, hready, Bool.and_self, ite_true]

/-- Project an intermediate engine node into the instance's shape state. -/
def envelope (e : Encoding F E p hN hn A) (nd : Model.Node (Model.protoOf (compiled F) E)) :
    e.State hn :=
  (cast (congrArg (fun s : ChainShape (Model.pubOf E) O.Id I => s.State) e.shape_eq)
    nd.st.1 : ∀ h, e.State h) hn

omit [DecidableEq V] in
/-- The projection is the same state cast used at an engine cut. -/
theorem envelope_eq (e : Encoding F E p hN hn A)
    (nd : Model.Node (Model.protoOf (compiled F) E)) : envelope e nd =
    (cast (congrArg (fun s : ChainShape (Model.pubOf E) O.Id I => s.State) e.shape_eq)
      nd.st.1 : ∀ h, e.State h) hn := by rfl

omit [DecidableEq V] in
/-- Transport a local duty to the actual compiled engine's duty type. -/
def engineDuty (e : Encoding F E p hN hn A) (d : ShapeDuty e.skel.Kind) :
    (Model.protoOf (compiled F) E).Duty :=
  cast (congrArg (fun s : ChainShape (Model.pubOf E) O.Id I => (compile s).Duty) e.shape_eq.symm) d

omit [DecidableEq V] in
/-- The duty cast is induced by the equality of the two shapes. -/
theorem engineDuty_eq (e : Encoding F E p hN hn A) (d : ShapeDuty e.skel.Kind) :
    engineDuty e d =
      cast (congrArg (fun s : ChainShape (Model.pubOf E) O.Id I => (compile s).Duty)
        e.shape_eq.symm) d := by rfl

omit [DecidableEq V] in
/-- The engine state just after the clock, before any tick duties. -/
def afterClock (rho : Model.Run (compiled F) E) (nd : Model.Node (Model.protoOf (compiled F) E))
    (v : V) (t : Time) : Model.Node (Model.protoOf (compiled F) E) :=
  ⟨(Model.protoOf (compiled F) E).clock nd.st t (Model.mempool rho.inbox v t), nd.seen⟩

omit [DecidableEq V] in
/-- Clocking preserves the engine's `seen` list and sets its cumulative mempool. -/
theorem afterClock_eq (rho : Model.Run (compiled F) E)
    (nd : Model.Node (Model.protoOf (compiled F) E)) (v : V) (t : Time) : afterClock rho nd v t =
    ⟨(Model.protoOf (compiled F) E).clock nd.st t (Model.mempool rho.inbox v t), nd.seen⟩ := by rfl

open Classical in
/-- Local operation laws and valid-run alignment for the encoded shape. `due` is an observer
used only in the proofs of these laws, never in the construction of the replay. -/
structure Encoding.Lawful (e : Encoding F E p hN hn A) (due : e.State hn → Bool) : Prop where
  init_due : ∀ k select io, due ((e.ops hn).init k select io) = false
  set_due : ∀ st b, due (e.adapter.setDue st b) = b
  clock_due : ∀ st t, due ((e.ops hn).clock st t) = due st
  process_due : ∀ st o hs, due ((e.ops hn).process st o hs) = due st
  restore_due : ∀ k st t, due ((e.ops hn).restore k st t) = false
  cut_due : ∀ (rho : Model.Run (compiled F) E) v i, due (stateAt e rho v i) = false
  tick_schedule : ∀ t, 0 ≤ t →
    (Model.protoOf (compiled F) E).duties t =
      (([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] : List (ShapeDuty e.skel.Kind)) ++
        e.skel.proposeAt t ++ ([.poll t.toNat, .poll t.toNat] : List (ShapeDuty e.skel.Kind))).map
          (engineDuty e)
  tick_prefix : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
      let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
        ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
      (if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
        e.adapter.node (envelope e pre) = (acCall (rho.ownKey v)
          (e.adapter.node (stateAt e rho v i)) t .tick).1 ∧
          due (envelope e pre) = e.adapter.sign (rho.ownKey v) t
      else e.adapter.node (envelope e pre) = e.adapter.node (stateAt e rho v i) ∧
        due (envelope e pre) = false)
  tick_proposal : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
      let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
        ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
      let post := (rho.runDuties v pre ((e.skel.proposeAt t).map (engineDuty e))).1
      due (envelope e post) = due (envelope e pre) ∧
      e.adapter.node (envelope e post) = (Node.tickStep (runProposer rho hn) (digestOf e rho)
        (rho.ownKey v) (e.adapter.node (envelope e pre)) t
        (encodeTxs (Model.mempool rho.inbox v t)) .proposal).1 ∧
      (¬ (paramsAtCount p (Fintype.card V) hN hn).IsPublic t →
        e.adapter.node (envelope e post) = e.adapter.node (envelope e pre))
  /-- The node after an engine tick is the node's tick (`postTick`) followed by the own
  `on_attestation` of every attestation the engine admitted to the pool during the event, in
  order (`admitsAt`). -/
  tick_admits : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
      e.adapter.node (stateAt e rho v (i + 1)) =
        (admitsAt e rho v i).foldl
          (fun n a => (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) n t
            (.attestation a)).1)
          (postTick e rho e.adapter.sign v i t)
  /-- Every attestation the engine admits to a node's pool during its tick is the node's own. -/
  admits_own : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
      ∀ a ∈ admitsAt e rho v i, a.val = rho.ownKey v
  gossip_node : ∀ (rho : Model.Run (compiled F) E) v nd t,
    e.adapter.node (envelope e (Model.releaseAll (Model.protoOf (compiled F) E) rho.hash
      (rho.ownKey v) nd (Model.gossipCandidates (Model.protoOf (compiled F) E) nd.st t)).1) =
      e.adapter.node (envelope e nd)
  delivery_process : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v o t}, rho.events[i]? = some (.deliver v o t) →
      e.adapter.node ((e.ops hn).process (stateAt e rho v i) (wireOf e o)
        (Model.digests rho.hash o)) = deliveryPost e rho v t i o
  delivery_publish : ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v o t}, rho.events[i]? = some (.deliver v o t) →
      due ((e.ops hn).process (stateAt e rho v i) (wireOf e o) (Model.digests rho.hash o)) = false →
      e.adapter.node (stateAt e rho v (i + 1)) =
        e.adapter.node ((e.ops hn).process (stateAt e rho v i) (wireOf e o)
          (Model.digests rho.hash o))
  restore_node : ∀ k st t,
    e.adapter.node ((e.ops hn).restore k st t) = (Node.restart k (e.adapter.node st) t).1

omit [DecidableEq V] in
private theorem cast_init {s s' : ChainShape (Model.pubOf E) O.Id I} (h : s = s')
    (k : Fin (Fintype.card V)) (select : (compile s).Role → Bool)
    (io : Model.VoteIO s.Token (compile s).Role s.VoteData (Fintype.card V)) :
    cast (congrArg (fun q => q.State) h) (s.init k select io) =
      s'.init k (fun r => select (cast (congrArg (fun q => (compile q).Role) h.symm) r))
        (cast (congrArg (fun q => Model.VoteIO q.Token (compile q).Role q.VoteData
          (Fintype.card V)) h) io) := by
  cases h
  rfl

private theorem stateAt_zero (v : V) :
    e.adapter.node (stateAt e rho v 0) = initial e rho (rho.ownKey v) := by
  rw [stateAt_eq, initial_eq]
  have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
  simp only [Model.Run.stateBefore, List.take_zero, List.foldl_nil, Model.Run.initWorld,
    engineRole_eq, voteIOAt_eq, hk]
  change e.adapter.node ((cast (congrArg (fun q : ChainShape (Model.pubOf E) O.Id I => q.State)
    e.shape_eq)
    ((F (Model.pubOf E)).init (rho.ownKey v) _ (rho.voteIO v))) hn) = _
  exact congrArg (fun st : ∀ h, e.State h => e.adapter.node (st hn))
    (cast_init e.shape_eq (rho.ownKey v) (fun r => decide (rho.ownKey v ∈ rho.sel r))
      (rho.voteIO v))

omit [DecidableEq V] in
private theorem cast_restore {s s' : ChainShape (Model.pubOf E) O.Id I} (h : s = s')
    (k : Fin (Fintype.card V)) (st : s.State) (t : Time) :
    cast (congrArg (fun q => q.State) h) (s.restore k (s.durable st) t) =
      s'.restore k (s'.durable (cast (congrArg (fun q => q.State) h) st)) t := by
  cases h
  rfl

/-- A restart restores the node's state. Kept for a downstream consumer. -/
theorem stateAt_restart {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    stateAt e rho v (i + 1) = (e.ops hn).restore (rho.ownKey v) (stateAt e rho v i) t := by
  rw [stateAt_eq, stateAt_eq, rho.stateBefore_succ he]
  simp only [Model.Run.step, Function.update_self]
  change (cast (congrArg (fun q : ChainShape (Model.pubOf E) O.Id I => q.State) e.shape_eq)
    ((F (Model.pubOf E)).restore (rho.ownKey v)
      ((F (Model.pubOf E)).durable (rho.stateBefore i v).st.1) t)) hn = _
  rw [cast_restore e.shape_eq]
  rfl

section Replay

variable {Q : Params} {N : NodeAC Q}

private def replay (y : Fin Q.n) (s : NodeState N) (rs : List (CutRec N)) : NodeState N :=
  rs.foldl (fun acc r => if r.node = y then r.post else acc) s

private theorem replay_append (y : Fin Q.n) (s : NodeState N) (xs ys : List (CutRec N)) :
    replay y s (xs ++ ys) = replay y (replay y s xs) ys := List.foldl_append ..

private theorem replay_group (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y z : Fin Q.n) (s st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N)
    (h : y = z → s = st) :
    replay y s (groupRecs pr dg z st t id ev) =
      if z = y then (exec pr dg z st t ev).1 else s := by
  rw [groupRecs_eq]
  dsimp only
  rw [← Node.foldl_cutPost_exec]
  generalize (exec pr dg z st t ev).2 = cs
  suffices aux : ∀ (cs : List (Cut N)) (s st : NodeState N) (j : Nat),
      (z = y → s = st) →
      replay y s ((cs.zip (cutPosts z t cs st)).mapIdx
        (fun k cp => ⟨z, t, id, k + j, cp.1, cp.2⟩)) =
        if z = y then cs.foldl (cutPost z t) st else s by
    exact aux cs s st 0 fun hzy => h hzy.symm
  intro cs
  induction cs with
  | nil => intro s st j hs; by_cases hz : z = y <;> simp [replay, hz, hs]
  | cons c cs ih =>
    intro s st j hs
    rw [cutPosts_cons]
    simp only [List.zip_cons_cons, List.mapIdx_cons, Nat.succ_add]
    change replay y (if z = y then cutPost z t st c else s) _ = _
    rw [show (fun (k : Nat) (cp : Cut N × NodeState N) =>
        (⟨z, t, id, k + j + 1, cp.1, cp.2⟩ : CutRec N)) =
        (fun k cp => ⟨z, t, id, k + (j + 1), cp.1, cp.2⟩) by
      simp only [Nat.add_assoc]]
    rw [ih _ _ _ (fun hz => ite_eq_left hz)]
    split <;> simp_all

omit [Countable I] in
private theorem replay_deliver {K B : Type} (C : WireCodec N K I B)
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (hs : List (Header I × Nat)) (y z : Fin Q.n) (t : Time) (i : Nat)
    (os : List (ShapeObj Q.n K I B)) (s st : NodeState N) (sub : Nat) (h : y = z → s = st) :
    replay y s (deliverRecs C pr dg hs z t i os st sub) =
      if z = y then os.foldl (fun a o => ((canonEvent C hs o).map
        (fun ev => (exec pr dg z a t ev).1)).getD a) st else s := by
  induction os generalizing s st sub with
  | nil =>
    rw [deliverRecs_nil]
    by_cases hz : z = y <;> simp [replay, hz, h]
  | cons o os ih =>
    rw [deliverRecs_cons, List.foldl_cons]
    cases he : canonEvent C hs o with
    | none => simpa only [he, Option.map_none, Option.getD_none] using ih s st (sub + 1) h
    | some ev =>
      simp only [Option.map_some, Option.getD_some, replay_append,
        replay_group _ _ _ _ _ _ _ _ _ h]
      rw [ih _ _ _ (fun hz => ite_eq_left hz.symm)]
      split <;> simp_all

private theorem replay_admit (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y z : Fin Q.n) (t : Time) (i : Nat) (as : List (FG.Att Q.n)) (s st : NodeState N)
    (sub : Nat) (h : y = z → s = st) :
    replay y s (admitRecs pr dg z t i as st sub) =
      if z = y then as.foldl (fun n a => (exec pr dg z n t (.attestation a)).1) st else s := by
  induction as generalizing s st sub with
  | nil =>
    rw [admitRecs_nil]
    by_cases hz : z = y <;> simp [replay, hz, h]
  | cons a as ih =>
    rw [admitRecs_cons, List.foldl_cons, replay_append, replay_group _ _ _ _ _ _ _ _ _ h]
    rw [ih _ _ _ (fun hz => ite_eq_left hz.symm)]
    split <;> simp_all

end Replay

private theorem replay_prefix (v : V) (i : Nat) (hi : i ≤ rho.events.length) :
    (simTrace e rho).state (rho.ownKey v) (cutMap e rho i) =
      replay (rho.ownKey v) (initial e rho (rho.ownKey v))
        ((List.range i).flatMap (eventCuts e rho)) := by
  classical
  have hmap : ∀ j, ((List.range j).flatMap (eventCuts e rho)).length = cutMap e rho j := by
    intro j
    induction j with
    | zero => rw [cutMap_zero]; rfl
    | succ j ih => rw [List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.length_append, ih, cutMap_succ]
  have hp : ((List.range i).flatMap (eventCuts e rho)) <+: allCuts e rho := by
    rw [allCuts_eq]
    have ht := List.take_prefix i (List.range rho.events.length)
    rw [List.take_range, min_eq_left hi] at ht
    exact ht.flatMap _
  rw [← hmap]
  generalize (List.range i).flatMap (eventCuts e rho) = rs at hp ⊢
  clear hmap hi i
  induction rs using List.reverseRecOn with
  | nil => rw [show ([] : List (CutRec A)).length = 0 from rfl, Trace.state.eq_1,
      simTrace_init_eq, ← initial_eq]; rfl
  | append_singleton rs r ih =>
    have hr : (allCuts e rho)[rs.length]? = some r := by
      obtain ⟨bs, hb⟩ := hp
      rw [← hb, List.append_assoc, List.getElem?_append_right (by omega)]
      simp
    rw [List.length_append, List.length_singleton, Trace.state.eq_2, simTrace_node,
      simTrace_label, simTrace_post, hr,
      replay_append, ih ((List.prefix_append ..).trans hp)]
    by_cases h : r.node = rho.ownKey v <;> simp [replay, h]

/-- Another node's event leaves this node's state unchanged. Kept for a downstream consumer. -/
theorem stateAt_other (v : V) {j : Nat}
    {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (he : rho.events[j]? = some ev) (hne : ev.node ≠ v) :
    stateAt e rho v (j + 1) = stateAt e rho v j := by
  rw [stateAt_eq, stateAt_eq, rho.stateBefore_succ he]
  cases ev <;> simp only [Model.Event.node] at hne <;>
    simp only [Model.Run.step, Function.update_of_ne (Ne.symm hne)]

private theorem keyLe_between {V' O' : Type} {x y z : Model.Event V' O'} (h1 : x.keyLe y)
    (h2 : y.keyLe z) (ht : x.time = z.time) (hp : x.phase = z.phase) :
    y.time = x.time ∧ y.phase = x.phase := by
  have a1 : @LT.lt Int _ x.time y.time ∨ (@Eq Int x.time y.time ∧ x.phase ≤ y.phase) := h1
  have a2 : @LT.lt Int _ y.time z.time ∨ (@Eq Int y.time z.time ∧ y.phase ≤ z.phase) := h2
  have a3 : @Eq Int x.time z.time := ht
  have : @Eq Int y.time x.time ∧ y.phase = x.phase := by omega
  exact this

/-- An engine event between two ticks at the same time is a tick at that time. -/
theorem tick_between (hv : rho.ExecutionValid) {j i k : Nat} {a b : V} {t : Time}
    {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (hj : rho.events[j]? = some (.tick a t)) (hk : rho.events[k]? = some (.tick b t))
    (hji : j ≤ i) (hik : i ≤ k) (hi : rho.events[i]? = some ev) : ∃ c, ev = .tick c t := by
  rcases Nat.eq_or_lt_of_le hji with rfl | hji
  · exact ⟨a, Option.some.inj (hi.symm.trans hj)⟩
  rcases Nat.eq_or_lt_of_le hik with rfl | hik
  · exact ⟨b, Option.some.inj (hi.symm.trans hk)⟩
  obtain ⟨ht, hp⟩ := keyLe_between (keyLe_of_lt rho hv hj hi hji) (keyLe_of_lt rho hv hi hk hik)
    rfl rfl
  cases ev with
  | tick c t' =>
    simp only [Model.Event.time] at ht
    exact ⟨c, by rw [ht]⟩
  | deliver c o t' => simp [Model.Event.phase] at hp
  | restart c t' => simp [Model.Event.phase] at hp

open Classical in
/-- Every bounded engine prefix agrees with its replay, including at cuts after compromise:
validity constrains the actual events, not the observing validator at the end of the prefix. -/
theorem stateAgreement_all {due : e.State hn → Bool} (laws : e.Lawful due)
    (hv : rho.ExecutionValid) (v : V) (i : Nat) (hi : i ≤ rho.events.length) :
    e.adapter.node (stateAt e rho v i) =
      (simTrace e rho).state (rho.ownKey v) (cutMap e rho i) := by
  rw [replay_prefix v i hi]
  induction i with
  | zero => exact stateAt_zero v
  | succ j ih =>
    have hj : j < rho.events.length := by omega
    have he : rho.events[j]? = some rho.events[j] := List.getElem?_eq_getElem hj
    have hp := ih (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, replay_append, ← hp]
    cases hev : rho.events[j] with
    | tick w t =>
      rw [hev] at he
      rw [eventCuts_tick e rho j w t he, replay_append]
      by_cases heq : w = v
      · subst w
        have hG : replay (rho.ownKey v) (e.adapter.node (stateAt e rho v j))
            (if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
              groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
                (e.adapter.node (stateAt e rho v j)) t (Nat.pair j 0)
                (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t))
            else []) = postTick e rho e.adapter.sign v j t := by
          rw [postTick_eq]
          split
          · rw [replay_group _ _ _ _ _ _ _ _ _ (fun _ => rfl), ite_eq_left rfl]
          · rfl
        rw [hG, replay_admit _ _ _ _ _ _ _ _ _ _ (fun _ => rfl), ite_eq_left rfl,
          laws.tick_admits rho hv he]
      · have hk : rho.ownKey w ≠ rho.ownKey v := fun h => heq (rho.key.symm.injective h)
        rw [stateAt_other v he heq, replay_admit _ _ _ _ _ _ _ _ _ _ (fun h => (hk h.symm).elim),
          ite_eq_right hk]
        split
        · rw [replay_group _ _ _ _ _ _ _ _ _ (fun h => (hk h.symm).elim), ite_eq_right hk]
        · rfl
    | restart w t =>
      rw [hev] at he
      rw [eventCuts_restart e rho j w t he]
      by_cases heq : w = v
      · subst w
        rw [replay_group _ _ _ _ _ _ _ _ _ (fun _ => rfl), ite_eq_left rfl]
        rw [stateAt_restart he, laws.restore_node]
        rfl
      · have hk : rho.ownKey w ≠ rho.ownKey v := fun h => heq (rho.key.symm.injective h)
        rw [stateAt_other v he heq,
          replay_group _ _ _ _ _ _ _ _ _ (fun h => (hk h.symm).elim), ite_eq_right hk]
    | deliver w o t =>
      rw [hev] at he
      rw [eventCuts_deliver e rho j w o t he]
      dsimp only
      by_cases heq : w = v
      · subst w
        have hd := (laws.process_due (stateAt e rho v j) (wireOf e o)
          (Model.digests rho.hash o)).trans (laws.cut_due rho v j)
        rw [laws.delivery_publish rho hv he hd, laws.delivery_process rho hv he]
        rw [deliveryPost_eq]
        apply Eq.symm
        simpa only [ite_true] using
          replay_deliver (receiverCodec e rho v) (runProposer rho hn) (digestOf e rho)
            (Model.digests rho.hash o)
            (rho.ownKey v) (rho.ownKey v) t j _ _ _ 0 (fun _ => rfl)
      · have hk : rho.ownKey w ≠ rho.ownKey v := fun h => heq (rho.key.symm.injective h)
        rw [stateAt_other v he heq]
        apply Eq.symm
        simpa only [ite_eq_right hk] using
          replay_deliver (receiverCodec e rho w) (runProposer rho hn) (digestOf e rho)
            (Model.digests rho.hash o)
            (rho.ownKey v) (rho.ownKey w) t j _ _ _ 0 (fun h => (hk h.symm).elim)

/-- The valid engine prefix and its replay agree at the same bounded observation cut. -/
theorem stateAgreement {due : e.State hn → Bool} (laws : e.Lawful due)
    (hv : rho.ExecutionValid) : StateAgreement e rho := by
  rw [stateAgreement_iff]
  exact fun v i hi _ => stateAgreement_all laws hv v i hi

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
