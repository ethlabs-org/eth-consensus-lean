module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeStateAgreement
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
import ConsensusLean.Lemmas.Model.DutyFold
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeInventorySchedule

public section

/-! # Local operation laws for the compiled node replay -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node
open Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable {e : Encoding F E p hN hn A} {due : e.State hn → Bool}

private theorem cast_clock {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : s.State) (t : Time) :
    cast (congrArg (fun x => x.State) h) (s.clock st t) =
      q.clock (cast (congrArg (fun x => x.State) h) st) t := by
  cases h
  rfl

/-- Clock the envelope with the engine's tick time. -/
theorem envelope_clock (rho : Model.Run (compiled F) E)
    (nd : Model.Node (Model.protoOf (compiled F) E)) (v : V) (t : Time) :
    envelope e (afterClock rho nd v t) = (e.ops hn).clock (envelope e nd) t := by
  rw [afterClock_eq, envelope_eq, envelope_eq]
  change (cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => s.State) e.shape_eq)
    ((F (pubOf E)).clock nd.st.1 t)) hn = _
  rw [cast_clock e.shape_eq]
  rfl

private theorem cast_recordOwn {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : s.State) (o : (compile s).Object) (hs : List (Header I × Nat)) :
    cast (congrArg (fun x => x.State) h) (s.recordOwn st o hs) =
      q.recordOwn (cast (congrArg (fun x => x.State) h) st)
        (cast (congrArg (fun x => (compile x).Object) h) o) hs := by
  cases h
  rfl

/-- Reading the envelope after a release applies the instance's own-object handler. -/
theorem envelope_recordOwn (nd : Model.Node (Model.protoOf (compiled F) E))
    (o : (Model.protoOf (compiled F) E).Object) (hs : List (Header I × Nat)) :
    envelope e ⟨(Model.protoOf (compiled F) E).recordOwn nd.st o hs, nd.seen ++ [o]⟩ =
      (e.ops hn).recordOwn (envelope e nd) (wireOf e o) hs := by
  rw [envelope_eq, envelope_eq, wireOf_eq]
  change (cast (congrArg (fun s : ChainShape (pubOf E) O.Id I => s.State) e.shape_eq)
    ((F (pubOf E)).recordOwn nd.st.1 o hs)) hn = _
  rw [cast_recordOwn e.shape_eq]
  rfl

private theorem cast_act {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : (compile s).State) (d : (compile q).Duty) :
    cast (congrArg (fun x => x.State) h)
      ((compile s).act st (cast (congrArg (fun x => (compile x).Duty) h.symm) d)).1.1 =
      ((compile q).act (cast (congrArg (fun x => x.State) h) st.1, st.2) d).1.1 := by
  cases h
  rfl

/-- Transport the engine's post-act state to its local shape operation. -/
theorem envelope_act (nd : Model.Node (Model.protoOf (compiled F) E))
    (d : ShapeDuty e.skel.Kind) :
    envelope e ⟨(Model.protoOf (compiled F) E).act nd.st (engineDuty e d) |>.1,
      nd.seen⟩ =
      match d with
      | .poll t => ((e.ops hn).pollBatch (envelope e nd) t).1
      | .pollPropose t => ((e.ops hn).pollPropose (envelope e nd) t).1
      | .propose s _ => ((e.ops hn).propose (envelope e nd) s).1
      | .act _ _ => envelope e nd := by
  rw [envelope_eq, engineDuty_eq]
  change (cast (congrArg (fun x : ChainShape (pubOf E) O.Id I => x.State) e.shape_eq)
    ((compile (F (pubOf E))).act nd.st _).1.1) hn = _
  refine (congrArg (fun f : ∀ h, e.State h => f hn) (cast_act e.shape_eq nd.st d)).trans ?_
  cases d <;> simp [compile, shape, familyOps, withMempool, hn, envelope_eq]

private theorem cast_role {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (d : (compile q).Duty) :
    (compile s).role (cast (congrArg (fun x => (compile x).Duty) h.symm) d) =
      cast (congrArg (fun x => (compile x).Role) h.symm) ((compile q).role d) := by
  cases h
  rfl

/-- The duty role is transported along with the duty. -/
theorem role_engineDuty (d : ShapeDuty e.skel.Kind) :
    (Model.protoOf (compiled F) E).role (engineDuty e d) = engineRole e (e.skel.role d) := by
  rw [engineDuty_eq, engineRole_eq]
  exact cast_role e.shape_eq d

private theorem cast_duties {s q : ChainShape (pubOf E) O.Id I} (h : s = q) (t : Time) :
    (compile s).duties t = ((compile q).duties t).map
      (cast (congrArg (fun x => (compile x).Duty) h.symm)) ∧
    (compile s).deliverDuties t = ((compile q).deliverDuties t).map
      (cast (congrArg (fun x => (compile x).Duty) h.symm)) := by
  cases h
  exact ⟨(List.map_id' _).symm, (List.map_id' _).symm⟩

private theorem engine_duties (t : Time) :
    (Model.protoOf (compiled F) E).duties t = (e.skel.duties t).map (engineDuty e) ∧
    (Model.protoOf (compiled F) E).deliverDuties t =
      (e.skel.deliverDuties t).map (engineDuty e) := by
  rw [show engineDuty e = _ from funext (engineDuty_eq e)]
  exact cast_duties e.shape_eq t

/-- Casting an object along a shape equality preserves its item.
Kept for a downstream consumer. -/
theorem cast_item {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (o : (compile s).Object) :
    (cast (congrArg (fun x => (compile x).Object) h) o : (compile q).Object).item? =
      o.item? := by
  cases h
  rfl

/-- Casting an object along a shape equality preserves whether it is unsigned.
Kept for a downstream consumer. -/
theorem cast_unsigned {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (o : (compile s).Object) :
    (cast (congrArg (fun x => (compile x).Object) h) o : (compile q).Object).auth = .none ↔
      o.auth = .none := by
  cases h
  rfl

/-- A poll duty cast along a shape equality still produces only data messages.
Kept for a downstream consumer. -/
theorem cast_poll_items {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : (compile s).State) (t : Nat)
    {m : Model.Msg (Header I) s.Body} {cs : List (compile s).Object}
    (hm : (m, cs) ∈ ((compile s).act st
      (cast (congrArg (fun x => (compile x).Duty) h.symm)
        (ShapeDuty.poll t : (compile q).Duty))).2) : ∃ b, m = .data b := by
  cases h
  obtain ⟨⟨b, carried⟩, _, he⟩ := List.mem_map.mp hm
  exact ⟨b, (Prod.mk.inj he).1.symm⟩

private theorem cast_pollPropose_candidates {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : (compile s).State) (t : Nat)
    (hnone : (q.pollPropose (cast (congrArg (fun x => x.State) h) st.1) t).2 = none) :
    ((compile s).act st (cast (congrArg (fun x => (compile x).Duty) h.symm)
      (ShapeDuty.pollPropose t : (compile q).Duty))).2 = [] := by
  cases h
  change (Option.map _ (s.pollPropose st.1 t).2).toList = []
  rw [show (s.pollPropose st.1 t).2 = none from hnone]
  rfl

/-- The receiver's vote authentication `io` held by the envelope: `init` stores it, every local
operation keeps it, and processing decodes messages with it. -/
structure Encoding.IOLaws (e : Encoding F E p hN hn A)
    (io : e.State hn → Model.VoteIO e.Tok (ShapeRole e.skel.Kind) e.Data (pubOf E).n) :
    Prop where
  init_io : ∀ k select x, io ((e.ops hn).init k select x) = x
  setNode_io : ∀ st n, io (e.adapter.setNode st n) = io st
  setDue_io : ∀ st b, io (e.adapter.setDue st b) = io st
  applyCuts_io : ∀ st w cuts, io (e.adapter.applyCuts st w cuts) = io st
  relayIf_io : ∀ st c [Decidable c] o, io (e.adapter.relayIf st c o) = io st
  attest_io : ∀ st n a, io (e.adapter.attest st n a) = io st
  wake_io : ∀ st k t, io (e.adapter.wake st k t) = io st
  clock_io : ∀ st t, io ((e.ops hn).clock st t) = io st
  pollBatch_io : ∀ st t, io ((e.ops hn).pollBatch st t).1 = io st
  pollPropose_io : ∀ st t, io ((e.ops hn).pollPropose st t).1 = io st
  recordOwn_io : ∀ st o hs, io ((e.ops hn).recordOwn st o hs) = io st
  process_eq : ∀ st, (e.ops hn).process st =
    NodeAsChainShape.process { e.codec with message := e.decodeMessage (io st) } e.adapter st

/-- The local equations used to derive the replay laws. They describe only the adapter's
observations, not the layout or contents of publication queues. -/
structure Encoding.OpLaws (e : Encoding F E p hN hn A) (due : e.State hn → Bool) : Prop where
  setNode_obs : ∀ st n, let d := e.adapter; let r := d.setNode st n
    d.node r = n ∧ d.self r = d.self st ∧ d.now r = d.now st ∧ due r = due st
  setDue_obs : ∀ st b, let d := e.adapter; let r := d.setDue st b
    d.node r = d.node st ∧ d.self r = d.self st ∧ d.now r = d.now st ∧ due r = b
  applyCuts_obs : ∀ st w cuts, let d := e.adapter; let r := d.applyCuts st w cuts
    d.node r = cuts.1 ∧ d.self r = d.self st ∧ d.now r = d.now st ∧ due r = due st
  relayIf_obs : ∀ st c [Decidable c] o, let d := e.adapter; let r := d.relayIf st c o
    d.node r = d.node st ∧ d.self r = d.self st ∧ d.now r = d.now st ∧ due r = due st
  /-- Signing records the new node state, then possibly runs the own `on_attestation`s of
  what it releases. -/
  attest_obs : ∀ st n a, let d := e.adapter; let r := d.attest st n a
    (∃ l : List (FG.Att (Fintype.card V)),
      d.node r = l.foldl (fun n a => (Node.onAttestation n a).1) n) ∧
    d.self r = d.self st ∧ d.now r = d.now st
  wake_obs : ∀ st k t, let d := e.adapter; let r := d.wake st k t
    d.self r = k ∧ d.now r = t
  init_obs : ∀ k select x, let r := (e.ops hn).init k select x
    e.adapter.self r = k ∧ due r = false
  voteIO : ∃ io, e.IOLaws io
  clock_obs : ∀ st t, let d := e.adapter; let r := (e.ops hn).clock st t
    d.node r = d.node st ∧ d.self r = d.self st ∧ d.now r = t ∧ due r = due st
  propose_eq : (e.ops hn).propose = NodeAsChainShape.propose e.codec e.adapter
  restore_eq : (e.ops hn).restore = NodeAsChainShape.restore e.adapter
  pollPropose_obs : ∀ st t, ((e.ops hn).pollPropose st t).2 = none ∧
    let d := e.adapter; let r := ((e.ops hn).pollPropose st t).1; let u := nodeTick d st
    d.node r = d.node u ∧ d.self r = d.self u ∧ d.now r = d.now u ∧ due r = due u
  pollBatch_obs : ∀ st t, let d := e.adapter; let r := ((e.ops hn).pollBatch st t).1
    let u := if due st then fgUpdate d st else st
    d.self r = d.self u ∧ d.now r = d.now u ∧ due r = false
  /-- A batch poll runs the node's FG update when due, then the own `on_attestation`s of the
  attestations it releases (`R st`: a flush, then the signed attestation). -/
  released : ∃ R : e.State hn → List (FG.Att (Fintype.card V)), ∀ st t pr dg x,
    let d := e.adapter
    d.node ((e.ops hn).pollBatch st t).1 = (R st).foldl (fun n a => (Node.onAttestation n a).1)
      (if due st then (tickStep pr dg (d.self st) (d.node st) (d.now st) x .fgUpdate).1
        else d.node st)
  /-- A quiet state's batch poll flushes nothing. The clock, every batch poll and the initial
  state are quiet, and recording an own object and processing a delivery keep it. -/
  quiet : ∃ Q : e.State hn → Prop,
    (∀ k select x, Q ((e.ops hn).init k select x)) ∧ (∀ st t, Q ((e.ops hn).clock st t)) ∧
    (∀ st t, Q ((e.ops hn).pollBatch st t).1) ∧
    (∀ st o hs, Q st → Q ((e.ops hn).recordOwn st o hs)) ∧
    (∀ st o hs, Q st → Q ((e.ops hn).process st o hs)) ∧
    ∀ st t, Q st → e.adapter.node ((e.ops hn).pollBatch st t).1 =
      e.adapter.node (if due st then fgUpdate e.adapter st else st)
  recordOwn_obs : ∀ st o hs,
    let d := e.adapter
    let r := (e.ops hn).recordOwn st o hs
    let u := match o with
      | .mk (.signed k (.proposer _)) (.item h) _ => recordBlock e.codec d st k h hs
      | _ => st
    d.node r = d.node u ∧ d.self r = d.self u ∧ d.now r = d.now u ∧ due r = due u
  tick_order : e.skel.order = [.poll, .poll, .pollPropose, .propose, .poll, .poll]
  deliver_order : e.skel.deliverOrder = [.poll]
  poll_selection : e.skel.pollSel = .fixed Finset.univ
  proposer_selection : ∀ s, e.skel.proposerSel s = .sized 1
  grid_time : ∀ s,
    e.skel.grid.slotTime s = (paramsAtCount p (Fintype.card V) hN hn).slotTime s
  proposer_role : ∀ s (hs : 0 < s) h,
    (e.role (.propose s hs) (.item h)).getD (.proposer s) = .proposer s
  decode_encode : ∀ atts payload,
    e.codec.decode (e.codec.encode atts payload) = some (atts, payload)

namespace Encoding.OpLaws

/-- The quiet states of `quiet`: their batch poll flushes nothing. -/
def quietOf (L : e.OpLaws due) : e.State hn → Prop := L.quiet.choose

theorem quietOf_spec (L : e.OpLaws due) :
    (∀ k select x, L.quietOf ((e.ops hn).init k select x)) ∧
    (∀ st t, L.quietOf ((e.ops hn).clock st t)) ∧
    (∀ st t, L.quietOf ((e.ops hn).pollBatch st t).1) ∧
    (∀ st o hs, L.quietOf st → L.quietOf ((e.ops hn).recordOwn st o hs)) ∧
    (∀ st o hs, L.quietOf st → L.quietOf ((e.ops hn).process st o hs)) ∧
    ∀ st t, L.quietOf st → e.adapter.node ((e.ops hn).pollBatch st t).1 =
      e.adapter.node (if due st then fgUpdate e.adapter st else st) :=
  L.quiet.choose_spec

/-- The attestations a batch poll releases, by `released`. -/
noncomputable def relOf (L : e.OpLaws due) : e.State hn → List (FG.Att (Fintype.card V)) :=
  L.released.choose

theorem relOf_spec (L : e.OpLaws due) : ∀ st t pr dg x,
    e.adapter.node ((e.ops hn).pollBatch st t).1 =
      (L.relOf st).foldl (fun n a => (Node.onAttestation n a).1)
        (if due st then (tickStep pr dg (e.adapter.self st) (e.adapter.node st)
          (e.adapter.now st) x .fgUpdate).1 else e.adapter.node st) :=
  L.released.choose_spec

/-- The tick duty order at a nonnegative time. Kept for a downstream consumer. -/
theorem tick_schedule (L : e.OpLaws due) (t : Time) (ht : 0 ≤ t) :
    (Model.protoOf (compiled F) E).duties t =
      (([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] : List (ShapeDuty e.skel.Kind)) ++
        e.skel.proposeAt t ++ ([.poll t.toNat, .poll t.toNat] : List (ShapeDuty e.skel.Kind))).map
          (engineDuty e) := by
  rw [(engine_duties (e := e) t).1]
  simp [Skeleton.duties, Skeleton.stepAt, L.tick_order, ht]

/-- A delivery schedules a poll exactly at nonnegative times. Kept for a downstream consumer. -/
theorem deliver_schedule (L : e.OpLaws due) (t : Time) :
    (Model.protoOf (compiled F) E).deliverDuties t =
      if 0 ≤ t then [engineDuty e (.poll t.toNat)] else [] := by
  rw [(engine_duties (e := e) t).2]
  by_cases ht : 0 ≤ t <;> simp [Skeleton.deliverDuties, Skeleton.stepAt, L.deliver_order, ht]

/-- Every node is selected for polling in a valid run. Kept for a downstream consumer. -/
theorem poll_selected [DecidableEq V] (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (hv : rho.ExecutionValid) (v : V) : rho.ownKey v ∈ rho.sel (engineRole e .poll) := by
  have h := hv.selValid (engineRole e .poll)
  rw [selSpec_engineRole] at h
  simp only [Skeleton.selSpec, L.poll_selection, Model.SelSpec.Admits] at h
  rw [h]
  exact Finset.mem_univ _

theorem recordOwn_pres (L : e.OpLaws due) (st : e.State hn)
    (o : ShapeObj (Fintype.card V) e.skel.Kind I e.Body) (hs : List (Header I × Nat)) :
    let r := (e.ops hn).recordOwn st o hs
    e.adapter.self r = e.adapter.self st ∧ e.adapter.now r = e.adapter.now st ∧ due r = due st := by
  have h := L.recordOwn_obs st o hs
  dsimp only at h ⊢
  refine ⟨h.2.1.trans ?_, h.2.2.1.trans ?_, h.2.2.2.trans ?_⟩ <;>
    split <;> simp [recordBlock] <;>
    split <;> simp [L.applyCuts_obs]

/-- Release preserves an envelope invariant if recording each candidate preserves it.
Kept for a downstream consumer. -/
theorem releaseAll_pres (rho : Model.Run (compiled F) E) (Q : e.State hn → Prop)
    (k : Fin (Fintype.card V)) (nd : Model.Node (Model.protoOf (compiled F) E))
    (cs : List (Model.protoOf (compiled F) E).Object)
    (hrec : ∀ o ∈ cs, ∀ st hs, Q st → Q ((e.ops hn).recordOwn st (wireOf e o) hs))
    (h : Q (envelope e nd)) :
    Q (envelope e (Model.releaseAll (Model.protoOf (compiled F) E) rho.hash k nd cs).1) := by
  refine Model.releaseAll_pres_node rho.hash k (fun n => Q (envelope e n)) nd cs ?_ h
  intro n c hc hn'
  exact (congrArg Q (envelope_recordOwn (e := e) n c (Model.digests rho.hash c))).mpr
    (hrec c hc _ _ hn')

private theorem recordOwn_plain (L : e.OpLaws due) (st : e.State hn)
    (o : ShapeObj (Fintype.card V) e.skel.Kind I e.Body) (hs : List (Header I × Nat))
    (h : o.auth = .none ∨ o.item? = none) :
    let r := (e.ops hn).recordOwn st o hs
    e.adapter.node r = e.adapter.node st ∧ e.adapter.self r = e.adapter.self st ∧
      e.adapter.now r = e.adapter.now st ∧ due r = due st := by
  have hobs := L.recordOwn_obs st o hs
  dsimp only at hobs ⊢
  split at hobs
  · rcases h with h | h <;> cases h
  · exact hobs

private theorem releaseAll_plain (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E))
    (cs : List (Model.protoOf (compiled F) E).Object)
    (hcs : ∀ o ∈ cs, o.auth = .none ∨ o.item? = none) :
    let a := envelope e nd
    let b := envelope e (Model.releaseAll (Model.protoOf (compiled F) E) rho.hash
      (rho.ownKey v) nd cs).1
    e.adapter.node b = e.adapter.node a ∧ e.adapter.self b = e.adapter.self a ∧
      e.adapter.now b = e.adapter.now a ∧ due b = due a := by
  dsimp only
  apply releaseAll_pres rho (fun st => e.adapter.node st = e.adapter.node (envelope e nd) ∧
    e.adapter.self st = e.adapter.self (envelope e nd) ∧
    e.adapter.now st = e.adapter.now (envelope e nd) ∧ due st = due (envelope e nd))
  · intro o ho st hs h
    have ⟨hn', hk, ht, hd⟩ := recordOwn_plain L st (wireOf e o) hs (by
      rcases hcs o ho with hunsigned | hdata
      · exact Or.inl ((congrArg Model.Obj.auth (wireOf_eq e o)).trans
          ((cast_unsigned e.shape_eq o).mpr hunsigned))
      · exact Or.inr ((congrArg Model.Obj.item? (wireOf_eq e o)).trans
          ((cast_item e.shape_eq o).trans hdata)))
    exact ⟨hn'.trans h.1, hk.trans h.2.1, ht.trans h.2.2.1, hd.trans h.2.2.2⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem gossip_obs (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Time) :
    let a := envelope e nd
    let b := envelope e (Model.releaseAll (Model.protoOf (compiled F) E) rho.hash
      (rho.ownKey v) nd (Model.gossipCandidates (Model.protoOf (compiled F) E) nd.st t)).1
    e.adapter.node b = e.adapter.node a ∧ e.adapter.self b = e.adapter.self a ∧
      e.adapter.now b = e.adapter.now a ∧ due b = due a := by
  apply releaseAll_plain L
  intro o ho
  obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
  exact Or.inl rfl

private theorem duty_poll_obs (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel (engineRole e .poll)) :
    let a := envelope e nd
    let b := envelope e (rho.dutyStep v nd (engineDuty e (.poll t))).1
    let u := if due a then fgUpdate e.adapter a else a
    e.adapter.node b = e.adapter.node ((e.ops hn).pollBatch a t).1 ∧
      e.adapter.self b = e.adapter.self u ∧ e.adapter.now b = e.adapter.now u ∧ due b = false ∧
      (L.quietOf a → e.adapter.node b = e.adapter.node u) ∧ L.quietOf b := by
  dsimp only
  rw [rho.dutyStep_eq, role_engineDuty, Skeleton.role, ite_eq_left hsel]
  let d := engineDuty e (.poll t)
  let act := (Model.protoOf (compiled F) E).act nd.st d
  have h := releaseAll_plain L rho v
    ⟨act.1, nd.seen⟩ (rho.signedCandidate v d act.2) (by
      intro o ho
      obtain ⟨m, cs, hm, _, _, rfl⟩ := (rho.mem_signedCandidate).mp ho
      dsimp only [act, d] at hm
      rw [engineDuty_eq] at hm
      obtain ⟨b, rfl⟩ := cast_poll_items e.shape_eq nd.st t hm
      exact Or.inr rfl)
  have hq : L.quietOf (envelope e (Model.releaseAll (Model.protoOf (compiled F) E) rho.hash
      (rho.ownKey v) ⟨act.1, nd.seen⟩ (rho.signedCandidate v d act.2)).1) := by
    refine releaseAll_pres rho L.quietOf _ _ _
      (fun _ _ st hs hq => (quietOf_spec L).2.2.2.1 st _ hs hq) ?_
    dsimp only [act, d]
    rw [envelope_act]
    exact (quietOf_spec L).2.2.1 _ t
  dsimp only at h
  dsimp only [act, d] at h hq
  simp only [envelope_act] at h
  obtain ⟨hk, ht, hd⟩ := L.pollBatch_obs (envelope e nd) t
  exact ⟨h.1, h.2.1.trans hk, h.2.2.1.trans ht,
    h.2.2.2.trans hd, fun ha => h.1.trans ((quietOf_spec L).2.2.2.2.2 _ t ha), hq⟩

/-- A selected proposal poll has the observable effect of a node tick.
Kept for a downstream consumer. -/
theorem duty_pollPropose (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Nat)
    (hsel : rho.ownKey v ∈ rho.sel (engineRole e .poll)) :
    let b := envelope e (rho.dutyStep v nd (engineDuty e (.pollPropose t))).1
    let u := nodeTick e.adapter (envelope e nd)
    e.adapter.node b = e.adapter.node u ∧ e.adapter.self b = e.adapter.self u ∧
      e.adapter.now b = e.adapter.now u ∧ due b = due u := by
  have hnone : ((Model.protoOf (compiled F) E).act nd.st (engineDuty e (.pollPropose t))).2 =
      [] := by
    rw [engineDuty_eq]
    apply cast_pollPropose_candidates e.shape_eq
    simp only [shape, familyOps, dite_eq_left hn, (L.pollPropose_obs _ _).1]
  have hs : rho.signedCandidate v (engineDuty e (.pollPropose t)) [] = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro o ho
    obtain ⟨m, cs, hm, _, _, _⟩ := rho.mem_signedCandidate.mp ho
    exact List.not_mem_nil hm
  dsimp only
  rw [rho.dutyStep_eq, role_engineDuty, Skeleton.role, ite_eq_left hsel, hnone, hs,
    Model.releaseAll]
  simp only [envelope_act]
  exact (L.pollPropose_obs _ _).2

private theorem fgUpdate_clock (L : e.OpLaws due) (st : e.State hn) :
    e.adapter.self (fgUpdate e.adapter st) = e.adapter.self st ∧
      e.adapter.now (fgUpdate e.adapter st) = e.adapter.now st := by
  simp only [fgUpdate]
  split
  · simp only [L.setDue_obs, L.setNode_obs, and_self]
  · split
    · simp only [L.setDue_obs, L.setNode_obs, and_self]
    · exact ⟨(L.attest_obs _ _ _).2.1.trans (L.setDue_obs _ _).2.1 |>.trans
        (L.setNode_obs _ _).2.1, (L.attest_obs _ _ _).2.2.trans (L.setDue_obs _ _).2.2.1 |>.trans
        (L.setNode_obs _ _).2.2.1⟩

private theorem poll_clock (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Nat) :
    let a := envelope e nd
    let b := envelope e (rho.dutyStep v nd (engineDuty e (.poll t))).1
    e.adapter.self b = e.adapter.self a ∧ e.adapter.now b = e.adapter.now a ∧
      (due a = false → due b = false) ∧ (L.quietOf a → L.quietOf b) ∧
      (due a = false → L.quietOf a → e.adapter.node b = e.adapter.node a) := by
  dsimp only
  by_cases hs : rho.ownKey v ∈ rho.sel (engineRole e .poll)
  · obtain ⟨-, hk, ht, hd, hq, hqb⟩ := duty_poll_obs L rho v nd t hs
    refine ⟨hk.trans ?_, ht.trans ?_, fun _ => hd, fun _ => hqb, fun ha hqa => ?_⟩
    · split
      · exact (fgUpdate_clock L _).1
      · rfl
    · split
      · exact (fgUpdate_clock L _).2
      · rfl
    · simpa only [ha, Bool.false_eq_true, ↓reduceIte] using hq hqa
  · rw [rho.dutyStep_eq, role_engineDuty, Skeleton.role, ite_eq_right hs]
    exact ⟨rfl, rfl, id, id, fun _ _ => rfl⟩

open Classical in
private theorem nodeTick_obs (L : e.OpLaws due) (st : e.State hn) :
    let r := nodeTick e.adapter st
    e.adapter.self r = e.adapter.self st ∧ e.adapter.now r = e.adapter.now st ∧
      if (paramsAtCount p (Fintype.card V) hN hn).IsPublic (e.adapter.now st) then
        e.adapter.node r =
          (acCall (e.adapter.self st) (e.adapter.node st) (e.adapter.now st) .tick).1 ∧
          due r = e.adapter.sign (e.adapter.self st) (e.adapter.now st)
      else e.adapter.node r = e.adapter.node st ∧ due r = due st := by
  dsimp only
  by_cases hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic (e.adapter.now st) <;>
    simp [nodeTick, hp, L.setDue_obs, L.applyCuts_obs]

private theorem processOne_obs (L : e.OpLaws due) (pr : Nat → Fin (Fintype.card V))
    (dg : Digest (List (FG.Att (Fintype.card V))) A.Payload) (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat))
    (st : e.State hn) (o : ShapeObj (Fintype.card V) e.skel.Kind I e.Body) :
    let r := processOne C e.adapter hs st o
    e.adapter.node r = ((canonEvent C hs o).map
      (fun ev => (exec pr dg
        (e.adapter.self st) (e.adapter.node st) (e.adapter.now st) ev).1)).getD
          (e.adapter.node st) ∧
    e.adapter.self r = e.adapter.self st ∧ e.adapter.now r = e.adapter.now st ∧ due r = due st := by
  dsimp only
  unfold processOne
  cases he : canonEvent C hs o with
  | none => simp
  | some ev =>
    cases ev <;> try solve | simp [exec, L.applyCuts_obs, L.relayIf_obs]
    all_goals unfold canonEvent at he; split at he <;> cases he

private theorem process_fold_obs (L : e.OpLaws due) (pr : Nat → Fin (Fintype.card V))
    (dg : Digest (List (FG.Att (Fintype.card V))) A.Payload) (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat))
    (xs : List (ShapeObj (Fintype.card V) e.skel.Kind I e.Body)) (st : e.State hn) :
    let r := xs.foldl (processOne C e.adapter hs) st
    e.adapter.node r = xs.foldl (fun s w => ((canonEvent C hs w).map
      (fun ev => (exec pr dg (e.adapter.self st) s (e.adapter.now st) ev).1)).getD s)
      (e.adapter.node st) ∧
    e.adapter.self r = e.adapter.self st ∧ e.adapter.now r = e.adapter.now st ∧
    due r = due st := by
  induction xs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons w ws ih =>
    obtain ⟨hnode, hself, hnow, hdue⟩ := processOne_obs L pr dg C hs st w
    obtain ⟨hn', hs', ht', hd'⟩ := ih (processOne C e.adapter hs st w)
    refine ⟨?_, hs'.trans hself, ht'.trans hnow, hd'.trans hdue⟩
    rw [List.foldl_cons, List.foldl_cons, hn', hself, hnow, hnode]

theorem restore_obs (L : e.OpLaws due) (k : Fin (Fintype.card V))
    (st : e.State hn) (t : Time) :
    let d := e.adapter
    let r := (e.ops hn).restore k st t
    d.node r = (Node.restart k (d.node st) t).1 ∧
    d.self r = k ∧ d.now r = t ∧ due r = false := by
  dsimp only
  rw [L.restore_eq]
  simp [NodeAsChainShape.restore, L.setDue_obs, L.applyCuts_obs, L.wake_obs]

private theorem cast_process {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : s.State) (o : (compile s).Object) (hs : List (Header I × Nat)) :
    cast (congrArg (fun x => x.State) h) (s.process st o hs) =
      q.process (cast (congrArg (fun x => x.State) h) st)
        (cast (congrArg (fun x => (compile x).Object) h) o) hs := by
  cases h
  rfl

/-- Transport the processed delivery to the instance envelope. -/
theorem envelope_process (nd : Model.Node (Model.protoOf (compiled F) E))
    (o : (Model.protoOf (compiled F) E).Object) (hs : List (Header I × Nat)) :
    envelope e ⟨(Model.protoOf (compiled F) E).process nd.st o hs, nd.seen ++ [o]⟩ =
      (e.ops hn).process (envelope e nd) (wireOf e o) hs := by
  rw [envelope_eq, envelope_eq, wireOf_eq]
  exact congrArg (fun f : ∀ h, e.State h => f hn) (cast_process e.shape_eq nd.st.1 o hs)

theorem process_pres (L : e.OpLaws due) (st : e.State hn)
    (o : ShapeObj (Fintype.card V) e.skel.Kind I e.Body) (hs : List (Header I × Nat)) :
    let r := (e.ops hn).process st o hs
    e.adapter.self r = e.adapter.self st ∧ e.adapter.now r = e.adapter.now st ∧
      due r = due st := by
  dsimp only
  obtain ⟨io, hio⟩ := L.voteIO
  rw [hio.process_eq]
  exact (process_fold_obs L (fun _ => e.adapter.self st) (fun _ _ _ _ _ => 0) _
    hs (delivered _ e.adapter hs st o) st).2

theorem propose_pres (L : e.OpLaws due) (st : e.State hn) (s : Slot) :
    let r := ((e.ops hn).propose st s).1
    e.adapter.self r = e.adapter.self st ∧ e.adapter.now r = e.adapter.now st ∧
      due r = due st := by
  dsimp only
  rw [L.propose_eq]
  cases he : (acProposal (e.adapter.node st) (e.adapter.now st)).2.2 with
  | none => simpa only [NodeAsChainShape.propose, he] using
      (L.setNode_obs st (acProposal (e.adapter.node st) (e.adapter.now st)).1).2
  | some dp =>
    obtain ⟨d, payload⟩ := dp
    simpa only [NodeAsChainShape.propose, he] using
      (L.setNode_obs st (acProposal (e.adapter.node st) (e.adapter.now st)).1).2

private theorem duty_pres (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (d : ShapeDuty e.skel.Kind) :
    let a := envelope e nd
    let b := envelope e (rho.dutyStep v nd (engineDuty e d)).1
    e.adapter.self b = e.adapter.self a ∧ e.adapter.now b = e.adapter.now a ∧
      (due a = false → (∀ t, d = .pollPropose t →
        rho.ownKey v ∉ rho.sel (engineRole e .poll)) → due b = false) := by
  dsimp only
  cases d with
  | poll t =>
    obtain ⟨hk, ht, hd, -⟩ := poll_clock L rho v nd t
    exact ⟨hk, ht, fun h _ => hd h⟩
  | pollPropose t =>
    by_cases hs : rho.ownKey v ∈ rho.sel (engineRole e .poll)
    · obtain ⟨-, hk, ht, -⟩ := duty_pollPropose L rho v nd t hs
      exact ⟨hk.trans (nodeTick_obs L _).1, ht.trans (nodeTick_obs L _).2.1,
        fun _ h => (h t rfl hs).elim⟩
    · rw [rho.dutyStep_eq, role_engineDuty, Skeleton.role, ite_eq_right hs]
      exact ⟨rfl, rfl, fun h _ => h⟩
  | propose s hs =>
    rw [rho.dutyStep_eq]
    split
    · apply releaseAll_pres rho (fun st => e.adapter.self st = e.adapter.self (envelope e nd) ∧
        e.adapter.now st = e.adapter.now (envelope e nd) ∧
        (due (envelope e nd) = false → (∀ t, ShapeDuty.propose s hs = .pollPropose t →
          rho.ownKey v ∉ rho.sel (engineRole e .poll)) → due st = false))
      · intro o _ st ds h
        obtain ⟨hk, ht, hd⟩ := recordOwn_pres L st (wireOf e o) ds
        exact ⟨hk.trans h.1, ht.trans h.2.1, fun ha hn => hd.trans (h.2.2 ha hn)⟩
      · rw [envelope_act]
        obtain ⟨hk, ht, hd⟩ := propose_pres L (envelope e nd) s
        exact ⟨hk, ht, fun ha _ => hd.trans ha⟩
    · exact ⟨rfl, rfl, fun hd _ => hd⟩
  | act s k =>
    rw [rho.dutyStep_eq]
    split
    · apply releaseAll_pres rho (fun st => e.adapter.self st = e.adapter.self (envelope e nd) ∧
        e.adapter.now st = e.adapter.now (envelope e nd) ∧
        (due (envelope e nd) = false → (∀ t, ShapeDuty.act s k = .pollPropose t →
          rho.ownKey v ∉ rho.sel (engineRole e .poll)) → due st = false))
      · intro o _ st ds h
        obtain ⟨hk, ht, hd⟩ := recordOwn_pres L st (wireOf e o) ds
        exact ⟨hk.trans h.1, ht.trans h.2.1, fun ha hn => hd.trans (h.2.2 ha hn)⟩
      · rw [envelope_act]
        exact ⟨rfl, rfl, fun ha _ => ha⟩
    · exact ⟨rfl, rfl, fun hd _ => hd⟩

private theorem duties_pres (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (ds : List (ShapeDuty e.skel.Kind)) :
    let a := envelope e nd
    let b := envelope e (rho.runDuties v nd (ds.map (engineDuty e))).1
    e.adapter.self b = e.adapter.self a ∧ e.adapter.now b = e.adapter.now a ∧
      (due a = false → (∀ t, ShapeDuty.pollPropose t ∈ ds →
        rho.ownKey v ∉ rho.sel (engineRole e .poll)) → due b = false) := by
  induction ds generalizing nd with
  | nil =>
    rw [List.map_nil, rho.runDuties_nil]
    exact ⟨rfl, rfl, fun h _ => h⟩
  | cons d ds ih =>
    rw [List.map_cons, rho.runDuties_cons]
    obtain ⟨hk, ht, hd⟩ := duty_pres L rho v nd d
    obtain ⟨hk', ht', hd'⟩ := ih (rho.dutyStep v nd (engineDuty e d)).1
    exact ⟨hk'.trans hk, ht'.trans ht, fun ha h =>
      hd' (hd ha (fun t he => h t (he ▸ List.mem_cons_self)))
        (fun t hm => h t (List.mem_cons_of_mem d hm))⟩

private theorem tick_pres (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Time) :
    let a := envelope e nd
    let b := envelope e (rho.tick nd v t).1
    e.adapter.self b = e.adapter.self a ∧ e.adapter.now b = t ∧
      (due a = false → due b = false) := by
  let clk := afterClock rho nd v t
  have ⟨_, hk, ht, hd⟩ := L.clock_obs (envelope e nd) t
  have hclk : e.adapter.self (envelope e clk) = e.adapter.self (envelope e nd) ∧
      e.adapter.now (envelope e clk) = t ∧ due (envelope e clk) = due (envelope e nd) := by
    rw [envelope_clock]; exact ⟨hk, ht, hd⟩
  dsimp only
  cases haw : E.awake v t with
  | false =>
    simp only [Model.Run.tick, haw, Bool.false_eq_true, ↓reduceIte, ← afterClock_eq]
    exact ⟨hclk.1, hclk.2.1, fun h => hclk.2.2.trans h⟩
  | true =>
    rw [rho.tick_of_awake nd v t haw, ← afterClock_eq]
    let r := (rho.runDuties v clk ((Model.protoOf (compiled F) E).duties t)).1
    obtain ⟨_, hgk, hgt, hgd⟩ := gossip_obs L rho v r t
    dsimp only at hgk hgt hgd
    rw [hgk, hgt, hgd]
    by_cases htime : 0 ≤ t
    · dsimp only [r]
      rw [tick_schedule L t htime]
      let ds := ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
        List (ShapeDuty e.skel.Kind)) ++ e.skel.proposeAt t
      have ⟨hdk, hdt, hdd⟩ := duties_pres L rho v clk
        (ds ++ ([.poll t.toNat, .poll t.toNat] : List (ShapeDuty e.skel.Kind)))
      refine ⟨hdk.trans hclk.1, hdt.trans hclk.2.1, fun h => ?_⟩
      by_cases hs : rho.ownKey v ∈ rho.sel (engineRole e .poll)
      · rw [List.map_append, rho.runDuties_append_fst, List.map_cons, List.map_cons, List.map_nil,
          rho.runDuties_cons, rho.runDuties_cons, rho.runDuties_nil]
        exact (duty_poll_obs L rho v _ t.toNat hs).2.2.2.1
      · exact hdd (hclk.2.2.trans h) (fun _ _ => hs)
    · dsimp only [r]
      rw [(engine_duties (e := e) t).1]
      simp only [Skeleton.duties, L.tick_order, Skeleton.stepAt, htime, ↓reduceIte,
        Skeleton.proposeAt, TimeGrid.slotAt?, sub_zero, false_and, List.flatMap_cons,
        List.flatMap_nil, List.nil_append, List.map_nil, rho.runDuties_nil]
      exact ⟨hclk.1, hclk.2.1, fun h => hclk.2.2.trans h⟩

private theorem deliver_obs (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E))
    (o : (Model.protoOf (compiled F) E).Object) (t : Time) :
    let a := (e.ops hn).process (envelope e nd) (wireOf e o) (Model.digests rho.hash o)
    let b := envelope e (rho.deliver nd v o t).1
    e.adapter.self b = e.adapter.self a ∧ e.adapter.now b = e.adapter.now a ∧
      (due a = false → due b = false) ∧
      (due a = false → L.quietOf a → e.adapter.node b = e.adapter.node a) := by
  let post : Model.Node (Model.protoOf (compiled F) E) :=
    ⟨(Model.protoOf (compiled F) E).process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
  let ds := (Model.protoOf (compiled F) E).deliverDuties t
  let b := envelope e (Model.releaseAll (Model.protoOf (compiled F) E)
    rho.hash (rho.ownKey v) (rho.runDuties v post ds).1
    (Model.gossipCandidates (Model.protoOf (compiled F) E) (rho.runDuties v post ds).1.st t)).1
  let a := (e.ops hn).process (envelope e nd) (wireOf e o) (Model.digests rho.hash o)
  dsimp only
  change e.adapter.self b = e.adapter.self a ∧ e.adapter.now b = e.adapter.now a ∧
    (due a = false → due b = false) ∧
    (due a = false → L.quietOf a → e.adapter.node b = e.adapter.node a)
  have ⟨hn', hk, ht, hd⟩ := gossip_obs L rho v (rho.runDuties v post ds).1 t
  dsimp only at hn' hk ht hd
  have hp := envelope_process (e := e) nd o (Model.digests rho.hash o)
  change envelope e post = a at hp
  rw [← hp, hk, ht, hn', hd]
  -- Delivery either polls once or has no duty (even on an invalid run).
  dsimp only [ds]
  rw [deliver_schedule L]
  split
  · rw [rho.runDuties_cons, rho.runDuties_nil]
    obtain ⟨hk, ht, hd, -, hq⟩ := poll_clock L rho v post t.toNat
    exact ⟨hk, ht, hd, hq⟩
  · rw [rho.runDuties_nil]
    exact ⟨rfl, rfl, id, fun _ _ => rfl⟩

private theorem cast_init {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (k : Fin (Fintype.card V)) (sel : (compile s).Role → Bool)
    (io : Model.VoteIO s.Token (compile s).Role s.VoteData (Fintype.card V)) :
    cast (congrArg (fun x => x.State) h) (s.init k sel io) =
      q.init k (fun r => sel (cast (congrArg (fun x => (compile x).Role) h.symm) r))
        (cast (congrArg (fun x => Model.VoteIO x.Token (compile x).Role x.VoteData
          (Fintype.card V)) h) io) := by
  cases h
  rfl

private theorem cast_restore {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (k : Fin (Fintype.card V)) (st : s.State) (t : Time) :
    cast (congrArg (fun x => x.State) h) (s.restore k (s.durable st) t) =
      q.restore k (q.durable (cast (congrArg (fun x => x.State) h) st)) t := by
  cases h
  rfl

/-- The initial envelope uses the engine's actual role selections and the node's vote
authentication. -/
theorem envelope_init (rho : Model.Run (compiled F) E) (v : V) :
    envelope e (rho.initWorld v) =
      (e.ops hn).init (rho.ownKey v)
        (fun r => decide (rho.ownKey v ∈ rho.sel (engineRole e r))) (voteIOAt e rho v) := by
  rw [envelope_eq]
  change (cast (congrArg (fun x : ChainShape (pubOf E) O.Id I => x.State) e.shape_eq)
    ((F (pubOf E)).init (rho.ownKey v) _ (rho.voteIO v))) hn = _
  simp only [engineRole_eq, voteIOAt_eq]
  exact congrArg (fun st : ∀ h, e.State h => st hn)
    (cast_init e.shape_eq (rho.ownKey v) (fun r => decide (rho.ownKey v ∈ rho.sel r))
      (rho.voteIO v))

/-- Restoring an engine node restores its instance envelope. -/
theorem envelope_restore (nd : Model.Node (Model.protoOf (compiled F) E))
    (k : Fin (Fintype.card V)) (t : Time) :
    envelope e ⟨(Model.protoOf (compiled F) E).restore k
      ((Model.protoOf (compiled F) E).durable nd.st) t, nd.seen⟩ =
      (e.ops hn).restore k (envelope e nd) t := by
  rw [envelope_eq, envelope_eq]
  exact congrArg (fun f : ∀ h, e.State h => f hn) (cast_restore e.shape_eq k nd.st.1 t)

/-- The state at a cut reads its engine envelope. -/
theorem cut_envelope [DecidableEq V] (rho : Model.Run (compiled F) E) (v : V) (i : Nat) :
    stateAt e rho v i = envelope e (rho.stateBefore i v) :=
  (stateAt_eq e rho v i).trans (envelope_eq e _).symm

/-- Key and due-flag alignment at cuts, independent of proposal readiness. -/
theorem cut_obs [DecidableEq V] (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (i : Nat) :
    e.adapter.self (stateAt e rho v i) = rho.ownKey v ∧ due (stateAt e rho v i) = false := by
  rw [cut_envelope]
  induction i with
  | zero =>
    change e.adapter.self (envelope e (rho.initWorld v)) = rho.ownKey v ∧ _
    rw [show rho.stateBefore 0 v = rho.initWorld v from rfl, envelope_init]
    exact L.init_obs _ _ _
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      have ht : rho.events.take (i + 1) = rho.events.take i := by
        have hl := List.getElem?_eq_none_iff.1 he
        rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
      simpa only [Model.Run.stateBefore, ht] using ih
    | some ev =>
      rw [rho.stateBefore_succ he]
      cases ev with
      | tick u t =>
        by_cases h : u = v
        · subst u
          simp only [Model.Run.step, Function.update_self]
          have ⟨hk, _, hd⟩ := tick_pres L rho v (rho.stateBefore i v) t
          exact ⟨hk.trans ih.1, hd ih.2⟩
        · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm h)] using ih
      | deliver u o t =>
        by_cases h : u = v
        · subst u
          simp only [Model.Run.step, Function.update_self]
          obtain ⟨hk, _, hd, -⟩ := deliver_obs L rho v (rho.stateBefore i v) o t
          have ⟨hpk, _, hpd⟩ := process_pres L (envelope e (rho.stateBefore i v))
            (wireOf e o) (Model.digests rho.hash o)
          exact ⟨hk.trans (hpk.trans ih.1), hd (hpd.trans ih.2)⟩
        · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm h)] using ih
      | restart u t =>
        by_cases h : u = v
        · subst u
          simp only [Model.Run.step, Function.update_self, envelope_restore]
          exact ⟨(restore_obs L _ _ _).2.1, (restore_obs L _ _ _).2.2.2⟩
        · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm h)] using ih

private theorem tick_quiet (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Time)
    (hsel : rho.ownKey v ∈ rho.sel (engineRole e .poll)) :
    L.quietOf (envelope e (rho.tick nd v t).1) := by
  have hclk : L.quietOf (envelope e (afterClock rho nd v t)) := by
    rw [envelope_clock]; exact (quietOf_spec L).2.1 _ t
  cases haw : E.awake v t with
  | false =>
    simp only [Model.Run.tick, haw, Bool.false_eq_true, ↓reduceIte, ← afterClock_eq]
    exact hclk
  | true =>
    rw [rho.tick_of_awake nd v t haw, ← afterClock_eq]
    refine releaseAll_pres rho L.quietOf _ _ _
      (fun _ _ st hs hq => (quietOf_spec L).2.2.2.1 st _ hs hq) ?_
    by_cases htime : 0 ≤ t
    · rw [tick_schedule L t htime, List.map_append, rho.runDuties_append_fst, List.map_cons,
        List.map_cons, List.map_nil, rho.runDuties_cons, rho.runDuties_cons, rho.runDuties_nil]
      exact (duty_poll_obs L rho v _ t.toNat hsel).2.2.2.2.2
    · rw [(engine_duties (e := e) t).1]
      simp only [Skeleton.duties, L.tick_order, Skeleton.stepAt, htime, ↓reduceIte,
        Skeleton.proposeAt, TimeGrid.slotAt?, sub_zero, false_and, List.flatMap_cons,
        List.flatMap_nil, List.nil_append, List.map_nil, rho.runDuties_nil]
      exact hclk

private theorem deliver_quiet (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E))
    (o : (Model.protoOf (compiled F) E).Object) (t : Time)
    (h : L.quietOf ((e.ops hn).process (envelope e nd) (wireOf e o) (Model.digests rho.hash o))) :
    L.quietOf (envelope e (rho.deliver nd v o t).1) := by
  let post : Model.Node (Model.protoOf (compiled F) E) :=
    ⟨(Model.protoOf (compiled F) E).process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
  let ds := (Model.protoOf (compiled F) E).deliverDuties t
  change L.quietOf (envelope e (Model.releaseAll (Model.protoOf (compiled F) E)
    rho.hash (rho.ownKey v) (rho.runDuties v post ds).1
    (Model.gossipCandidates (Model.protoOf (compiled F) E) (rho.runDuties v post ds).1.st t)).1)
  refine releaseAll_pres rho L.quietOf _ _ _
    (fun _ _ st hs hq => (quietOf_spec L).2.2.2.1 st _ hs hq) ?_
  have hp := envelope_process (e := e) nd o (Model.digests rho.hash o)
  change envelope e post = _ at hp
  rw [← hp] at h
  dsimp only [ds]
  rw [deliver_schedule L]
  split
  · rw [rho.runDuties_cons, rho.runDuties_nil]
    exact (poll_clock L rho v post t.toNat).2.2.2.1 h
  · rw [rho.runDuties_nil]
    exact h

/-- At every cut of a valid run a node's state is quiet unless its last event was a restart. -/
theorem cut_quiet [DecidableEq V] (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (hv : rho.ExecutionValid) (v : V) :
    ∀ i, LastRestart rho v i ∨ L.quietOf (stateAt e rho v i)
  | 0 => by
    rw [cut_envelope, show rho.stateBefore 0 v = rho.initWorld v from rfl, envelope_init]
    exact Or.inr ((quietOf_spec L).1 _ _ _)
  | i + 1 => by
    have ih := cut_quiet L rho hv v i
    rw [cut_envelope] at ih ⊢
    have hext : LastRestart rho v i → (∀ ev, rho.events[i]? = some ev → ev.node ≠ v) →
        LastRestart rho v (i + 1) := fun h hi => lastRestart_other rho hi h
    cases he : rho.events[i]? with
    | none =>
      have ht : rho.events.take (i + 1) = rho.events.take i := by
        have hl := List.getElem?_eq_none_iff.1 he
        rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
      simp only [Model.Run.stateBefore, ht] at ih ⊢
      exact ih.imp_left fun h => hext h fun ev he' => by rw [he] at he'; cases he'
    | some ev =>
      by_cases hne : ev.node = v
      · rw [rho.stateBefore_succ he]
        cases ev with
        | tick u t =>
          simp only [Model.Event.node] at hne
          subst hne
          simp only [Model.Run.step, Function.update_self]
          exact Or.inr (tick_quiet L rho u _ t (poll_selected L rho hv u))
        | deliver u o t =>
          simp only [Model.Event.node] at hne
          subst hne
          simp only [Model.Run.step, Function.update_self]
          refine Or.inr (deliver_quiet L rho u _ o t ((quietOf_spec L).2.2.2.2.1 _ _ _ ?_))
          exact ih.resolve_left (not_lastRestart_deliver rho hv he)
        | restart u t =>
          simp only [Model.Event.node] at hne
          subst hne
          exact Or.inl ((lastRestart_iff rho u (i + 1)).2
            ⟨i, by omega, t, he, fun l h1 h2 => absurd h2 (by omega)⟩)
      · have h' := ih.imp_left fun h => hext h fun ev' he' => by
          rw [he] at he'; cases he'; exact hne
        rw [rho.stateBefore_succ he]
        cases ev <;> simp only [Model.Event.node] at hne <;>
          simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hne)] using h'

section VoteIO

variable {io : e.State hn → Model.VoteIO e.Tok (ShapeRole e.skel.Kind) e.Data (pubOf E).n}

private theorem processOne_io (hio : e.IOLaws io) (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat)) (st : e.State hn)
    (o : ShapeObj (Fintype.card V) e.skel.Kind I e.Body) :
    io (processOne C e.adapter hs st o) = io st := by
  unfold processOne
  split <;> simp only [hio.applyCuts_io, hio.relayIf_io]

theorem process_io (hio : e.IOLaws io) (st : e.State hn)
    (o : ShapeObj (Fintype.card V) e.skel.Kind I e.Body) (hs : List (Header I × Nat)) :
    io ((e.ops hn).process st o hs) = io st := by
  rw [hio.process_eq, NodeAsChainShape.process]
  generalize delivered _ e.adapter hs st o = xs
  generalize ({ e.codec with message := e.decodeMessage (io st) } :
    WireCodec A e.skel.Kind I e.Body) = C
  induction xs generalizing st with
  | nil => rfl
  | cons w ws ih => rw [List.foldl_cons, ih, processOne_io hio]

theorem duty_io (L : e.OpLaws due) (hio : e.IOLaws io) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (d : ShapeDuty e.skel.Kind) :
    io (envelope e (rho.dutyStep v nd (engineDuty e d)).1) = io (envelope e nd) := by
  rw [rho.dutyStep_eq]
  split
  · apply releaseAll_pres rho (fun st => io st = io (envelope e nd))
    · intro o _ st hs h
      exact (hio.recordOwn_io st _ hs).trans h
    · rw [envelope_act]
      cases d with
      | poll t => exact hio.pollBatch_io _ t
      | pollPropose t => exact hio.pollPropose_io _ t
      | propose s _ =>
        dsimp only
        rw [L.propose_eq]
        unfold NodeAsChainShape.propose
        dsimp only
        split <;> exact hio.setNode_io _ _
      | act _ _ => rfl
  · rfl

private theorem duties_io (L : e.OpLaws due) (hio : e.IOLaws io)
    (rho : Model.Run (compiled F) E) (v : V) (nd : Model.Node (Model.protoOf (compiled F) E))
    (ds : List (ShapeDuty e.skel.Kind)) :
    io (envelope e (rho.runDuties v nd (ds.map (engineDuty e))).1) = io (envelope e nd) := by
  induction ds generalizing nd with
  | nil => rw [List.map_nil, rho.runDuties_nil]
  | cons d ds ih => rw [List.map_cons, rho.runDuties_cons, ih, duty_io L hio]

private theorem gossip_io (hio : e.IOLaws io) (rho : Model.Run (compiled F) E) (v : V)
    (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Time) :
    io (envelope e (Model.releaseAll (Model.protoOf (compiled F) E) rho.hash (rho.ownKey v) nd
      (Model.gossipCandidates (Model.protoOf (compiled F) E) nd.st t)).1) =
      io (envelope e nd) :=
  releaseAll_pres rho (fun st => io st = io (envelope e nd)) _ nd _
    (fun _ _ st hs h => (hio.recordOwn_io st _ hs).trans h) rfl

private theorem tick_io (L : e.OpLaws due) (hio : e.IOLaws io) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Time) :
    io (envelope e (rho.tick nd v t).1) = io (envelope e nd) := by
  have hclk : io (envelope e (afterClock rho nd v t)) = io (envelope e nd) := by
    rw [envelope_clock]; exact hio.clock_io _ t
  cases haw : E.awake v t with
  | false =>
    simp only [Model.Run.tick, haw, Bool.false_eq_true, ↓reduceIte, ← afterClock_eq]
    exact hclk
  | true =>
    rw [rho.tick_of_awake nd v t haw, ← afterClock_eq, gossip_io hio, (engine_duties (e := e) t).1,
      duties_io L hio, hclk]

private theorem deliver_io (L : e.OpLaws due) (hio : e.IOLaws io)
    (rho : Model.Run (compiled F) E) (v : V) (nd : Model.Node (Model.protoOf (compiled F) E))
    (o : (Model.protoOf (compiled F) E).Object) (t : Time) :
    io (envelope e (rho.deliver nd v o t).1) = io (envelope e nd) := by
  let post : Model.Node (Model.protoOf (compiled F) E) :=
    ⟨(Model.protoOf (compiled F) E).process nd.st o (Model.digests rho.hash o), nd.seen ++ [o]⟩
  let ds := (Model.protoOf (compiled F) E).deliverDuties t
  change io (envelope e (Model.releaseAll (Model.protoOf (compiled F) E)
    rho.hash (rho.ownKey v) (rho.runDuties v post ds).1
    (Model.gossipCandidates (Model.protoOf (compiled F) E) (rho.runDuties v post ds).1.st t)).1) = _
  rw [gossip_io hio]
  dsimp only [ds]
  rw [(engine_duties (e := e) t).2, duties_io L hio,
    show envelope e post = _ from envelope_process nd o _]
  exact process_io hio _ _ _

/-- The envelope at every cut holds the node's own vote authentication. -/
theorem cut_io [DecidableEq V] (L : e.OpLaws due) (hio : e.IOLaws io)
    (rho : Model.Run (compiled F) E) (v : V) (i : Nat) :
    io (stateAt e rho v i) = voteIOAt e rho v := by
  rw [cut_envelope]
  induction i with
  | zero =>
    rw [show rho.stateBefore 0 v = rho.initWorld v from rfl, envelope_init]
    exact hio.init_io _ _ _
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      have ht : rho.events.take (i + 1) = rho.events.take i := by
        have hl := List.getElem?_eq_none_iff.1 he
        rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
      simpa only [Model.Run.stateBefore, ht] using ih
    | some ev =>
      rw [rho.stateBefore_succ he]
      cases ev with
      | tick u t =>
        by_cases h : u = v
        · subst u
          simp only [Model.Run.step, Function.update_self]
          exact (tick_io L hio rho _ _ t).trans ih
        · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm h)] using ih
      | deliver u o t =>
        by_cases h : u = v
        · subst u
          simp only [Model.Run.step, Function.update_self]
          exact (deliver_io L hio rho _ _ o t).trans ih
        · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm h)] using ih
      | restart u t =>
        by_cases h : u = v
        · subst u
          simp only [Model.Run.step, Function.update_self, envelope_restore]
          rw [L.restore_eq]
          simp only [NodeAsChainShape.restore, hio.setDue_io, hio.applyCuts_io, hio.wake_io]
          exact ih
        · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm h)] using ih

end VoteIO

/-- At a cut, processing a delivery decodes messages with the receiver's codec. -/
theorem process_stateAt [DecidableEq V] (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (i : Nat) :
    (e.ops hn).process (stateAt e rho v i) =
      NodeAsChainShape.process (receiverCodec e rho v) e.adapter (stateAt e rho v i) := by
  obtain ⟨io, hio⟩ := L.voteIO
  rw [hio.process_eq, cut_io L hio rho v i, receiverCodec_eq]

open Classical in
theorem tick_prefix [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v t}
    (_he : rho.events[i]? = some (.tick v t)) :
    let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
    (if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
      e.adapter.node (envelope e pre) = (acCall (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t .tick).1 ∧
        due (envelope e pre) = e.adapter.sign (rho.ownKey v) t
    else e.adapter.node (envelope e pre) = e.adapter.node (stateAt e rho v i) ∧
      due (envelope e pre) = false) := by
  let clk := afterClock rho (rho.stateBefore i v) v t
  let a := rho.dutyStep v clk (engineDuty e (.poll t.toNat)) |>.1
  let b := rho.dutyStep v a (engineDuty e (.poll t.toNat)) |>.1
  have hsel := poll_selected L rho hv v
  have hm := cut_obs L rho v i
  rw [cut_envelope] at hm
  have ⟨hnc, hkc, htc, hdc⟩ := L.clock_obs (envelope e (rho.stateBefore i v)) t
  dsimp only at hnc hkc htc hdc
  rw [← envelope_clock rho (rho.stateBefore i v) v t] at hnc hkc htc hdc
  have hqc : L.quietOf (envelope e clk) := by
    rw [envelope_clock]; exact (quietOf_spec L).2.1 _ t
  obtain ⟨hka, hta, hda, hqa, hna⟩ := poll_clock L rho v clk t.toNat
  obtain ⟨hkb, htb, hdb, -, hnb⟩ := poll_clock L rho v a t.toNat
  have hd0 := hdc.trans hm.2
  have ha := hna hd0 hqc
  have hb := hnb (hda hd0) (hqa hqc)
  have hN' : e.adapter.node (envelope e b) = e.adapter.node (stateAt e rho v i) := by
    rw [cut_envelope]
    exact hb.trans (ha.trans hnc)
  have hK' : e.adapter.self (envelope e b) = rho.ownKey v := hkb.trans (hka.trans (hkc.trans hm.1))
  have hT' : e.adapter.now (envelope e b) = t := htb.trans (hta.trans htc)
  have h := (nodeTick_obs L (envelope e b)).2.2
  rw [hK', hT', hN', hdb (hda hd0)] at h
  dsimp only
  rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, rho.runDuties_cons,
    rho.runDuties_cons, rho.runDuties_cons, rho.runDuties_nil]
  change (if _ then e.adapter.node (envelope e
    (rho.dutyStep v b (engineDuty e (.pollPropose t.toNat))).1) = _ ∧ _
    else e.adapter.node
      (envelope e (rho.dutyStep v b (engineDuty e (.pollPropose t.toNat))).1) = _ ∧ _)
  obtain ⟨hn1, -, -, hd1⟩ := duty_pollPropose L rho v b t.toNat hsel
  rw [hn1, hd1]
  exact h

/-- The node after a tick's two trailing polls: the FG update when due, then the own
`on_attestation`s of what they release, in some order. -/
theorem tick_finish_at (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (t : Time)
    (hsel : rho.ownKey v ∈ rho.sel (engineRole e .poll))
    (hk : e.adapter.self (envelope e nd) = rho.ownKey v) (ht : e.adapter.now (envelope e nd) = t)
    (l : List (FG.Att (Fintype.card V)))
    (hl : e.adapter.node ((e.ops hn).pollBatch (envelope e nd) t.toNat).1 =
      l.foldl (fun n a => (Node.onAttestation n a).1) (if due (envelope e nd) then
        (tickStep (runProposer rho hn) (digestOf e rho) (e.adapter.self (envelope e nd))
          (e.adapter.node (envelope e nd)) (e.adapter.now (envelope e nd))
          (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
      else e.adapter.node (envelope e nd))) :
    e.adapter.node (envelope e (rho.runDuties v nd
      (([.poll t.toNat, .poll t.toNat] : List (ShapeDuty e.skel.Kind)).map (engineDuty e))).1) =
      l.foldl (fun n a => (Node.onAttestation n a).1)
        (if due (envelope e nd) then
        (tickStep (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
          (e.adapter.node (envelope e nd)) t (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
      else e.adapter.node (envelope e nd)) := by
  rw [List.map_cons, List.map_cons, List.map_nil, rho.runDuties_cons, rho.runDuties_cons,
    rho.runDuties_nil]
  obtain ⟨h₁, -, -, hd, -, hq⟩ := duty_poll_obs L rho v nd t.toNat hsel
  dsimp only at h₁ hd hq ⊢
  rw [(poll_clock L rho v _ t.toNat).2.2.2.2 hd hq, h₁, hl, hk, ht]

private theorem cut_now_between [DecidableEq V] (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (t : Time) (j : Nat) (hj : rho.events[j]? = some (.tick v t)) :
    ∀ i, j < i → (∀ k, j < k → k < i → ∀ ev, rho.events[k]? = some ev → ev.time = t) →
      e.adapter.now (stateAt e rho v i) = t := by
  intro i
  induction i with
  | zero => omega
  | succ i ih =>
    intro hi hb
    rw [cut_envelope]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hji | rfl
    · have hclock := ih hji (fun k hjk hki => hb k hjk (by omega))
      rw [cut_envelope] at hclock
      cases he : rho.events[i]? with
      | none =>
        have ht : rho.events.take (i + 1) = rho.events.take i := by
          have hl := List.getElem?_eq_none_iff.mp he
          rw [List.take_of_length_le hl, List.take_of_length_le (by omega)]
        simpa only [Model.Run.stateBefore, ht] using hclock
      | some ev =>
        have ht := hb i hji (by omega) ev he
        rw [rho.stateBefore_succ he]
        cases ev with
        | tick u s =>
          by_cases hu : u = v
          · subst u
            simp only [Model.Run.step, Function.update_self]
            exact (tick_pres L rho v (rho.stateBefore i v) s).2.1.trans ht
          · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hu)] using hclock
        | deliver u o s =>
          by_cases hu : u = v
          · subst u
            simp only [Model.Run.step, Function.update_self]
            exact (deliver_obs L rho v (rho.stateBefore i v) o s).2.1.trans
              ((process_pres L _ (wireOf e o) (Model.digests rho.hash o)).2.1.trans hclock)
          · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hu)] using hclock
        | restart u s =>
          by_cases hu : u = v
          · subst u
            simp only [Model.Run.step, Function.update_self, envelope_eq]
            change e.adapter.now ((cast (congrArg (fun x : ChainShape (pubOf E) O.Id I => x.State)
              e.shape_eq) ((F (pubOf E)).restore (rho.ownKey v)
                ((F (pubOf E)).durable (rho.stateBefore i v).st.1) s)) hn) = t
            rw [cast_restore e.shape_eq]
            exact (restore_obs L _ _ _).2.2.1.trans ht
          · simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hu)] using hclock
    · rw [rho.stateBefore_succ hj]
      simp only [Model.Run.step, Function.update_self]
      exact (tick_pres L rho v (rho.stateBefore j v) t).2.1

private theorem delivery_now [DecidableEq V] (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (hv : rho.ExecutionValid) {i v o t} (he : rho.events[i]? = some (.deliver v o t)) :
    e.adapter.now (stateAt e rho v i) = t := by
  have hm := List.mem_of_getElem? he
  have hh := hv.in_horizon _ hm
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1
    (hv.tick_total v t hh.1 hh.2 (hv.honest_only _ hm) (hv.deliver_awake v o t hm))
  have hkey {a b : Nat} {x y} (ha : rho.events[a]? = some x) (hb : rho.events[b]? = some y)
      (hab : a < b) : Model.Event.keyLe x y := by
    obtain ⟨ha', rfl⟩ := List.getElem?_eq_some_iff.1 ha
    obtain ⟨hb', rfl⟩ := List.getElem?_eq_some_iff.1 hb
    exact List.pairwise_iff_getElem.1 hv.sorted a b ha' hb' hab
  have hji : j < i := by
    rcases lt_trichotomy j i with h | rfl | h
    · exact h
    · rw [he] at hj; cases hj
    · have bad := hkey he hj h
      simp [Model.Event.keyLe, Model.Event.time, Model.Event.phase] at bad
  apply cut_now_between L rho v t j hj i hji
  intro k hjk hki ev hk
  have h₁ := hkey hj hk hjk
  have h₂ := hkey hk he hki
  change t < ev.time ∨ t = ev.time ∧ _ at h₁
  change ev.time < t ∨ ev.time = t ∧ _ at h₂
  exact le_antisymm (h₂.elim le_of_lt fun h => h.1.le) (h₁.elim le_of_lt fun h => h.1.le)

open Classical in
private theorem receipt_group (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (C : WireCodec A e.skel.Kind I e.Body) (hs : List (Header I × Nat)) (y : Fin (Fintype.card V))
    (t : Time) (i : Nat)
    (os : List (ShapeObj (Fintype.card V) e.skel.Kind I e.Body))
    (st : e.State hn) (sub : Nat) (hk : e.adapter.self st = y) (ht : e.adapter.now st = t)
    {r : CutRec A} (hr : r ∈ deliverRecs C (runProposer rho hn) (digestOf e rho)
      hs y t i os (e.adapter.node st) sub) :
    ∃ pre w post ev, os = pre ++ w :: post ∧ canonEvent C hs w = some ev ∧
      let σ := pre.foldl (processOne C e.adapter hs) st
      e.adapter.self σ = y ∧ e.adapter.now σ = t ∧
      ∃ j, r ∈ groupRecs (runProposer rho hn) (digestOf e rho) y
        (e.adapter.node σ) t (Nat.pair i j) ev := by
  obtain ⟨pre, w, post, ev, j, hsplit, hc, _, hg⟩ :=
    mem_deliverRecs_prefix C hs (runProposer rho hn) (digestOf e rho) y t i os _ sub hr
  obtain ⟨hnode, hself, hnow, _⟩ :=
    process_fold_obs L (runProposer rho hn) (digestOf e rho) C hs pre st
  dsimp only at hnode hself hnow
  rw [hk, ht] at hnode
  exact ⟨pre, w, post, ev, hsplit, hc, hself.trans hk, hnow.trans ht, j, by rw [hnode]; exact hg⟩

open Classical in
/-- Each receipt cut comes from an actual `applyCuts` invocation in the delivery fold.
The input is the shape state left by the preceding visited objects, at the delivery time. -/
theorem replay_cut_in_applyCuts [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v o t}
    (he : rho.events[i]? = some (.deliver v o t)) {r : CutRec A} (hr : r ∈ eventCuts e rho i) :
    let hs := Model.digests rho.hash o
    let st := stateAt e rho v i
    ∃ pre w post ev,
      delivered (receiverCodec e rho v) e.adapter hs st (wireOf e o) = pre ++ w :: post ∧
      canonEvent (receiverCodec e rho v) hs w = some ev ∧
      let σ := pre.foldl (processOne (receiverCodec e rho v) e.adapter hs) st
      let result := exec (runProposer rho hn) (digestOf e rho) (e.adapter.self σ)
        (e.adapter.node σ) (e.adapter.now σ) ev
      e.adapter.self σ = rho.ownKey v ∧ e.adapter.now σ = t ∧
      (∃ j, r ∈ groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node σ) t (Nat.pair i j) ev) ∧
      r.label ∈ result.2 ∧
      (processOne (receiverCodec e rho v) e.adapter hs σ w =
          e.adapter.applyCuts σ (some w) result ∨
        ∃ (c : Prop) (dc : Decidable c), processOne (receiverCodec e rho v) e.adapter hs σ w =
          @Adapter.relayIf _ _ _ _ _ _ e.adapter (e.adapter.applyCuts σ none result) c dc w) := by
  rw [eventCuts_deliver e rho i v o t he] at hr
  obtain ⟨pre, w, post, ev, hsplit, hc, hk, ht, hg⟩ := receipt_group L rho _ _ _ _ _ _ _ _
    (cut_obs L rho v i).1 (delivery_now L rho hv he) hr
  refine ⟨pre, w, post, ev, hsplit, hc, hk, ht, hg, ?_, ?_⟩
  · dsimp only
    rw [hk, ht]
    obtain ⟨j, hj⟩ := hg
    rw [groupRecs_eq] at hj
    obtain ⟨k, _, rfl⟩ := List.getElem_of_mem hj
    rw [List.getElem_mapIdx, List.getElem_zip]
    exact List.getElem_mem _
  · dsimp only
    unfold processOne
    rw [hc]
    cases ev with
    | message m => exact Or.inl rfl
    | block b => exact Or.inr ⟨_, _, rfl⟩
    | attestation a => exact Or.inr ⟨True, _, rfl⟩
    | tick x fgDue => unfold canonEvent at hc; split at hc <;> cases hc
    | restart => unfold canonEvent at hc; split at hc <;> cases hc

private theorem receipt_cut_state [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat))
    (y : Fin (Fintype.card V)) (t : Time) (i : Nat)
    (os : List (ShapeObj (Fintype.card V) e.skel.Kind I e.Body))
    (st : e.State hn) (j sub m : Nat) {r : CutRec A}
    (hy : e.adapter.self st = y) (ht : e.adapter.now st = t)
    (hstate : (simTrace e rho).state y j = e.adapter.node st)
    (hcuts : ∀ n < (deliverRecs C (runProposer rho hn) (digestOf e rho)
      hs y t i os (e.adapter.node st) sub).length,
      (allCuts e rho)[j + n]? = (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os (e.adapter.node st) sub)[n]?)
    (hr : (deliverRecs C (runProposer rho hn) (digestOf e rho)
      hs y t i os (e.adapter.node st) sub)[m]? = some r) :
    ∃ pre w post ev, os = pre ++ w :: post ∧ canonEvent C hs w = some ev ∧
      let σ := pre.foldl (processOne C e.adapter hs) st
      let result := exec (runProposer rho hn) (digestOf e rho) y (e.adapter.node σ) t ev
      e.adapter.self σ = y ∧ e.adapter.now σ = t ∧ result.2[r.pos]? = some r.label ∧
      (simTrace e rho).state y (j + m) =
        (result.2.take r.pos).foldl (cutPost y t) (e.adapter.node σ) := by
  obtain ⟨pre, w, post, ev, hsplit, hc, hstep⟩ :=
    indexed_receipt_state e rho C hs os (e.adapter.node st) hcuts hstate hr
  obtain ⟨hnode, hself, hnow, _⟩ :=
    process_fold_obs L (runProposer rho hn) (digestOf e rho) C hs pre st
  dsimp only at hnode hself hnow hstep
  rw [hy, ht] at hnode
  refine ⟨pre, w, post, ev, hsplit, hc, hself.trans hy, hnow.trans ht, ?_⟩
  dsimp only
  rw [hnode]
  exact hstep

/-- The trace state before an indexed receipt cut folds the earlier cuts of its handler,
starting from the shape state left by the preceding visited objects.
For a labelled global cut, take `i := eventOf e rho k`: `eventOf_spec` supplies the cut-map
bounds, and `allCuts_getElem?_add` converts the global lookup to the event's local lookup. -/
theorem simTrace_state_at_cut [DecidableEq V] (L : e.OpLaws due) (laws : e.Lawful due)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid)
    {i v o t} (he : rho.events[i]? = some (.deliver v o t)) {k : Nat} {r : CutRec A}
    (hlo : cutMap e rho i ≤ k) (hr : (eventCuts e rho i)[k - cutMap e rho i]? = some r) :
    let hs := Model.digests rho.hash o
    let st := stateAt e rho v i
    ∃ pre w post ev,
      delivered (receiverCodec e rho v) e.adapter hs st (wireOf e o) = pre ++ w :: post ∧
      canonEvent (receiverCodec e rho v) hs w = some ev ∧
      let σ := pre.foldl (processOne (receiverCodec e rho v) e.adapter hs) st
      let result := exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node σ) t ev
      e.adapter.self σ = rho.ownKey v ∧ e.adapter.now σ = t ∧ result.2[r.pos]? = some r.label ∧
      (simTrace e rho).state (rho.ownKey v) k =
        (result.2.take r.pos).foldl (cutPost (rho.ownKey v) t) (e.adapter.node σ) := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hcuts := allCuts_getElem?_add e rho i
  rw [eventCuts_deliver e rho i v o t he] at hr hcuts
  have h := receipt_cut_state L rho _ _ _ _ i _ _ _ 0 _ (cut_obs L rho v i).1
    (delivery_now L rho hv he)
    (stateAgreement_all laws hv v i hi.le).symm
    (fun n hn' => hcuts n hi hn') hr
  rwa [Nat.add_sub_cancel' hlo] at h

theorem delivery_process [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v o t}
    (he : rho.events[i]? = some (.deliver v o t)) :
    e.adapter.node ((e.ops hn).process (stateAt e rho v i) (wireOf e o)
      (Model.digests rho.hash o)) = deliveryPost e rho v t i o := by
  rw [process_stateAt L, deliveryPost_eq]
  dsimp only [NodeAsChainShape.process]
  have h := (process_fold_obs L (runProposer rho hn) (digestOf e rho) (receiverCodec e rho v)
    (Model.digests rho.hash o)
    (delivered (receiverCodec e rho v) e.adapter (Model.digests rho.hash o) (stateAt e rho v i)
      (wireOf e o))
    (stateAt e rho v i)).1
  dsimp only at h
  rw [(cut_obs L rho v i).1, delivery_now L rho hv he] at h
  exact h

theorem delivery_publish [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v o t}
    (he : rho.events[i]? = some (.deliver v o t))
    (hd : due ((e.ops hn).process (stateAt e rho v i) (wireOf e o) (Model.digests rho.hash o)) =
      false) :
    e.adapter.node (stateAt e rho v (i + 1)) =
      e.adapter.node ((e.ops hn).process (stateAt e rho v i) (wireOf e o)
        (Model.digests rho.hash o)) := by
  rw [cut_envelope rho v (i + 1), cut_envelope]
  rw [rho.stateBefore_succ he]
  simp only [Model.Run.step, Function.update_self]
  have hq := (quietOf_spec L).2.2.2.2.1 _ (wireOf e o) (Model.digests rho.hash o)
    ((cut_quiet L rho hv v i).resolve_left (not_lastRestart_deliver rho hv he))
  rw [cut_envelope] at hd hq
  exact (deliver_obs L rho v (rho.stateBefore i v) o t).2.2.2 hd hq

private theorem cast_proposal_candidates {s q : ChainShape (pubOf E) O.Id I} (h : s = q)
    (st : (compile s).State) (j : Slot) (hj : 0 < j)
    (key : Fin (Fintype.card V)) (sel : (compile s).Role → Finset (Fin (Fintype.card V)))
    (hsel : key ∈ sel (.proposer j))
    (hrole : ∀ header, (q.candidateRole (.propose j hj) (.item header)).getD (.proposer j) =
      .proposer j) :
    let d : (compile s).Duty := cast (congrArg (fun x => (compile x).Duty) h.symm) (.propose j hj)
    let prop := q.propose (cast (congrArg (fun x => x.State) h) st.1) j
    (((compile s).act st d).2.filterMap fun (m, cs) =>
      let r := (compile s).candidateRole d m
      if key ∈ sel r then some (.mk (.signed key r) m cs) else none) =
      (prop.2.map fun (par, info, cs) => cast (congrArg (fun x => (compile x).Object) h.symm)
        (.mk (.signed key (.proposer j)) (.item ⟨par, j, encodeTxs st.2, info⟩) cs)).toList := by
  cases h
  dsimp only
  change ((Option.map _ (s.propose st.1 j).2).toList.filterMap
    (fun (m, cs) => let r := (compile s).candidateRole (.propose j hj) m
      if key ∈ sel r then some (Model.Obj.mk (.signed key r) m cs) else none)) =
    ((s.propose st.1 j).2.map fun (par, info, cs) =>
      (Model.Obj.mk (.signed key (.proposer j)) (.item ⟨par, j, encodeTxs st.2, info⟩) cs :
        (compile s).Object)).toList
  cases hp : (s.propose st.1 j).2 with
  | none => rfl
  | some abc =>
    obtain ⟨par, info, cs⟩ := abc
    have hr : (compile s).candidateRole (.propose j hj)
        (.item ⟨par, j, encodeTxs st.2, info⟩) = .proposer j := hrole _
    change [((Model.Msg.item ⟨par, j, encodeTxs st.2, info⟩, cs) :
      Model.Msg (Header I) s.Body × List (compile s).Object)].filterMap _ = _
    rw (config := { transparency := .default }) [List.filterMap_cons]
    dsimp only
    rw (config := { transparency := .default }) [hr, ite_eq_left hsel]
    rfl

/-- The signed candidate list for a selected proposal duty encodes its proposal result.
Kept for a downstream consumer. -/
theorem proposal_candidates (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.ownKey v ∈ rho.sel (engineRole e (.proposer s))) :
    let d := engineDuty e (.propose s hs)
    rho.signedCandidate v d ((Model.protoOf (compiled F) E).act nd.st d).2 =
      ((((e.ops hn).propose (envelope e nd) s).2).map fun (par, info, cs) =>
        engineObj e (.mk (.signed (rho.ownKey v) (.proposer s))
          (.item ⟨par, s, encodeTxs nd.st.2, info⟩) cs)).toList := by
  dsimp only
  rw [Model.Run.signedCandidate, role_engineDuty, Skeleton.role, ite_eq_left hsel]
  have hsel' : rho.ownKey v ∈ rho.sel (.proposer s) := by
    exact engineRole_proposer e s ▸ hsel
  simp only [engineDuty_eq, engineObj_eq, envelope_eq]
  have h := cast_proposal_candidates e.shape_eq nd.st s hs (rho.ownKey v) rho.sel hsel'
    (L.proposer_role s hs)
  simp only [shape, familyOps, dite_eq_left hn] at h
  exact h

/-- Duties keep the engine's mempool snapshot. Kept for a downstream consumer. -/
theorem duties_mempool (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E))
    (ds : List ((Model.protoOf (compiled F) E).Duty)) :
    (rho.runDuties v nd ds).1.st.2 = nd.st.2 := by
  induction ds generalizing nd with
  | nil => rfl
  | cons d ds ih =>
    rw [rho.runDuties_cons]
    change (rho.runDuties v (rho.dutyStep v nd d).1 ds).1.st.2 = _
    rw [ih, rho.dutyStep_eq]
    split
    · apply Model.releaseAll_invariant (fun st : (Model.protoOf (compiled F) E).State =>
        st.2 = nd.st.2)
      · intro st o hs _ h; exact h
      · cases d <;> rfl
    · rfl

end Encoding.OpLaws

/-- Both release guards for the actual selected proposal, proved by the instance. -/
def Encoding.ProposalReady [DecidableEq V] (e : Encoding F E p hN hn A) : Prop :=
  ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
    ∀ s (hs : 0 < s), e.skel.proposeAt t = [.propose s hs] →
    rho.ownKey v ∈ rho.sel (engineRole e (.proposer s)) →
    let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
    ∀ par info cs, ((e.ops hn).propose (envelope e pre) s).2 = some (par, info, cs) →
    let o := engineObj e (.mk (.signed (rho.ownKey v) (.proposer s))
      (.item ⟨par, s, encodeTxs pre.st.2, info⟩) cs)
    Model.releasable pre.seen o = true ∧
      (Model.protoOf (compiled F) E).dependencies.ready (Model.closure pre.seen) o = true

/-- Unpack readiness at the actual proposal duty and its signed candidate. -/
theorem Encoding.proposalReady_iff [DecidableEq V] : e.ProposalReady ↔
  ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
    ∀ s (hs : 0 < s), e.skel.proposeAt t = [.propose s hs] →
    rho.ownKey v ∈ rho.sel (engineRole e (.proposer s)) →
    let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
    ∀ par info cs, ((e.ops hn).propose (envelope e pre) s).2 = some (par, info, cs) →
    let o := engineObj e (.mk (.signed (rho.ownKey v) (.proposer s))
      (.item ⟨par, s, encodeTxs pre.st.2, info⟩) cs)
    Model.releasable pre.seen o = true ∧
      (Model.protoOf (compiled F) E).dependencies.ready (Model.closure pre.seen) o = true := by
  rfl

namespace Encoding.OpLaws

/-- After the clock and any duties of a tick, the envelope has the node's key and the tick time.
Kept for a downstream consumer. -/
theorem proposal_clock [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (v : V) (i : Nat) (t : Time)
    (ds : List (ShapeDuty e.skel.Kind)) :
    let r := envelope e (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      (ds.map (engineDuty e))).1
    e.adapter.self r = rho.ownKey v ∧ e.adapter.now r = t := by
  have ⟨hk, ht, _⟩ := duties_pres L rho v (afterClock rho (rho.stateBefore i v) v t) ds
  dsimp only at hk ht ⊢
  rw [hk, ht, envelope_clock]
  have h := L.clock_obs (envelope e (rho.stateBefore i v)) t
  have hself := (cut_obs L rho v i).1
  rw [cut_envelope] at hself
  exact ⟨h.2.1.trans hself, h.2.2.1⟩

theorem proposal_finish [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (v : V) (i : Nat) (t : Time) :
    let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
    let post := (rho.runDuties v pre ((e.skel.proposeAt t).map (engineDuty e))).1
    e.adapter.self (envelope e post) = rho.ownKey v ∧ e.adapter.now (envelope e post) = t := by
  dsimp only
  rw [← rho.runDuties_append_fst, ← List.map_append]
  exact proposal_clock L rho v i t _

end Encoding.OpLaws

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
