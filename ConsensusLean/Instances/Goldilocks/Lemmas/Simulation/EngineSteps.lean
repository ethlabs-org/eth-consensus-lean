module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineState
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

public section

/-! # Goldilocks Simulation: the engine-side steps

What a valid engine run (`ExecutionValid`) does to the shape's state at each event, stated on
`stateAt`: the node state inside the shape's state after an event of an honest node is the
node's handler applied to the node state before it (a tick at a public time with the encoded
mempool, a delivery one `canonEvent` after the other, a restart), the shape's clock is the time of
the node's last tick or restart, and the interface's obligations: at most two bodies
pending at a tick, a proposal carries only released objects (so `releasable` admits it), and the
digests the engine passes with a block object map its header to its root.
`EngineState` has the shape preservation, `stateAt` across an event, the invariants of every
engine cut, the duties of a tick and the clock at a delivery; this module the node state.

The route to the node state across a tick: the engine's tick runs the duties of the time (two
poll steps, the node's tick, the slot proposal if due, two poll steps) and then the gossip, each
through `releaseAll` of the candidates it signs. A poll step's own candidate is a data body that
`recordOwn` ignores, the gossip's candidates are unsigned, so only the proposal duty changes the
node state through its released block. `atProposal` names the engine node at that duty (after the
clock, the two leading poll steps and the node's tick); `proposal_releasable` is stated on it,
because the proposal the engine releases is `propose` of that node, not of the node before the
tick. `node_of_tick_public` then matches `tick_node_eq` against the node's `onTick`.

A delivery runs `process`, then the delivery's poll step (`deliverOrder := [.poll]`, at `t ≥ 0`)
and the gossip (`Model.Run.deliver`); the FG update is never due there, so the poll only pops the
outbox, and the gossip's candidates are unsigned (`deliver_pres`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams Vote Payload)

variable {binding : VoteBinding}

variable {sp : ACParams}

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## The node state across a delivery -/

/-- The node state after a delivery of the objects `os` at time `t` from `st`: the handler of
each canonical object in order, nothing for a dropped object (the state `deliverRecs` threads). -/
noncomputable def deliverState (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (io : VoteAuth sp.n binding)
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) :
    List (Wire sp.n binding) → NodeState (goldilocksNode sp) → NodeState (goldilocksNode sp)
  | [], st => st
  | o :: os, st =>
      match canonEvent sp io hs o with
      | some e => deliverState proposer dg io hs self t os (exec proposer dg self st t e).1
      | none => deliverState proposer dg io hs self t os st

/-- The canonical event of a wire object, if any, is a block, a message or an attestation. -/
theorem canonEvent_cases (io : VoteAuth sp.n binding) hs (o : Wire sp.n binding) :
    canonEvent sp io hs o = none ∨ (∃ B, canonEvent sp io hs o = some (.block B)) ∨
      (∃ v, canonEvent sp io hs o = some (.message v)) ∨
      (∃ a, canonEvent sp io hs o = some (.attestation a)) := by
  rw [canonEvent_eq]
  split <;> simp

/-- Processing one delivered object runs the handler of its canonical event, nothing if it has none.
-/
theorem processOne_node (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (io : VoteAuth sp.n binding) hs
    (st : State sp binding) o :
    (processOne io hs st o).node =
      match canonEvent sp io hs o with
      | some e => (exec proposer dg st.self st.node st.now e).1
      | none => st.node := by
  rcases canonEvent_cases io hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩ <;>
    simp [processOne_eq, h, relayIf_node, apply_node, exec]

/-- Processing a list of delivered objects runs `deliverState` on the node state. -/
theorem foldl_processOne_node (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (io : VoteAuth sp.n binding) hs
    (os : List (Wire sp.n binding)) (st : State sp binding) :
    (os.foldl (processOne io hs) st).node =
      deliverState proposer dg io hs st.self st.now os st.node := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih =>
    rw [List.foldl_cons, ih, processOne_self, processOne_now, processOne_node proposer dg]
    rcases canonEvent_cases io hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩ <;>
      simp only [deliverState, h]

/-- **`SimulatesAt.deliver`'s node step.** An engine delivery to an honest node runs the handlers of
the delivered canonical objects in order on the node state before it, with the digests the engine
passes. -/
theorem node_of_deliver (hv : rho.ExecutionValid) (v : V) (_hv' : v ∉ rho.faultyAt 0) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (t : Time)
    (he : rho.events[i]? = some (.deliver v o t))
    (hr : HeldRefused (S.release (pubOf E)) (stateAt S rho hn v i)) :
    (stateAt S rho hn v (i + 1)).node =
      deliverState (runProposer S rho hn) (digestOf S rho) (stateAt S rho hn v i).voteIO
        (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (stateAt S rho hn v i).voteIO (Model.digests rho.hash o)
          (stateAt S rho hn v i) o) (stateAt S rho hn v i).node := by
  have hpre := (fgDue_eq_false S rho hn v i)
  rw [stateAt_deliver S rho hn v he]
  refine (deliver_pres S rho hn
    (fun st => st.node = (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node ∧
      st.fgDue = false ∧ HeldRefused (S.release (pubOf E)) st)
    (fun st t (h : _ ∧ _ ∧ HeldRefused (S.release (pubOf E)) st) =>
      ⟨(pollBatch_node_of_fgDue st t h.2.1 (pollFlush_eq_nil h.2.2)).trans h.1,
        pollBatch_fgDue st t, heldRefused_pollBatch_of_refused h.2.2 t⟩)
    (fun st m cs hs (h : _ ∧ _ ∧ HeldRefused (S.release (pubOf E)) st) =>
      ⟨(recordOwn_none_node st _ _ hs).trans h.1, (recordOwn_fgDue st _ hs).trans h.2.1,
        heldRefused_of_held (recordOwn_self st (.mk .none m cs) hs)
          (recordOwn_now st (.mk .none m cs) hs) (recordOwn_held st (.mk .none m cs) hs) h.2.2⟩)
    v _ o t ⟨by rw [stateAt_eq],
      (process_fgDue _ _ _).trans (by simpa only [stateAt_eq] using hpre),
      heldRefused_of_held (process_self _ _ _) (process_now _ _ _) (process_held _ _ _)
        (by simpa only [stateAt_eq] using hr)⟩).1.trans ?_
  rw [process_eq (stateAt S rho hn v i) o (Model.digests rho.hash o)]
  refine (foldl_processOne_node (runProposer S rho hn) (digestOf S rho) _ _ _ _).trans ?_
  rw [self_eq_ownKey, now_eq_lastClock S rho hn hv, lastClock_of_deliver S rho hv v he]

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
theorem rootOf_digests_of_mem (o : (Model.protoOf (compiled (goldilocks S)) E).Object)
    (h : Header Info) (hm : h ∈ o.parts.filterMap Model.Obj.item?) :
    rootOf (Model.digests rho.hash o) h = some (rho.hash h) :=
  find?_map_pair rho.hash h _ hm

omit [DecidableEq V] in
/-- The engine's digests of an item object map its header to the engine's hash of it. -/
theorem rootOf_digests_item (a : Model.Auth (Fintype.card V) (ShapeRole S.vote.Kind))
    (h : Header Info)
    (cs : List (Wire (Fintype.card V) S.vote)) :
    rootOf (Model.digests rho.hash (.mk a (.item h) cs)) h = some (rho.hash h) :=
  rootOf_digests_of_mem S rho _ h
    (List.mem_filterMap.2 ⟨.mk a (.item h) cs, by simp [Model.Obj.parts], rfl⟩)

/-! ## Slots -/

/-- A time is in slot `s` of a grid starting at `0` exactly when it is the slot's start. -/
theorem slotAt?_zero_iff (G : TimeGrid) (t : Time) (s : Slot) :
    G.slotAt? 0 t = some s ↔ t = G.slotTime s := by
  have hL := G.slotLen_pos
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
theorem Skeleton.proposeAt_cases {n : Nat} (sk : Skeleton n) (t : Time) :
    (sk.proposeAt t = [] ∧ ∀ s, 0 < s → t ≠ sk.grid.slotTime s) ∨
      ∃ s, ∃ h : 0 < s, sk.proposeAt t = [.propose s h] ∧ t = sk.grid.slotTime s := by
  unfold Skeleton.proposeAt
  match hs : sk.grid.slotAt? 0 t with
  | none =>
    left
    refine ⟨rfl, fun s hs' ht => ?_⟩
    have := (slotAt?_zero_iff sk.grid t s).2 ht
    rw [hs] at this
    cases this
  | some s =>
    by_cases h : 0 < s
    · right
      exact ⟨s, h, by simp [h], (slotAt?_zero_iff sk.grid t s).1 hs⟩
    · left
      refine ⟨by simp [h], fun s' hs' ht => ?_⟩
      have := (slotAt?_zero_iff sk.grid t s').2 ht
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
      (skeleton (pubOf E) S.vote).grid.slotTime s := by
  simp only [skeleton, TimeGrid.slotTime, pubOf]
  ring

omit [DecidableEq V] in
/-- At the start of slot `s > 0`, a key proposes exactly when it is the slot's proposer. -/
theorem proposes_iff (proposer : Nat → Fin (Fintype.card V))
    (self : Fin (Fintype.card V)) (s : Nat) (hs : 0 < s) :
    Proposes (P := (S.params (pubOf E) hn).toParams) proposer self
        ((S.params (pubOf E) hn).toParams.slotTime s) ↔
      proposer s = self := by
  unfold Proposes
  rw [slotOf_slotTime]
  exact ⟨fun h => h.2.2, fun h => ⟨hs, rfl, h⟩⟩

omit [DecidableEq V] in
/-- A key proposes at no time that starts no positive slot. -/
theorem not_proposes (proposer : Nat → Fin (Fintype.card V))
    (self : Fin (Fintype.card V)) (t : Time)
    (h : ∀ s, 0 < s → t ≠ (S.params (pubOf E) hn).toParams.slotTime s) :
    ¬ Proposes (P := (S.params (pubOf E) hn).toParams) proposer self t :=
  fun hp => h _ hp.1 hp.2.1


/-! ## The selection of a valid run -/

omit [DecidableEq V] in
/-- In an admitted run, the proposer role selects exactly `runProposer`. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {runProposer S rho hn s} := by
  open NodeAsChainShape.CanonicalTrace in
  rw [(runProposer_digestOf S rho hn).1,
    ← engineRole_proposer (traceEncoding S hn) s]
  exact traceEncoding_induction S hn
    (fun e _ _ => rho.sel (NodeAsChainShape.CanonicalTrace.engineRole e (.proposer s)) =
      {NodeAsChainShape.CanonicalTrace.runProposer rho hn s})
    (by
      intro e _
      exact NodeAsChainShape.CanonicalTrace.selValid_proposer e rho hsel s rfl)

/-! ## The proposal duty -/

omit [DecidableEq V] in
/-- The candidate of the engine's `propose` duty is the shape's proposal wrapped as a block item
with the node's mempool. -/
theorem act_propose_snd (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (s : Slot)
    (hs : 0 < s) :
    ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs)).2 =
      ((propose (shapeOf S hn nd) s).2.map
        (fun r => (.item ⟨r.1, s, encodeTxs nd.st.2, r.2.1⟩, r.2.2))).toList := by
  change (Option.map _ ((goldilocks S (pubOf E)).propose nd.st.1 s).2).toList = _
  rw [goldilocks_propose_eq S _ nd.st.1 s, dite_eq_left hn]
  rfl

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
      mkBlock (A := goldilocksNode (S.params (pubOf E) hn)) (digestOf S rho) k fg t x
        H p := by
  subst hslot
  simp only [blockOf_eq, mkBlock, digestOf_eq]
  erw [dgOf_eq]
  rw [parentRoot_parentRef]

omit [DecidableEq V] in
/-- **The proposal duty is the node's proposal step.** At the start of slot `s` of which the node is
the selected proposer, when the proposal carries only released objects, the engine's `propose` duty
step records the block the node's `tickStep .proposal` makes, withholding the shape's held queue;
otherwise both do nothing. -/
theorem dutyStep_propose_node (v : V) (nd : Model.Node (Model.protoOf (compiled
    (goldilocks S)) E))
    (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {runProposer S rho hn s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (pubOf E) hn).toParams.slotTime s)
    (hrel : rho.ownKey v ∈ rho.sel (.proposer s) →
      ∀ par info cs, (propose (shapeOf S hn nd) s).2 = some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure nd.seen) :
    (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).node =
      (tickStep (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (shapeOf S hn nd).node (shapeOf S hn nd).now
        (encodeTxs nd.st.2) .proposal).1 := by
  have hact2 := act_propose_snd S hn nd s hs
  have hact1 := shapeOf_act_propose S hn nd.st s hs
  unfold Model.Run.dutyStep
  generalize (Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs) =
      a at hact1 hact2
  have hP : Proposes (P := (S.params (pubOf E) hn).toParams) (runProposer S rho hn) (rho.ownKey v)
        (shapeOf S hn nd).now ↔
      runProposer S rho hn s = (shapeOf S hn nd).self := by
    rw [hst, proposes_iff S hn (runProposer S rho hn) _ s hs, hself]
  by_cases hp : runProposer S rho hn s = (shapeOf S hn nd).self
  · have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
      rw [hsel]
      exact Finset.mem_singleton.2 (hp.trans hself).symm
    have hrel := hrel hmem
    simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
      .proposer s from rfl, hmem, ↓reduceIte]
    simp only [propose_eq] at hact1 hact2 hrel
    simp only [tickStep, hP.2 hp, ite_true]
    rcases hr : (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with _ | ⟨d, p⟩
    · simp only [hr] at hact1 hact2
      rw [hact2]
      simp only [Option.map_none, Option.toList_none, Model.Run.signedCandidate]
      erw [List.filterMap_nil]
      simp only [ite_self, Model.releaseAll]
      change (a.1.1 hn).node = _
      rw [hact1]
    · simp only [hr] at hact1 hact2 hrel
      rw [hact2]
      have hrole : (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
          .proposer s := rfl
      have hcrole : ∀ h, (Model.protoOf (compiled (goldilocks S)) E).candidateRole
          (.propose s hs) (.item h) = .proposer s := fun h => by
        change (S.vote.candidateRole _ (.propose s hs) (.item h)).getD (.proposer s) = .proposer s
        exact congrArg (Option.getD · _) (candidateRole_item _ _ _ h)
      simp only [Option.map, Option.toList_some, Model.Run.signedCandidate, hrole]
      erw [List.filterMap_cons, List.filterMap_nil, hcrole]
      have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
        rw [hsel]
        exact Finset.mem_singleton.2 (hp.trans hself).symm
      simp only [hmem, ↓reduceIte]
      unfold Model.releaseAll
      rw [ite_eq_left (Bool.and_eq_true_iff.2 ⟨?_, ?_⟩)]
      · change (recordOwn (a.1.1 hn) _ _).node = _
        rw [hact1]
        refine (congrArg State.node (recordOwn_eq _ _ _)).trans ?_
        simp only [decodeInfo_encodeInfo]
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
      · exact dependencies_item _ _ _ _ _
  · simp only [tickStep, hP.not.2 hp, ite_false]
    have hmem : rho.ownKey v ∉ rho.sel (.proposer s) := by
      rw [hsel, Finset.mem_singleton]
      intro heq
      exact hp (heq.symm.trans hself.symm)
    simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
      .proposer s from rfl, hmem, ↓reduceIte]


/-! ## The node state across a tick -/

/-- The poll runs the FG update exactly when it is due. -/
theorem poll_node_eq {release : Fin sp.n → Time → Bool} (st : State sp binding) (t : Time) :
    (poll st t release).1.node = if st.fgDue then (fgUpdate st release).node else st.node := by
  cases h : st.fgDue
  · exact poll_node_of_fgDue st t h
  · unfold poll
    simp only [h, ite_true]
    split <;> rfl

/-- The node's tick at a public time runs the AC's tick on the node state. -/
theorem nodeTick_node_public (st : State sp binding) (h : sp.toParams.IsPublic st.now)
    {sign : Fin sp.n → Time → Bool} :
    (nodeTick st sign).node = (Node.acCall st.self st.node st.now .tick).1 := by
  rw [nodeTick_eq (sign := _)]
  rw [ite_eq_left h]
  rfl

/-- `ac_to_fg` and `fg_attest` do not read the pool. -/
private theorem tickStep_fgUpdate_atts (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (n : NodeState (goldilocksNode sp)) (t : Time) (x : Nat) (l : List (FG.Att sp.n)) :
    (Node.tickStep proposer dg self { n with fg := { n.fg with atts := l } } t x .fgUpdate).1 =
      { (Node.tickStep proposer dg self n t x .fgUpdate).1 with
        fg := { (Node.tickStep proposer dg self n t x .fgUpdate).1.fg with atts := l } } := by
  have hA : Node.acToFG { n with fg := { n.fg with atts := l } } t =
      ({ (Node.acToFG n t).1 with fg := { n.fg with atts := l } }, (Node.acToFG n t).2) := rfl
  simp only [Node.tickStep, hA]
  rcases h : (Node.acToFG n t).2.2 with _ | C
  · rfl
  · simp only [Node.attest]
    have hB : Store.attest { n.fg with atts := l } (Node.acToFG n t).1.record self C =
        Store.attest (Node.acToFG n t).1.fg (Node.acToFG n t).1.record self C := rfl
    dsimp only at hB
    rw [hB]
    rcases (Node.acToFG n t).1.fg.attest (Node.acToFG n t).1.record self C with _ | ⟨a, Λ'⟩ <;> rfl

/-- The FG update keeps the FG store. -/
theorem tickStep_fgUpdate_fg (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (n : NodeState (goldilocksNode sp)) (t : Time) (x : Nat) :
    (Node.tickStep proposer dg self n t x .fgUpdate).1.fg = n.fg := by
  simp only [Node.tickStep]
  split
  · rfl
  · simp only [Node.attest]; split <;> rfl

/-- **The own `on_attestation`s commute with the FG update**: it neither reads nor writes the
pool except through `on_attestation`. -/
private theorem tickStep_fgUpdate_foldl (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n) (t : Time) (x : Nat)
    (l : List (FG.Att sp.n)) (n : NodeState (goldilocksNode sp)) :
    (Node.tickStep proposer dg self (l.foldl (fun n a => (Node.onAttestation n a).1) n) t x
      .fgUpdate).1 =
      l.foldl (fun n a => (Node.onAttestation n a).1)
        (Node.tickStep proposer dg self n t x .fgUpdate).1 := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    have hfg := tickStep_fgUpdate_fg proposer dg self n t x
    by_cases ha : a ∈ n.fg.atts
    · simp only [Node.onAttestation, Store.onAttestation, hfg, ha, ↓reduceIte]
      change (Node.tickStep proposer dg self n t x .fgUpdate).1 = _
      generalize (Node.tickStep proposer dg self n t x .fgUpdate).1 = m at hfg ⊢
      cases m; subst hfg; rfl
    · simp only [Node.onAttestation, Store.onAttestation, hfg, ha, ↓reduceIte]
      rw [tickStep_fgUpdate_atts]
      generalize (Node.tickStep proposer dg self n t x .fgUpdate).1 = m at hfg ⊢
      cases m; subst hfg; rfl

/-- The shape's FG update is the node's `tickStep .fgUpdate`, for any digests and mempool, then,
when the release schedule allows release at the node's time, the own `on_attestation` of the
attestation it signs. -/
theorem fgUpdate_node {release : Fin sp.n → Time → Bool} (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat)
    (st : State sp binding) :
    (fgUpdate st release).node =
      (if release st.self st.now then (fgSigned st).toList else []).foldl
        (fun n a => (Node.onAttestation n a).1)
        (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).1 := by
  rw [fgUpdate_eq st release, fgSigned_eq]
  simp only [Node.tickStep]
  rcases h : (Node.acToFG st.node st.now).2.2 with _ | C
  · simp
  · simp only [Node.attest, Option.bind_some]
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩
    · simp
    · cases release st.self st.now <;> rfl

/-- **The batch poll's node state**: the flush's own `on_attestation`s, then the FG update when
due, is the node's `tickStep .fgUpdate` followed by the own `on_attestation`s of the flushed
attestations, oldest first, and then of the one the FG update signs when the schedule releases
it. Processing an attestation changes only the pool, which `ac_to_fg` and `fg_attest` neither
read nor write (`tickStep_fgUpdate_foldl`), so the flush commutes past the FG update. -/
theorem pollBatch_node_eq {release : Fin sp.n → Time → Bool} (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat) (st : State sp binding)
    (t : Time) : (pollBatch st t release).1.node =
      (pollFlush st release ++
        if (st.fgDue && release st.self st.now) = true then (fgSigned st).toList else []).foldl
        (fun n a => (Node.onAttestation n a).1)
        (if st.fgDue then (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).1
          else st.node) := by
  rw [pollBatch_fst, pollFlush_eq]
  split
  · rw [poll_node_eq, heldDrain_fgDue]
    cases hd : st.fgDue
    · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
        heldDrain_node]
    · simp only [↓reduceIte, Bool.true_and]
      rw [fgUpdate_node proposer dg x, heldDrain_self, heldDrain_now, fgSigned_heldDrain,
        heldDrain_node, tickStep_fgUpdate_foldl, List.foldl_append]
  · rw [poll_node_eq, List.nil_append]
    cases hd : st.fgDue
    · simp
    · simp only [↓reduceIte, Bool.true_and]
      rw [fgUpdate_node proposer dg x]

omit [DecidableEq V] in
/-- A duty keeps the mempool. -/
theorem act_mempool (st : (Model.protoOf (compiled (goldilocks S)) E).State)
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    ((Model.protoOf (compiled (goldilocks S)) E).act st d).1.2 = st.2 := by
  cases d <;> rfl

omit [DecidableEq V] in
/-- `releaseAll` keeps the mempool. -/
private theorem releaseAll_mempool (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (cs : List (Model.protoOf (compiled (goldilocks S)) E).Object),
      (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd cs).1.st.2 =
          nd.st.2
  | _, [] => rfl
  | nd, c :: cs => by
    unfold Model.releaseAll
    split
    · exact releaseAll_mempool k _ cs
    · exact releaseAll_mempool k nd cs

omit [DecidableEq V] in
/-- Running duties keeps the mempool. -/
theorem runDuties_mempool (v : V) :
    ∀ (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)),
      (rho.runDuties v nd ds).1.st.2 = nd.st.2
  | [], _ => rfl
  | d :: ds, nd => by
    rw [runDuties_fst_cons, runDuties_mempool v ds]
    unfold Model.Run.dutyStep
    split
    case isFalse => rfl
    rw [releaseAll_mempool]
    exact act_mempool S _ d

omit [DecidableEq V] in
/-- `releaseAll` of candidates whose `recordOwn` keeps the node state keeps the node state. -/
theorem releaseAll_node_eq (k : Fin (Fintype.card V)) :
    ∀ (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (cs : List (Model.protoOf (compiled (goldilocks S)) E).Object),
      (∀ c ∈ cs, ∀ (st : State (S.params (pubOf E) hn) S.vote) hs,
        (recordOwn st c hs).node = st.node) →
      (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
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
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time) :
    (shapeOf S hn (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash k nd
      (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd.st t)).1).node =
      (shapeOf S hn nd).node := by
  apply releaseAll_node_eq
  intro c hc st hs
  obtain ⟨mc, _, rfl⟩ := List.mem_map.1 hc
  exact recordOwn_none_node st _ _ hs

omit [DecidableEq V] in
/-- The tick of an awake node: the duties from the clocked node, then the gossip. -/
theorem tick_of_awake (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hw : E.awake v t = true) :
    (rho.tick nd v t).1 =
      (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v)
        (rho.runDuties v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
          (Model.mempool rho.inbox v t), nd.seen⟩
          ((Model.protoOf (compiled (goldilocks S)) E).duties t)).1
        (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E)
          (rho.runDuties v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
            (Model.mempool rho.inbox v t), nd.seen⟩
            ((Model.protoOf (compiled (goldilocks S)) E).duties t)).1.st t)).1 := by
  unfold Model.Run.tick
  simp only [hw, ite_true]

/-- The node of validator `v` at its proposal duty of a tick at `t` from `nd`: after the clock,
the two leading poll steps and the node's tick. -/
noncomputable def atProposal (v : V) (nd : Model.Node (Model.protoOf (compiled
    (goldilocks S)) E))
    (t : Time) : Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
  (rho.runDuties v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
    (Model.mempool rho.inbox v t), nd.seen⟩
    ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
      List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1

omit [DecidableEq V] in
/-- `atProposal` unfolded: the engine's `runDuties` of the two leading polls and the proposal
poll on the clocked node (for modules that cannot see its body). -/
theorem atProposal_eq (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) :
    atProposal S rho v nd t =
      (rho.runDuties v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st t
        (Model.mempool rho.inbox v t), nd.seen⟩
        ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
          List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1 := by rfl

omit [DecidableEq V] in
/-- The shape at the proposal duty: `nodeTick` of two batch polls of the clocked state. -/
theorem atProposal_shape (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    shapeOf S hn (atProposal S rho v nd t) =
      { nodeTick (pollBatch (pollBatch { nd.st.1 hn with now := t, ticked := false } t.toNat
        (S.release (pubOf E))).1 t.toNat (S.release (pubOf E))).1 (S.sign (pubOf E)) with
        ticked := true } := by
  change shapeOf S hn (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v _ (.poll t.toNat)).1
    (.poll t.toNat)).1 (.pollPropose t.toNat)).1 = _
  rw [dutyStep_pollPropose _ _ _ _ _ _ hsel, dutyStep_poll _ _ _ _ _ _ hsel,
    dutyStep_poll _ _ _ _ _ _ hsel]
  rfl

omit [DecidableEq V] in
/-- The key at the proposal duty is the key before the tick. -/
theorem atProposal_self (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (atProposal S rho v nd t)).self = (nd.st.1 hn).self := by
  rw [atProposal_shape _ _ _ _ _ _ hsel, nodeTick_self, pollBatch_self, pollBatch_self]

omit [DecidableEq V] in
/-- The clock at the proposal duty is the tick time. -/
theorem atProposal_now (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (atProposal S rho v nd t)).now = t := by
  rw [atProposal_shape _ _ _ _ _ _ hsel, nodeTick_now, pollBatch_now, pollBatch_now]

omit [DecidableEq V] in
/-- At a public time the node's tick sets the FG duty from the signing calendar. -/
theorem atProposal_fgDue (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (atProposal S rho v nd t)).fgDue = S.sign (pubOf E) (nd.st.1 hn).self t := by
  rw [atProposal_shape _ _ _ _ _ _ hsel]
  rw [nodeTick_eq (sign := _)]
  rw [ite_eq_left (by rw [pollBatch_now, pollBatch_now]; exact hp)]
  dsimp only
  rw [pollBatch_self, pollBatch_self, pollBatch_now, pollBatch_now]

omit [DecidableEq V] in
/-- The mempool at the proposal duty is the tick's mempool. -/
theorem atProposal_mempool (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) : (atProposal S rho v nd t).st.2 = Model.mempool rho.inbox v t := by
  unfold atProposal
  rw [runDuties_mempool]
  rfl

omit [DecidableEq V] in
/-- With no FG update due before the tick, the node state at the proposal duty is `nodeTick` of the
clocked state. -/
theorem atProposal_node (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hf : (nd.st.1 hn).fgDue = false)
    (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (atProposal S rho v nd t)).node =
      (nodeTick { nd.st.1 hn with now := t } (S.sign (pubOf E))).node := by
  rw [atProposal_shape _ _ _ _ _ _ hsel]
  change (nodeTick (pollBatch (pollBatch { nd.st.1 hn with now := t, ticked := false } t.toNat
    (S.release (pubOf E))).1 t.toNat (S.release (pubOf E))).1 (S.sign (pubOf E))).node = _
  have h1 : (pollBatch (pollBatch { nd.st.1 hn with now := t, ticked := false } t.toNat
      (S.release (pubOf E))).1 t.toNat (S.release (pubOf E))).1.node = (nd.st.1 hn).node := by
    rw [pollBatch_node_of_fgDue _ _ (pollBatch_fgDue _ _)
        (pollFlush_of_unticked _ (by rw [pollBatch_ticked])),
      pollBatch_node_of_fgDue { nd.st.1 hn with now := t, ticked := false } _ hf
        (pollFlush_of_unticked _ rfl)]
  have h2 : (pollBatch (pollBatch { nd.st.1 hn with now := t, ticked := false } t.toNat
      (S.release (pubOf E))).1 t.toNat (S.release (pubOf E))).1.self = (nd.st.1 hn).self := by
    rw [pollBatch_self, pollBatch_self]
  have h3 : (pollBatch (pollBatch { nd.st.1 hn with now := t, ticked := false } t.toNat
      (S.release (pubOf E))).1 t.toNat (S.release (pubOf E))).1.now = t := by
    rw [pollBatch_now, pollBatch_now]
  rw [nodeTick_eq (sign := _)]
  rw [h3]
  by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
  · simp only [hp, ite_true, apply_node, h1, h2]
    rw [nodeTick_eq (sign := _)]
    simp [hp, apply_node]
  · simp only [hp, ite_false, h1]
    rw [nodeTick_eq (sign := _)]
    simp [hp]

omit [DecidableEq V] in
/-- The node after the whole tick, in terms of the node at the proposal duty: the proposal if
due, a poll step, a poll step, the gossip. -/
theorem tick_node_eq (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true)
    (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (rho.tick nd v t).1).node =
      (pollBatch (pollBatch (shapeOf S hn (rho.runDuties v (atProposal S rho v nd t)
          ((skeleton (pubOf E) S.vote).proposeAt t)).1) t.toNat (S.release (pubOf E))).1
        t.toNat (S.release (pubOf E))).1.node := by
  -- The goal's duty lists are typed at `ShapeDuty`, the step lemmas at the engine's `Duty`: stated
  -- as local equations on the goal's own terms, the steps rewrite with plain `rw` (an `erw` would
  -- try every projection of the goal at default transparency).
  have hpoll : ∀ (nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (x : Nat),
      shapeOf S hn (rho.runDuties v nd' [.poll x]).1 =
        (pollBatch (shapeOf S hn nd') x (S.release (pubOf E))).1 :=
    fun nd' x => dutyStep_poll S rho hn v nd' x hsel
  have hinit : ∀ nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
      (rho.runDuties v nd' (dutiesInit S t)).1 =
        (rho.runDuties v (rho.runDuties v (rho.runDuties v nd'
          ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
            List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
          ((skeleton (pubOf E) S.vote).proposeAt t)).1 [.poll t.toNat]).1 := fun nd' =>
    (runDuties_fst_append S rho v nd' _ _).trans
      (congrArg (fun x => (rho.runDuties v x [.poll t.toNat]).1)
        (runDuties_fst_append S rho v nd' _ _))
  rw [tick_of_awake S rho v nd t hw, gossip_node_eq, duties_eq S t ht, runDuties_fst_append, hpoll,
    hinit, hpoll]
  rfl

/-- The AC-tick step is the AC's tick. -/
theorem tickStep_acTick (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp)) (t : Time) (x : Nat) :
    (Node.tickStep proposer dg self st t x .acTick).1 = (Node.acCall self st t .tick).1 := rfl

/-- The proposal step of a key that does not propose at `t` keeps the node state. -/
theorem tickStep_proposal_not (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp)) (t : Time) (x : Nat)
    (h : ¬ Proposes (P := sp.toParams) proposer self t) :
    (Node.tickStep proposer dg self st t x .proposal).1 = st := by
  unfold Node.tickStep
  simp only [h, ite_false]

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn` and `propose` is preserved by the
engine's `propose` duty step. -/
theorem dutyStep_propose_pres (Q : State (S.params (pubOf E) hn) S.vote → Prop)
    (hrec : ∀ st o hs, Q st → Q (recordOwn st o hs))
    (hprop : ∀ st s, Q st → Q (propose st s).1) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (h : Q (shapeOf S hn nd)) : Q (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1) := by
  unfold Model.Run.dutyStep
  split
  case isFalse => exact h
  apply releaseAll_pres S rho hn Q hrec
  have := hprop _ s h
  rw [← shapeOf_act_propose S hn nd.st s hs] at this
  exact this

end Engine

end Consensus.Goldilocks.Simulation

end
