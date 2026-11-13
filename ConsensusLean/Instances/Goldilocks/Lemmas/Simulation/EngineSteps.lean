module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineState

public section

/-! # Goldilocks Simulation: the engine-side steps

What a valid engine run (`ExecutionValid`) does to the shape's state at each event, stated on
`stateAt`: the node state inside the shape's state after an event of an honest node is the
node's handler applied to the node state before it (a tick at a public time with the encoded
mempool, a delivery one `canonEvent` after the other, a restart), the shape's clock is the time of
the node's last tick or restart, and the interface's obligations: at most two bodies
pending at a tick, a proposal carries only released objects (so `releasable` admits it), the
own-object guard `protects` never blocks an honest node, and the digests the engine passes with a
block object map its header to its root.
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
open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

section Engine

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## The node state across a delivery -/

/-- The node state after a delivery of the objects `os` at time `t` from `st`: the handler of
each canonical object in order, nothing for a dropped object (the state `deliverRecs` threads). -/
noncomputable def deliverState (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) :
    List (Wire sp.n) → NodeState (goldilocksNode sp ro) → NodeState (goldilocksNode sp ro)
  | [], st => st
  | o :: os, st =>
      match canonEvent sp ro hs o with
      | some e => deliverState proposer dg hs self t os (exec proposer dg self st t e).1
      | none => deliverState proposer dg hs self t os st

/-- `deliverState` of no objects is the state. -/
theorem deliverState_nil (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time)
    (st : NodeState (goldilocksNode sp ro)) : deliverState proposer dg hs self t [] st = st := by
  simp only [deliverState]

/-- `deliverState` of a canonical object runs its handler first. -/
theorem deliverState_cons_some (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (o : Wire sp.n)
    (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro))
    (e : Event (goldilocksNode sp ro)) (he : canonEvent sp ro hs o = some e) :
    deliverState proposer dg hs self t (o :: os) st =
      deliverState proposer dg hs self t os (exec proposer dg self st t e).1 := by
  simp only [deliverState, he]

/-- `deliverState` skips a dropped object. -/
theorem deliverState_cons_none (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (o : Wire sp.n)
    (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro))
    (he : canonEvent sp ro hs o = none) :
    deliverState proposer dg hs self t (o :: os) st = deliverState proposer dg hs self t os st := by
  simp only [deliverState, he]

/-- The canonical event of a wire object, if any, is a block, a message or an attestation. -/
theorem canonEvent_cases hs (o : Wire sp.n) :
    canonEvent sp ro hs o = none ∨ (∃ B, canonEvent sp ro hs o = some (.block B)) ∨
      (∃ v, canonEvent sp ro hs o = some (.message v)) ∨
      (∃ a, canonEvent sp ro hs o = some (.attestation a)) := by
  unfold canonEvent
  split <;> simp

/-- Processing one delivered object runs the handler of its canonical event, nothing if it has none.
-/
theorem processOne_node (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) hs (st : State sp ro)
    o :
    (processOne hs st o).node =
      match canonEvent sp ro hs o with
      | some e => (exec proposer dg st.self st.node st.now e).1
      | none => st.node := by
  rcases canonEvent_cases (ro := ro) hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩ <;>
    simp [processOne, h, relayIf_node, apply_node, exec]

/-- Processing a list of delivered objects runs `deliverState` on the node state. -/
theorem foldl_processOne_node (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) hs
    (os : List (Wire sp.n)) (st : State sp ro) :
    (os.foldl (processOne hs) st).node = deliverState proposer dg hs st.self st.now os st.node := by
  induction os generalizing st with
  | nil => rfl
  | cons o os ih =>
    rw [List.foldl_cons, ih, processOne_self, processOne_now, processOne_node proposer dg]
    rcases canonEvent_cases (ro := ro) hs o with h | ⟨B, h⟩ | ⟨v, h⟩ | ⟨a, h⟩ <;>
      simp only [deliverState, h]

/-- **`Simulates.deliver`'s node step.** An engine delivery to an honest node runs the handlers of
the delivered canonical objects in order on the node state before it, with the digests the engine
passes. -/
theorem node_of_deliver (hv : rho.ExecutionValid) (v : V) (_hv' : v ∉ rho.faultyAt 0) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocks S)) E).Object) (t : Time)
    (he : rho.events[i]? = some (.deliver v o t)) :
    (stateAt S rho hn v (i + 1)).node =
      deliverState (runProposer S rho hn) (digestOf S rho)
        (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (stateAt S rho hn v i).node := by
  have hpre := (fgDue_eq_false S rho hn v i)
  rw [stateAt_deliver S rho hn v he]
  refine (deliver_pres S rho hn
    (fun st => st.node = (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).node ∧
      st.fgDue = false)
    (fun st t h => ⟨(poll_node_of_fgDue st t h.2).trans h.1, poll_fgDue st t⟩)
    (fun st _ _ hs h =>
      ⟨(recordOwn_none_node st _ _ hs).trans h.1, (recordOwn_fgDue st _ hs).trans h.2⟩)
    v _ o t ⟨by rw [stateAt_eq],
      (process_fgDue _ _ _).trans (by simpa only [stateAt_eq] using hpre)⟩).1.trans ?_
  unfold process
  refine (foldl_processOne_node (runProposer S rho hn) (digestOf S rho) _ _ _).trans ?_
  rw [self_eq_ownKey, now_eq_lastClock S rho hn hv, lastClock_of_deliver S rho hv v he]

/-- **`Simulates.restart`'s node step.** An engine restart of an honest node runs the node's restart
on the node state before it. -/
theorem node_of_restart (_hv : rho.ExecutionValid) (v : V) (_hv' : v ∉ rho.faultyAt 0) (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.restart v t)) :
    (stateAt S rho hn v (i + 1)).node =
      (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t .restart).1 := by
  rw [stateAt_restart S rho hn v he]
  rfl

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
theorem rootOf_digests_item (a : Model.Auth (Fintype.card V) (ShapeRole Empty)) (h : Header Info)
    (cs : List (Wire (Fintype.card V))) :
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
      (skeleton (pubOf E)).grid.slotTime s := by
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
/-- The skeleton lets the run select one proposer per slot. -/
theorem skeleton_proposerSel (s : Nat) :
    (goldilocks S (pubOf E)).skel.proposerSel s = .sized 1 := rfl

omit [DecidableEq V] in
/-- In an admitted run, the proposer role selects exactly `runProposer`. -/
theorem selValid_proposer (hsel : rho.SelValid) (s : Nat) :
    rho.sel (.proposer s) = {runProposer S rho hn s} := by
  have h := hsel (.proposer s)
  change (rho.sel (.proposer s)).card = min 1 (Fintype.card V) at h
  rw [min_eq_left hn] at h
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  have hne : (rho.sel (.proposer s)).Nonempty := ⟨k, hk ▸ Finset.mem_singleton_self k⟩
  rw [runProposer_eq, dite_eq_left hne]
  exact Finset.eq_singleton_iff_unique_mem.mpr
    ⟨Finset.min'_mem _ _, fun x hx => by
      have hm := Finset.min'_mem (rho.sel (.proposer s)) hne
      exact (Finset.mem_singleton.mp (hk ▸ hx)).trans
        (Finset.mem_singleton.mp (Eq.mp (congrArg (fun a => _ ∈ a) hk) hm)).symm⟩

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
  simp only [goldilocks, goldilocksWith, dite_eq_left hn]; rfl

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
  simp only [blockOf, mkBlock, digestOf_eq]
  erw [dgOf_eq]
  rw [parentRoot_parentRef]

omit [DecidableEq V] in
/-- **The proposal duty is the node's proposal step.** At the start of slot `s` of which the node is
the selected proposer, when the proposal carries only released objects, the engine's `propose` duty
step records the block the node's `tickStep .proposal` makes; otherwise both do nothing. -/
theorem dutyStep_propose_node (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
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
    simp only [propose] at hact1 hact2 hrel
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
      have hcrole : ∀ m, (Model.protoOf (compiled (goldilocks S)) E).candidateRole
          (.propose s hs) m = .proposer s := fun _ => rfl
      simp only [Option.map, Option.toList_some, Model.Run.signedCandidate, hrole, hcrole]
      erw [List.filterMap_cons, List.filterMap_nil]
      have hmem : rho.ownKey v ∈ rho.sel (.proposer s) := by
        rw [hsel]
        exact Finset.mem_singleton.2 (hp.trans hself).symm
      simp only [hmem, ↓reduceIte]
      unfold Model.releaseAll
      rw [ite_eq_left (Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨?_, ?_⟩, ?_⟩)]
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
      · exact dependencies_item _ _ _ _ _
  · simp only [tickStep, hP.not.2 hp, ite_false]
    have hmem : rho.ownKey v ∉ rho.sel (.proposer s) := by
      rw [hsel, Finset.mem_singleton]
      intro heq
      exact hp (heq.symm.trans hself.symm)
    simp only [show (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
      .proposer s from rfl, hmem, ↓reduceIte]


/-! ## The node state across a tick -/

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
theorem fgUpdate_node (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat)
    (st : State sp ro) :
    (fgUpdate st).node = (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).1 := by
  unfold fgUpdate Node.tickStep
  simp only
  rcases h : (Node.acToFG st.node st.now).2.2 with _ | C
  · rfl
  · unfold Node.attest
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C with _ | ⟨a, Λ'⟩ <;> simp only [h']

omit [DecidableEq V] in
/-- `fgUpdate_node` with the engine's digests. -/
theorem fgUpdate_node_digestOf (st : State (S.params (pubOf E) hn) (S.ro _)) (x : Nat) :
    (fgUpdate st).node =
      (Node.tickStep (runProposer S rho hn) (digestOf S rho)
        st.self st.node st.now x .fgUpdate).1 :=
  fgUpdate_node (runProposer S rho hn) (digestOf S rho) x st

omit [DecidableEq V] in
/-- A duty keeps the mempool. -/
theorem act_mempool (st : (Model.protoOf (compiled (goldilocks S)) E).State)
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) :
    ((Model.protoOf (compiled (goldilocks S)) E).act st d).1.2 = st.2 := by
  cases d <;> rfl

omit [DecidableEq V] in
/-- `releaseAll` keeps the mempool. -/
theorem releaseAll_mempool (k : Fin (Fintype.card V)) :
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
      (∀ c ∈ cs, ∀ (st : State (S.params (pubOf E) hn) (S.ro _)) hs,
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
noncomputable def atProposal (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
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
/-- The shape at the proposal duty: `nodeTick` of two poll steps of the clocked state. -/
theorem atProposal_shape (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    shapeOf S hn (atProposal S rho v nd t) =
      nodeTick (poll (poll { nd.st.1 hn with now := t } t.toNat).1 t.toNat).1 := by
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
  rw [atProposal_shape _ _ _ _ _ _ hsel, nodeTick_self, poll_self, poll_self]

omit [DecidableEq V] in
/-- The clock at the proposal duty is the tick time. -/
theorem atProposal_now (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (atProposal S rho v nd t)).now = t := by
  rw [atProposal_shape _ _ _ _ _ _ hsel, nodeTick_now, poll_now, poll_now]

omit [DecidableEq V] in
/-- At a public time the FG update is due at the proposal duty: the node's tick set it. -/
theorem atProposal_fgDue (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (atProposal S rho v nd t)).fgDue = true := by
  rw [atProposal_shape _ _ _ _ _ _ hsel]
  unfold nodeTick
  rw [ite_eq_left (by rw [poll_now, poll_now]; exact hp)]

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
      (nodeTick { nd.st.1 hn with now := t }).node := by
  rw [atProposal_shape _ _ _ _ _ _ hsel]
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
theorem tick_node_eq (v : V) (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (t : Time) (ht : 0 ≤ t) (hw : E.awake v t = true)
    (hsel : rho.ownKey v ∈ rho.sel .poll) :
    (shapeOf S hn (rho.tick nd v t).1).node =
      (poll (poll (shapeOf S hn (rho.runDuties v (atProposal S rho v nd t)
          ((skeleton (pubOf E)).proposeAt t)).1) t.toNat).1
        t.toNat).1.node := by
  -- The goal's duty lists are typed at `ShapeDuty`, the step lemmas at the engine's `Duty`: stated
  -- as local equations on the goal's own terms, the steps rewrite with plain `rw` (an `erw` would
  -- try every projection of the goal at default transparency).
  have hpoll : ∀ (nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (x : Nat),
      shapeOf S hn (rho.runDuties v nd' [.poll x]).1 = (poll (shapeOf S hn nd') x).1 :=
    fun nd' x => dutyStep_poll S rho hn v nd' x hsel
  have hinit : ∀ nd' : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
      (rho.runDuties v nd' (dutiesInit S t)).1 =
        (rho.runDuties v (rho.runDuties v (rho.runDuties v nd'
          ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
            List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
          ((skeleton (pubOf E)).proposeAt t)).1 [.poll t.toNat]).1 := fun nd' =>
    (runDuties_fst_append S rho v nd' _ _).trans
      (congrArg (fun x => (rho.runDuties v x [.poll t.toNat]).1)
        (runDuties_fst_append S rho v nd' _ _))
  rw [tick_of_awake S rho v nd t hw, gossip_node_eq, duties_eq S t ht, runDuties_fst_append, hpoll,
    hinit, hpoll]
  rfl

/-- **`Simulates.tick`'s node step at a non-public time.** An engine tick at a non-public time
leaves the node state unchanged: no slot starts, so no proposal, and the FG update is not due. -/
theorem node_of_tick_other (hv : rho.ExecutionValid) (v : V) (_hv' : v ∉ rho.faultyAt 0)
    (i : Nat)
    (t : Time) (he : rho.events[i]? = some (.tick v t))
    (hp : ¬ (S.params (pubOf E) hn).toParams.IsPublic t) :
    (stateAt S rho hn v (i + 1)).node = (stateAt S rho hn v i).node := by
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hsel := poll_selected S rho hv v
  rw [stateAt_tick S rho hn v he, tick_node_eq S rho hn v _ t ht hw hsel]
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E)) t with
    ⟨hnil, _⟩ | ⟨s, hs, _, hts⟩
  · rw [hnil]
    erw [runDuties_fst_nil]
    have hf : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).fgDue = false := by
      rw [atProposal_shape _ _ _ _ _ _ hsel]
      unfold nodeTick
      rw [ite_eq_right (by rw [poll_now, poll_now]; exact hp)]
      exact poll_fgDue _ _
    rw [poll_node_of_fgDue _ _ (poll_fgDue _ _), poll_node_of_fgDue _ _ hf,
      atProposal_node S rho hn v _ t
        (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel,
      nodeTick_node_other _ hp, stateAt_eq]
  · exfalso
    apply hp
    rw [hts, ← slotTime_eq S hn s]
    exact (S.params (pubOf E) hn).toParams.slotTime_public s

/-- The node's `onTick` is its three tick steps in order: the AC's tick, the proposal, the FG
update. -/
theorem onTick_node (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.onTick proposer dg self st t x).1 =
      (Node.tickStep proposer dg self
        (Node.tickStep proposer dg self (Node.tickStep proposer dg self st t x .acTick).1 t x
          .proposal).1 t x .fgUpdate).1 := rfl

/-- The AC-tick step is the AC's tick. -/
theorem tickStep_acTick (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (Node.tickStep proposer dg self st t x .acTick).1 = (Node.acCall self st t .tick).1 := rfl

/-- The proposal step of a key that does not propose at `t` keeps the node state. -/
theorem tickStep_proposal_not (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)
    (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    (h : ¬ Proposes (P := sp.toParams) proposer self t) :
    (Node.tickStep proposer dg self st t x .proposal).1 = st := by
  unfold Node.tickStep
  simp only [h, ite_false]

omit [DecidableEq V] in
/-- A property of the shape's state preserved by `recordOwn` and `propose` is preserved by the
engine's `propose` duty step. -/
theorem dutyStep_propose_pres (Q : State (S.params (pubOf E) hn) (S.ro _) → Prop)
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
