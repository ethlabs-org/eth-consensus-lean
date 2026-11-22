module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

public section

/-! # Goldilocks Simulation: where the cuts of the simulating trace come from

Every node cut of `allCuts` is a cut of one engine event: cut `k` of the trace, below the
length of `allCuts` (which is `cutMap` of the number of events), is the cut `k - cutMap i` of
the event `i` with `cutMap i ≤ k < cutMap (i + 1)` (`allCuts_getElem?`), and conversely
(`allCuts_getElem?_add`). A cut of event `i` is at the event's node and time, under an event id
`Nat.pair i s` (`mem_eventCuts`). The cuts of a group are at the positions `0, 1, …`
(`getElem_groupRecs`); a cut at position `0` starts a group whose handler is of the engine
event's phase (`phase_of_pos_zero`); an `ac_restart` cut is a cut of an engine restart
(`restart_of_mem_eventCuts`). -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {binding : VoteBinding}

/-! ## Groups and deliveries -/

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)

/-- One post-state per cut. -/
theorem length_cutPosts (t : Time) (cs : List (Cut (goldilocksNode sp ro)))
    (st : NodeState (goldilocksNode sp ro)) : (cutPosts self t cs st).length = cs.length := by
  induction cs generalizing st with
  | nil => simp only [cutPosts_nil, List.length_nil]
  | cons c cs ih => simp only [cutPosts_cons, List.length_cons, ih]

/-- A group has one cut per handler cut. -/
theorem length_groupRecs (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) :
    (groupRecs proposer dg self st t id e).length = (exec proposer dg self st t e).2.length := by
  simp [groupRecs_eq, length_cutPosts]

/-- The cut at position `k` of a group: the node, time and event id of the group, position `k`,
the handler's cut `k`. -/
theorem getElem_groupRecs (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) (k : Nat)
    (hk : k < (groupRecs proposer dg self st t id e).length) :
    (groupRecs proposer dg self st t id e)[k].node = self ∧
      (groupRecs proposer dg self st t id e)[k].time = t ∧
      (groupRecs proposer dg self st t id e)[k].event = id ∧
      (groupRecs proposer dg self st t id e)[k].pos = k ∧
      (groupRecs proposer dg self st t id e)[k].label =
        (exec proposer dg self st t e).2[k]'(by rwa [length_groupRecs] at hk) := by
  rw [List.getElem_of_eq (groupRecs_eq proposer dg self st t id e) hk, List.getElem_mapIdx,
    List.getElem_zip]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A cut of a group is at the group's node, time and event id. -/
theorem mem_groupRecs {st : NodeState (goldilocksNode sp ro)} {t : Time} {id : Nat}
    {e : Event (goldilocksNode sp ro)} {r : CutRec sp ro}
    (hr : r ∈ groupRecs proposer dg self st t id e) :
    r.node = self ∧ r.time = t ∧ r.event = id := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨h1, h2, h3, -⟩ := getElem_groupRecs proposer dg self st t id e k hk
  exact ⟨h1, h2, h3⟩

/-- A cut of a delivery's cuts is at the delivery's node and time, under the id of a sub-event
from `sub` on. -/
theorem mem_deliverRecs (hs : List (Header Info × Nat)) (t : Time) (i : Nat)
    {os : List (Wire sp.n binding)} {st : NodeState (goldilocksNode sp ro)} {sub : Nat}
    {r : CutRec sp ro} (hr : r ∈ deliverRecs proposer dg hs self t i os st sub) :
    r.node = self ∧ r.time = t ∧ ∃ s, sub ≤ s ∧ r.event = Nat.pair i s := by
  induction os generalizing st sub with
  | nil => simp [deliverRecs_nil] at hr
  | cons o os ih =>
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none proposer dg hs self t i o os st sub he] at hr
      obtain ⟨h1, h2, s, hs', h3⟩ := ih hr
      exact ⟨h1, h2, s, by omega, h3⟩
    | some e =>
      rw [deliverRecs_cons_some proposer dg hs self t i o os st sub e he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨h1, h2, h3⟩ := mem_groupRecs proposer dg self hr
        exact ⟨h1, h2, sub, le_rfl, h3⟩
      · obtain ⟨h1, h2, s, hs', h3⟩ := ih hr
        exact ⟨h1, h2, s, by omega, h3⟩

end

/-! ## The cuts of the run -/

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The number of node cuts is the cut map at the last engine cut. -/
theorem length_allCuts : (allCuts S rho hn).length = cutMap S rho hn rho.events.length := by
  obtain ⟨_, hall, _⟩ := cutRecords_map S rho hn
  rw [hall, List.length_map, (simTrace_encoding S rho hn).2,
    NodeAsChainShape.CanonicalTrace.allCuts_eq]
  exact NodeAsChainShape.CanonicalTrace.prefix_cuts (traceEncoding S hn) rho _

/-- **Every node cut is a cut of one engine event**: cut `k` below the length of `allCuts` is the
cut `k - cutMap i` of the event `i` with `cutMap i ≤ k < cutMap (i + 1)`. -/
theorem allCuts_getElem? (k : Nat) (hk : k < (allCuts S rho hn).length) :
    ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (allCuts S rho hn)[k]? = (eventCuts S rho hn i)[k - cutMap S rho hn i]? := by
  obtain ⟨_, hall, hevent⟩ := cutRecords_map S rho hn
  rw [hall, List.length_map] at hk
  cases hcut : (NodeAsChainShape.CanonicalTrace.allCuts (traceEncoding S hn) rho)[k]? with
  | none => simp [List.getElem?_eq_getElem hk] at hcut
  | some r =>
    have hprefix := hcut
    rw [NodeAsChainShape.CanonicalTrace.allCuts_eq] at hprefix
    obtain ⟨i, hi, hlo, hhi, hix⟩ := NodeAsChainShape.CanonicalTrace.cut_event_range
      (traceEncoding S hn) rho _ k r hprefix
    rw [(simTrace_encoding S rho hn).2]
    refine ⟨i, hi, hlo, hhi, ?_⟩
    rw [hall, hevent, List.getElem?_map, List.getElem?_map, hcut, hix]

/-- The cut `j` of the engine event `i` is the node cut `cutMap i + j`. -/
theorem allCuts_getElem?_add (i j : Nat) (hi : i < rho.events.length)
    (hj : j < (eventCuts S rho hn i).length) :
    (allCuts S rho hn)[cutMap S rho hn i + j]? = (eventCuts S rho hn i)[j]? := by
  obtain ⟨_, hall, hevent⟩ := cutRecords_map S rho hn
  rw [hevent, List.length_map] at hj
  rw [hall, hevent, List.getElem?_map, List.getElem?_map, (simTrace_encoding S rho hn).2,
    NodeAsChainShape.CanonicalTrace.allCuts_getElem?_add _ _ i j hi hj]

/-- A node cut that exists is a cut of an engine event `i`, the event at index `i`. -/
theorem exists_event_of_getElem? {k : Nat} {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : (allCuts S rho hn)[k]? = some r) :
    ∃ i ev, rho.events[i]? = some ev ∧ cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (eventCuts S rho hn i)[k - cutMap S rho hn i]? = some r := by
  obtain ⟨i, hi, h1, h2, h3⟩ :=
    allCuts_getElem? S rho hn k (List.getElem?_eq_some_iff.mp hr).1
  exact ⟨i, rho.events[i], List.getElem?_eq_getElem hi, h1, h2, h3 ▸ hr⟩

/-- A cut of engine event `i` is at the event's node (its own key) and time, under an event id
`Nat.pair i s`. -/
theorem mem_eventCuts {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) :
    r.node = rho.ownKey ev.node ∧ r.time = ev.time ∧ ∃ s, r.event = Nat.pair i s := by
  obtain ⟨q, hq, _, _, hn', ht, hid⟩ := eventCuts_source S rho hn i hr
  obtain ⟨hqt, hqn⟩ := NodeAsChainShape.CanonicalTrace.eventCut_node_time
    (traceEncoding S hn) rho he hq
  rw [hn', ht, hid]
  exact ⟨hqn, hqt, NodeAsChainShape.CanonicalTrace.eventCut_id (traceEncoding S hn) rho he hq⟩

/-- A cut at position `0` of engine event `i` starts a group whose handler is of the engine
event's phase: if its label is the first cut of the handler of `e` (at any state), `e` has the
phase of the engine event. -/
theorem phase_of_pos_zero {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) (h0 : r.pos = 0)
    {dg : Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V))}
    {y : Fin (Fintype.card V)} {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    {t : Time} {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    {cs : List (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))}
    {proposer : Nat → Fin (Fintype.card V)}
    (hcs : (exec proposer dg y st t e).2 = r.label :: cs) : e.phase = ev.phase := by
  obtain ⟨q, hq, hpos, hlabel, _⟩ := eventCuts_source S rho hn i hr
  exact NodeAsChainShape.CanonicalTrace.phase_of_pos_zero (traceEncoding S hn) rho he hq
    (hpos ▸ h0) (hlabel ▸ hcs)

/-- An `ac_restart` cut is a cut of an engine restart. -/
theorem restart_of_mem_eventCuts {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hl : r.label = .ac ℓ) (hℓ : ℓ.call = .restart) : ∃ v t, ev = .restart v t := by
  obtain ⟨q, hq, _, hlabel, _⟩ := eventCuts_source S rho hn i hr
  exact NodeAsChainShape.CanonicalTrace.restart_of_mem_eventCuts (traceEncoding S hn) rho he hq
    (hlabel ▸ hl) hℓ

/-- The cuts of a group-shaped engine event (a tick at a public time, a restart) are at the
positions `0, 1, …`. -/
theorem pos_getElem_eventCuts_of_group {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t) ∨ rho.events[i]? = some (.restart v t)) (m : Nat)
    (hm : m < (eventCuts S rho hn i).length) : (eventCuts S rho hn i)[m].pos = m := by
  rcases he with he | he
  · by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · simp only [eventCuts_tick_public S rho hn i v t he hp] at hm ⊢
      exact (getElem_groupRecs _ _ _ _ _ _ _ m hm).2.2.2.1
    · simp [eventCuts_tick_other S rho hn i v t he hp] at hm
  · simp only [eventCuts_restart S rho hn i v t he] at hm ⊢
    exact (getElem_groupRecs _ _ _ _ _ _ _ m hm).2.2.2.1

/-- An engine restart has exactly one cut, the restart's `ac_restart`. -/
theorem eventCuts_restart_length {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) : (eventCuts S rho hn i).length = 1 := by
  rw [eventCuts_restart S rho hn i v t he]
  exact (length_groupRecs _ _ _ _ _ _ _).trans rfl

/-- An engine restart's one cut, at `cutMap i`: at the restart's node and time, an `ac_restart`. -/
theorem restart_getElem? {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    cutMap S rho hn (i + 1) = cutMap S rho hn i + 1 ∧
      ∃ r, (allCuts S rho hn)[cutMap S rho hn i]? = some r ∧ r.node = rho.ownKey v ∧
        r.time = t ∧ ∃ ℓ, r.label = .ac ℓ ∧ ℓ.call = .restart := by
  have hlen := eventCuts_restart_length S rho hn he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨by rw [cutMap_succ, hlen], (eventCuts S rho hn i)[0], ?_⟩
  have h0 := allCuts_getElem?_add S rho hn i 0 hi (by rw [hlen]; exact Nat.one_pos)
  rw [Nat.add_zero] at h0
  refine ⟨by rw [h0]; exact List.getElem?_eq_getElem _, ?_⟩
  have hm : 0 < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) .restart).length := by
    rw [← eventCuts_restart S rho hn i v t he, hlen]; exact Nat.one_pos
  obtain ⟨h1, h2, -, -, h5⟩ := getElem_groupRecs _ _ _ _ _ _ _ 0 hm
  simp only [eventCuts_restart S rho hn i v t he]
  refine ⟨h1, h2, _, h5.trans rfl, rfl⟩

/-- **A labelled cut of the trace is a cut of an engine event**: the event `i` at whose cuts
`[cutMap i, cutMap (i + 1))` it lies, with the cut's node (the event node's key), time (the
event's), position and label. -/
theorem simTrace_cut {k : Nat} (hk : (simTrace S rho hn).label k ≠ none) :
    ∃ r i ev, (allCuts S rho hn)[k]? = some r ∧ rho.events[i]? = some ev ∧
      cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (eventCuts S rho hn i)[k - cutMap S rho hn i]? = some r ∧
      (simTrace S rho hn).node k = rho.ownKey ev.node ∧ (simTrace S rho hn).time k = ev.time ∧
      (simTrace S rho hn).pos k = r.pos ∧ (simTrace S rho hn).label k = some r.label := by
  rw [simTrace_label] at hk
  cases hr : (allCuts S rho hn)[k]? with
  | none => simp [hr] at hk
  | some r =>
  obtain ⟨i, ev, he, h1, h2, h3⟩ := exists_event_of_getElem? S rho hn hr
  have hmem : r ∈ eventCuts S rho hn i := List.mem_of_getElem? h3
  obtain ⟨hnode, htime, -⟩ := mem_eventCuts S rho hn he hmem
  refine ⟨r, i, ev, rfl, he, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · rw [simTrace_node, hr]; exact hnode
  · rw [simTrace_time, hr]; exact htime
  · rw [simTrace_pos, hr]; rfl
  · rw [simTrace_label, hr]; rfl

/-- Past the last node cut the trace is unlabelled, strictly after the observation horizon. -/
theorem simTrace_of_getElem?_none {k : Nat} (hk : (allCuts S rho hn)[k]? = none) :
    (simTrace S rho hn).label k = none ∧ (simTrace S rho hn).time k = rho.horizon + 1 := by
  simp [simTrace_label, simTrace_time, hk]

end Consensus.Goldilocks.Simulation

end
