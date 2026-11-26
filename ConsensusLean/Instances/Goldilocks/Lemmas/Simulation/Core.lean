module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.VoteForwardQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Forwarding
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PoolInsertionRelease
import ConsensusLean.Lemmas.Model.Constant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLaws
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

public section

/-! # Goldilocks Simulation: the engine simulates the node

Engine facts of the trace `simTrace` with the cut map `cutMap` (`Trace`): restart events and
the absence of restarts between same-time sends, the sending event of a call, and the processing
of received votes and of a delivered block's payload. The simulation itself is
`simTraceAt_simulates` (`Growing/Simulation/Simulates`). -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Shape Blocks Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
  {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
  {hn : 1 ≤ Fintype.card V} {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
  (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

private theorem delivery_label_cut {i : Nat} {v : V} {o : (Model.protoOf (compiled F) E).Object}
    {t : Time} (he : rho.events[i]? = some (.deliver v o t)) {r : CutRec A}
    (hr : r ∈ eventCuts e rho i) :
    ∃ k, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) ∧
      (simTrace e rho).CallAt (rho.ownKey v) k r.label ∧ (simTrace e rho).time k = t := by
  obtain ⟨ht, hy⟩ := eventCut_node_time e rho he hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr
  have hk : (allCuts e rho)[cutMap e rho i + j]? = some r := by
    rw [allCuts_getElem?_add e rho i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  refine ⟨cutMap e rho i + j, Nat.le_add_right _ _, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [cutMap_succ]; omega
  · simpa only [simTrace_node, hk, Option.elim_some, Model.Event.node] using
      hy.resolve_right fun ⟨⟨_, h⟩, _⟩ => by cases h
  · simp only [simTrace_label, hk, Option.map_some]
  · simpa only [simTrace_time, hk, Option.elim_some, Model.Event.time] using ht

/-- A visited object decoding to a message has an explicit processing cut in its delivery. -/
theorem received_message_processAt {i : Nat} {v : V} {o : (Model.protoOf (compiled F) E).Object}
    {t : Time} {m : A.Msg} (he : rho.events[i]? = some (.deliver v o t))
    (h : ∃ w ∈ delivered (receiverCodec e rho v) e.adapter (Model.digests rho.hash o)
        (stateAt e rho v i) (wireOf e o),
      canonEvent (receiverCodec e rho v) (Model.digests rho.hash o) w = some (.message m)) :
    ∃ k, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) ∧
      (simTrace e rho).projAC.ProcessAt (rho.ownKey v) k m ∧ (simTrace e rho).time k = t := by
  obtain ⟨r, hr, l, hl, hm⟩ := deliverRecs_message_call (receiverCodec e rho v) _
    (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i m _ _ 0 h
  have hr' : r ∈ eventCuts e rho i := by
    rw [eventCuts_deliver e rho i v o t he]
    exact hr
  obtain ⟨k, hlo, hhi, hcall, ht⟩ := delivery_label_cut e rho he hr'
  rw [hl] at hcall
  exact ⟨k, hlo, hhi, ⟨l, Compose.projAC_callAt.mpr hcall, Or.inl hm⟩, ht⟩

/-- A visited object decoding to an attestation has a direct processing call at receipt time,
even if the attestation was already pooled. -/
theorem received_att_processAt {i : Nat} {v : V} {o : (Model.protoOf (compiled F) E).Object}
    {t : Time} {a : FG.Att (Fintype.card V)} (he : rho.events[i]? = some (.deliver v o t))
    (h : ∃ w ∈ delivered (receiverCodec e rho v) e.adapter (Model.digests rho.hash o)
        (stateAt e rho v i) (wireOf e o),
      canonEvent (receiverCodec e rho v) (Model.digests rho.hash o) w = some (.attestation a)) :
    ∃ k, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) ∧
      (simTrace e rho).ProcessAttAt (rho.ownKey v) k a ∧ (simTrace e rho).time k = t := by
  obtain ⟨r, hr, hl⟩ := deliverRecs_label (receiverCodec e rho v) _ (runProposer rho hn)
    (digestOf e rho) (rho.ownKey v) t i (.attestation a) (· = .fg (.attestation a)) _ _ 0 h
    (by intro s; simp [exec, onAttestation])
  have hr' : r ∈ eventCuts e rho i := by
    rw [eventCuts_deliver e rho i v o t he]
    exact hr
  obtain ⟨k, hlo, hhi, hcall, ht⟩ := delivery_label_cut e rho he hr'
  rw [hl] at hcall
  exact ⟨k, hlo, hhi, Or.inl hcall, ht⟩

/-- A message carried by a non-refused receipt is processed at that same delivery. -/
theorem received_carried_message_processAt {i : Nat} {v : V}
    {o : (Model.protoOf (compiled F) E).Object} {t : Time} {m : A.Msg}
    {w : ShapeObj (Fintype.card V) e.skel.Kind I e.Body}
    (he : rho.events[i]? = some (.deliver v o t))
    (ha : ¬ Refuses (receiverCodec e rho v) e.adapter (Model.digests rho.hash o)
      (stateAt e rho v i) (wireOf e o))
    (hm : w ∈ (wireOf e o).carried)
    (hd : canonEvent (receiverCodec e rho v) (Model.digests rho.hash o) w = some (.message m)) :
    ∃ k, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) ∧
      (simTrace e rho).projAC.ProcessAt (rho.ownKey v) k m ∧ (simTrace e rho).time k = t :=
  received_message_processAt e rho he
    ⟨w, carried_subset_delivered_self (receiverCodec e rho v) e.adapter _ ha hm, hd⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Shape Blocks
open Consensus.Model (pubOf)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A trace restart is produced by an actual engine restart, never by tick or
recursive delivery processing. The interval identifies its exact engine event. -/
theorem simTrace_restart_event {y : Fin (Fintype.card V)} {k : Nat}
    (hr : (simTrace S rho hn).RestartAt y k) :
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.events[i]? = some (.restart (rho.key y) ((simTrace S rho hn).time k)) := by
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hr
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, hlo, hhi, hidx, hn', ht, -, hlab'⟩ :=
    simTrace_cut S rho hn hl fun a h => by rw [hlab] at h; cases h
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn he (List.mem_of_getElem? hidx) hrl hcall
  have hkey : v = rho.key y := by
    have hk := congrArg rho.key (hn'.symm.trans hnode)
    exact (rho.key.apply_symm_apply v).symm.trans hk
  exact ⟨i, hlo, hhi, by simpa only [hkey, ht, Model.Event.time] using he⟩

/-- An engine interval without this node's restarts contains no restart cuts for
that node. This supplies the cut-level premise needed for pool monotonicity. -/
theorem simTrace_noRestart_between {y : Fin (Fintype.card V)} {a b k : Nat}
    (hnr : ∀ i, a ≤ i → i < b → ∀ t,
      rho.events[i]? ≠ some (.restart (rho.key y) t))
    (ha : cutMap S rho hn a ≤ k) (hb : k < cutMap S rho hn b) :
    ¬ (simTrace S rho hn).RestartAt y k := by
  intro hr
  obtain ⟨i, hlo, hhi, he⟩ := simTrace_restart_event S rho hn hr
  have hai : a ≤ i := by
    by_contra h
    have hm := cutMap_mono S rho hn (show i + 1 ≤ a by omega)
    omega
  have hib : i < b := by
    by_contra h
    have hm := cutMap_mono S rho hn (show b ≤ i by omega)
    omega
  exact hnr i hai hib _ he

/-- Restarts precede all sending events at a fixed time, so none can intervene
between two such events, even for a different node. -/
theorem noRestart_between_same_time_sends (hv : rho.ExecutionValid)
    {v : V} {a b : Nat} {t : Time} (ha : rho.SendsAt v a t) (hb : rho.SendsAt v b t)
    {j : Nat} (haj : a ≤ j) (hjb : j < b) (w : V) (u : Time) :
    rho.events[j]? ≠ some (.restart w u) := by
  intro hr
  have haj' : a < j := by
    rcases haj.lt_or_eq with h | rfl
    · exact h
    · rcases ha with ha | ⟨o, ha⟩ <;> rw [hr] at ha <;> cases ha
  have hle : u ≤ t := by
    rcases hb with hb | ⟨o, hb⟩ <;>
      rcases keyLe_of_lt S rho hv hr hb hjb with h | h
    all_goals first | exact h.le | exact h.1.le
  rcases ha with ha | ⟨o, ha⟩ <;>
    rcases keyLe_of_lt S rho hv ha hr haj' with h | h
  all_goals first
    | exact (not_lt_of_ge hle) h
    | simpa only [Model.Event.phase, Nat.reduceLeDiff] using h.2

/-- Every non-restart AC cut lies in a sending engine event of the same node and time.
This is interval transport only; it does not assume the publication supplier. -/
theorem simTrace_call_sending_event {y : Fin (Fintype.card V)} {k : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hc : (simTrace S rho hn).CallAt y k (.ac ℓ)) (hnr : ℓ.call ≠ .restart) :
    ∃ i, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      rho.SendsAt (rho.key y) i ((simTrace S rho hn).time k) := by
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hc.2]; simp
  obtain ⟨r, i, ev, -, he, hlo, hhi, hidx, hnode, ht, -, hlabel⟩ :=
    simTrace_cut S rho hn hl fun a h => by rw [hc.2] at h; cases h
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

end Consensus.Goldilocks.Simulation

end
