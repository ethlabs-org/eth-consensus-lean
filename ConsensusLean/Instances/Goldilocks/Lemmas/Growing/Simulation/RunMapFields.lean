module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.EngineRepresentation
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace
import ConsensusLean.Spec.Shape.Claims

public section

/-! # The data and laws of the Goldilocks run map

The data `goldilocksRunMap` needs beyond existing definitions, with the laws that no existing
lemma states:

* `outTip`: the tip of each output, so a node's output is the header list of `blocksTo` up to it
  (`outOf_eq_blocksTo`);
* `payloadOf`: the transactions decoded from a block's header input;
* `eventOf`: the engine event whose trace cuts contain a labelled cut (`eventOf_lt`,
  `eventOf_group`, `eventOf_time`);
* `cutTime_le_cutMap_time` and `simTraceAt_inHorizon_iff_le`: the time after an engine cut and the
  trace horizon. -/

namespace Consensus.Goldilocks.Generic.RunMap

open Shape

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {I : Type}
  [DecidableEq I] [Countable I] {F : ChainShapeFamily O I}
  {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat} (M : RunMap rho payload)

/-- On the run's horizon, trace honesty is engine honesty at the same time. -/
theorem honest_iff_of_le {y : Fin P.n} {t : Time} (ht : t ≤ rho.horizon) :
    y ∈ M.honest t ↔ rho.point.HonestAt (M.validator y) t := by
  rw [M.honest_eq, min_eq_left ht]

/-- The map transports engine readiness at any time in its observation window. -/
theorem readyAt {c t : Time} {v : V} (ht : t ≤ rho.horizon)
    (hr : rho.point.Ready c v t) :
    M.validator.symm v ∈ M.honest t ∧
      ∀ u, max 0 (t - c - 1) ≤ u → u ≤ t → M.trace.awake (M.validator.symm v) u := by
  refine ⟨(M.honest_iff_of_le ht).mpr (by simpa using hr.1), fun u hu hut => ?_⟩
  apply (M.awake_eq _ _).mpr
  exact ⟨by simpa only [Model.Run.point, Equiv.apply_symm_apply] using hr.2 u hu hut,
    (le_max_left _ _).trans hu, hut.trans ht⟩

/-- A ready engine reader at a bounded cut has a ready read on its mapped cut. -/
theorem readyReadAtCut (hv : rho.ExecutionValid) {c : Time} {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hr : rho.point.Ready c v (rho.cutTime i)) :
    ReadyRead M c (M.validator.symm v) (M.cut i) (rho.cutTime i) := by
  have laws := (Model.sysOf_laws O (compiled F) V).trace ⟨E, rho⟩ hv
  have h0 : 0 ≤ rho.cutTime i := laws.cutTime_mono 0 i (Nat.zero_le i) hi
  have hh : rho.cutTime i ≤ rho.horizon := laws.cutTime_le_horizon i hi
  exact ⟨(M.readyAt hh hr).1, M.before_time i hi, M.after_time i hi, h0, hh,
    (M.readyAt hh hr).2⟩

/-- The faulty indices are the preimage of the faulty validators, within the horizon. -/
theorem faulty_ncard {t : Time} (ht : t ≤ rho.horizon) :
    (M.honest t)ᶜ.ncard = (rho.faultyAt t).card := by
  have heq : (M.honest t)ᶜ = M.validator ⁻¹' (↑(rho.faultyAt t) : Set V) := by
    ext y
    simp [M.honest_iff_of_le ht, EnvPoint.HonestAt, Model.Run.point]
  rw [heq, Set.ncard_preimage_of_injective_subset_range M.validator.injective
    (by simp [M.validator.surjective.range_eq]), Set.ncard_coe_finset]

/-- Mapping a committee back to validators recovers the engine selection. -/
theorem committee_map {t : Time} (ht : 0 ≤ t) :
    (M.committee t).map M.validator.toEmbedding =
      (Model.sysExternal O (compiled F) V).selected E (rho.key, rho.sel) t := by
  ext v
  simp only [Finset.mem_map, Equiv.toEmbedding_apply]
  exact ⟨fun ⟨y, hy, he⟩ => he ▸ (M.committee_eq y t ht).mp hy,
    fun hv => ⟨M.validator.symm v, (M.committee_eq _ t ht).mpr (by simpa using hv), by simp⟩⟩

end Consensus.Goldilocks.Generic.RunMap

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Payload)

section Chain

variable {sp : SAParams}

variable (sp) (ro : ReplayOrder sp (List (FG.Att sp.n)))

/-- The tip of each output of a node state at time `t`, as in `outOf`: `Σ.F` for `finalized`,
`ac_confirmed(𝒜, fg_to_ac(Σ), t)` for `confirmed`. -/
noncomputable def outTip : Out → NodeState (goldilocksNode sp ro) → Time → Blk sp
  | .finalized, st, _ => st.fg.F
  | .confirmed, st, t => (goldilocksNode sp ro).confirmed st.ac (Node.frame st) t

/-- The confirmed tip is the AC's confirmed block. -/
theorem outTip_confirmed (st : NodeState (goldilocksNode sp ro)) (t : Time) :
    outTip sp ro .confirmed st t = (goldilocksNode sp ro).confirmed st.ac (Node.frame st) t := by
  rfl

/-- The finalized tip is the FG store's finalized block. -/
theorem outTip_finalized (st : NodeState (goldilocksNode sp ro)) (t : Time) :
    outTip sp ro .finalized st t = st.fg.F := by
  rfl

/-- Each node output is the header list of `blocksTo` up to its tip (fuel: the tip's slot). -/
theorem outOf_eq_blocksTo (st : NodeState (goldilocksNode sp ro)) (t : Time) (g : Out) :
    outOf st t g = (blocksTo st.fg.blocks ((outTip sp ro g st t).slot + 1)
      (outTip sp ro g st t)).map (headerOf sp) := by
  rw [blocksTo_map]
  cases g <;> rfl

end Chain

/-- The transactions of a block: those decoded from its header's input. -/
def payloadOf (S : Setup) {pub : Model.Public} {hn : 1 ≤ pub.n}
    (B : Blk (S.params pub hn)) : Set Nat :=
  {tx | tx ∈ decodeTxs (headerOf _ B).input}

/-- A block's payload is the transactions decoded from its header's input. -/
theorem payloadOf_eq (S : Setup) {pub : Model.Public} {hn : 1 ≤ pub.n}
    (B : Blk (S.params pub hn)) :
    payloadOf S B = {tx | tx ∈ decodeTxs (headerOf _ B).input} := by rfl

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The engine event whose trace cuts contain cut `k` (`0` if there is none). -/
noncomputable def eventOf (k : Nat) : Nat :=
  NodeAsChainShape.CanonicalTrace.eventOf (traceEncoding S hn) rho k

/-- The Goldilocks event index is that of the generic replay. -/
theorem eventOf_encoding (k : Nat) : eventOf S rho hn k =
    NodeAsChainShape.CanonicalTrace.eventOf (traceEncoding S hn) rho k := by rfl

open Classical in
/-- `eventOf` chooses a covering engine event when there is one. -/
theorem eventOf_eq (k : Nat) : eventOf S rho hn k =
    if h : ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) then
      h.choose
    else 0 := by
  rw [eventOf_encoding, NodeAsChainShape.CanonicalTrace.eventOf_eq, (simTrace_encoding S rho hn).2]

/-- A labelled cut lies in the cuts of the engine event `eventOf` chooses. -/
theorem eventOf_spec {k : Nat} (hk : (simTraceAt S rho hn).label k ≠ none) :
    eventOf S rho hn k < rho.events.length ∧ cutMap S rho hn (eventOf S rho hn k) ≤ k ∧
      k < cutMap S rho hn (eventOf S rho hn k + 1) := by
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1] at hk
  simpa only [eventOf_encoding, (simTrace_encoding S rho hn).2] using
    NodeAsChainShape.CanonicalTrace.eventOf_spec (traceEncoding S hn) rho hk

/-- The event of a labelled cut is an engine event. -/
theorem eventOf_lt :
    ∀ k, (simTraceAt S rho hn).label k ≠ none → eventOf S rho hn k < rho.events.length :=
  fun _ hk => (eventOf_spec S rho hn hk).1

/-- A labelled cut lies in its event's cuts. -/
theorem eventOf_group : ∀ k, (simTraceAt S rho hn).label k ≠ none →
    cutMap S rho hn (eventOf S rho hn k) ≤ k ∧ k < cutMap S rho hn (eventOf S rho hn k + 1) :=
  fun _ hk => (eventOf_spec S rho hn hk).2

/-- A labelled cut is at the time of its event. -/
theorem eventOf_time : ∀ k e, (simTraceAt S rho hn).label k ≠ none →
    rho.events[eventOf S rho hn k]? = some e → (simTraceAt S rho hn).time k = e.time := by
  intro k e hk he
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1] at hk ⊢
  rw [eventOf_encoding] at he
  exact NodeAsChainShape.CanonicalTrace.eventOf_time (traceEncoding S hn) rho hk he

/-- The trace cut at an engine cut is no earlier than the engine cut's time. -/
theorem cutTime_le_cutMap_time (hv : rho.ExecutionValid) :
    ∀ i, i ≤ rho.events.length →
      rho.cutTime i ≤ (simTraceAt S rho hn).time (cutMap S rho hn i) := by
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1, (simTrace_encoding S rho hn).2]
  exact fun _ hi =>
    (NodeAsChainShape.CanonicalTrace.cutMap_time_bounds (traceEncoding S hn) rho hv hi).2

/-- The trace horizon is the engine horizon. -/
theorem simTraceAt_inHorizon_iff_le (hv : rho.ExecutionValid) (t : Time) :
    (simTraceAt S rho hn).InHorizon t ↔ t ≤ rho.horizon := by
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1]
  exact NodeAsChainShape.CanonicalTrace.inHorizon_iff (traceEncoding S hn) rho hv t

end Consensus.Goldilocks.Simulation

end
