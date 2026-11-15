module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Trace

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

open Classical in
/-- The engine event whose trace cuts contain cut `k` (`0` if there is none). -/
noncomputable def eventOf (k : Nat) : Nat :=
  if h : ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) then
    h.choose
  else 0

open Classical in
/-- `eventOf` chooses a covering engine event when there is one. -/
theorem eventOf_eq (k : Nat) : eventOf S rho hn k =
    if h : ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) then
      h.choose
    else 0 := by rfl

/-- A labelled cut lies in the cuts of the engine event `eventOf` chooses. -/
theorem eventOf_spec {k : Nat} (hk : (simTraceAt S rho hn).label k ≠ none) :
    eventOf S rho hn k < rho.events.length ∧ cutMap S rho hn (eventOf S rho hn k) ≤ k ∧
      k < cutMap S rho hn (eventOf S rho hn k + 1) := by
  rw [simTraceAt_eq] at hk
  have h := simTrace_covered S rho hn k hk
  rw [eventOf_eq, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

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
  have hg := eventOf_group S rho hn k hk
  rw [simTraceAt_eq] at hk ⊢
  obtain ⟨_, i, ev, -, hev, h1, h2, -, -, ht, -⟩ := simTrace_cut S rho hn hk
  have hi : i = eventOf S rho hn k :=
    le_antisymm (cutMap_index_le S rho hn h1 hg.2 le_rfl) (cutMap_index_le S rho hn hg.1 h2 le_rfl)
  rw [hi, he] at hev
  rw [ht, Option.some.inj hev]

/-- The trace cut at an engine cut is no earlier than the engine cut's time. -/
theorem cutTime_le_cutMap_time (hv : rho.ExecutionValid) :
    ∀ i, i ≤ rho.events.length →
      rho.cutTime i ≤ (simTraceAt S rho hn).time (cutMap S rho hn i) := by
  intro i hi
  cases i with
  | zero => exact simTraceAt_time_nonneg S rho hn hv _
  | succ i =>
    obtain ⟨e, he⟩ : ∃ e, rho.events[i]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hc : rho.cutTime (i + 1) = e.time := by simp [Model.Run.cutTime, he]
    rw [hc, simTraceAt_eq]
    exact (Obligations.readPoint_after_event S rho hn hv he).2

/-- The trace horizon is the engine horizon. -/
theorem simTraceAt_inHorizon_iff_le (hv : rho.ExecutionValid) (t : Time) :
    (simTraceAt S rho hn).InHorizon t ↔ t ≤ rho.horizon := by
  refine ⟨simTraceAt_inHorizon_le S rho hn hv, fun ht => ?_⟩
  rw [simTraceAt_eq]
  exact simTrace_inHorizon_of_le S rho hn ht

end Consensus.Goldilocks.Simulation

end
