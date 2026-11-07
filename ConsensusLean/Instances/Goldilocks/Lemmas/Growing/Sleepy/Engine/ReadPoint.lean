module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Sleepy
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Record
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.Outputs
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Cuts
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The read point of an engine reader under growing faults

An engine node read at engine cut `i` is honest and ready at `rho.cutTime i`, the time of the
event before the cut. The trace cut `cutMap i` is at the time of the next event (or after the
horizon), so a node compromised in between is not honest there. Such a reader is read instead at
the trace cut after its last own event before `i` (`cutMap (lastOwn v i)`), at its stored clock:

* `lastOwn v i`: the engine cut after `v`'s last own event before `i` (`0` if none), monotone in
  `i`, at which `v`'s engine state is its state at `i` (`stateAt_lastOwn`);
* `cutMap_boundary`: the trace cut at an engine cut is a boundary of every node;
* `lastOwn_readPoint`, `engine_read_eq_at`: for a node honest at `cutTime i`, that cut is a read
  point at its stored clock, and every engine output at `i` is read from the trace state there;
* `engine_read_point`: with catch-up `c + 1` at `cutTime i`, the trace cut `cutMap (lastOwn v i)`
  is a read point at the stored clock `t ∈ [0, horizon]`, the node is ready at `t` with catch-up
  `c` (honest at `t ≤ cutTime i`), and its engine confirmed read is the chain of `readAfter` there;
* `held_state`: a state read by a node honest at `t ≥ 0` with every earlier cut no later has a
  reachable store, a well-formed frame and a tree inside the blocks held while honest;
* `read_prefix`: ancestry of two such reads inside the blocks held while honest is a prefix of their
  confirmed chains.

Readers of other outputs and regimes reuse the same read point. -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Blocks Shape Node
open Consensus.Model (pubOf)

section Held

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- The state before cut `j` of a node honest at `t ≥ 0`, with every cut before `j` at a time
`≤ t`: a reachable store, a well-formed frame, and a tree inside the blocks held while honest
(the static facts on the prefix through `t`). -/
theorem held_state (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} {j : Nat} {t : Time} (ht : 0 ≤ t) (hj : ∀ k < j, tr.time k ≤ t)
    (hy : y ∈ H t) :
    (tr.state y j).fg.Reachable (goldilocksNode sp ro).genesisPayload ∧
      FrameOK (Node.frame (tr.state y j)) ∧ (tr.state y j).fg.tree ⊆ tr.HonestBlocksAt H := by
  have hs := Trace.upTo_state tr y hj
  have hr := (hrun.upTo ht).toLocalRun
  refine ⟨?_, ?_, fun B hB => ⟨y, j, t, ht, hj, hy, hB⟩⟩
  · rw [← hs]
    exact Compose.fg_reachable hr hy j
  · rw [← hs]
    exact Compose.frameOK_state hr hy j

end Held

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The first cut of an event's group is at position `0`. -/
private theorem groupRecs_head_pos {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) {r : CutRec sp ro}
    (h : (groupRecs proposer dg self st t id e)[0]? = some r) : r.pos = 0 := by
  simp only [groupRecs_eq, List.getElem?_mapIdx, Option.map_eq_some_iff] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

/-- The first cut of a delivery is at position `0`. -/
private theorem deliverRecs_head_pos {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat)
      {r : CutRec sp ro}, (deliverRecs proposer dg hs self t i os st sub)[0]? = some r →
      r.pos = 0
  | [], st, sub, r, h => by simp [deliverRecs_nil] at h
  | o :: os, st, sub, r, h => by
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at h
      exact deliverRecs_head_pos proposer dg hs self t i os st (sub + 1) h
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at h
      by_cases hg : (groupRecs proposer dg self st t (Nat.pair i sub) e).length = 0
      · rw [List.getElem?_append_right (by omega), hg] at h
        exact deliverRecs_head_pos proposer dg hs self t i os _ (sub + 1) h
      · rw [List.getElem?_append_left (by omega)] at h
        exact groupRecs_head_pos proposer dg self st t _ e h

/-- The first cut of an engine event is at position `0`. -/
private theorem eventCuts_head_pos (i : Nat) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (h : (eventCuts S rho hn i)[0]? = some r) : r.pos = 0 := by
  rw [eventCuts_eq] at h
  split at h
  · split at h
    · exact groupRecs_head_pos _ _ _ _ _ _ _ h
    · simp at h
  · exact deliverRecs_head_pos _ _ _ _ _ _ _ _ _ h
  · exact groupRecs_head_pos _ _ _ _ _ _ _ h
  · simp at h

/-- The trace cut at engine cut `q` is a boundary of every node: if it is a call, it is the first
cut of its engine event. -/
theorem cutMap_boundary (y : Fin (Fintype.card V)) (q : Nat) :
    Regimes.Boundary (simTraceAt S rho hn) y (cutMap S rho hn q) := by
  rintro ⟨c, hc⟩
  rw [simTraceAt_eq] at hc ⊢
  obtain ⟨r, i, ev, hr, _, hlo, hhi, hri, _, _, hpos, _⟩ :=
    simTrace_cut S rho hn (k := cutMap S rho hn q) (by rw [hc.2]; simp)
  have hiq : cutMap S rho hn i = cutMap S rho hn q := by
    rcases Nat.lt_or_ge i q with h | h
    · have := cutMap_mono S rho hn (show i + 1 ≤ q by omega)
      omega
    · exact le_antisymm hlo (cutMap_mono S rho hn h)
  rw [hiq, Nat.sub_self] at hri
  rw [hpos]
  exact eventCuts_head_pos S rho hn i hri

open Classical in
/-- The engine cut after `v`'s last own event before engine cut `i` (`0` if none). -/
noncomputable def lastOwn (v : V) (i : Nat) : Nat :=
  Nat.findGreatest (fun q => q = 0 ∨ ∃ e, rho.events[q - 1]? = some e ∧ e.node = v) i

open Classical in
/-- `lastOwn v i` is the greatest engine cut `q ≤ i` that is `0` or follows an event of `v`. -/
theorem lastOwn_eq (v : V) (i : Nat) :
    lastOwn S rho v i =
      Nat.findGreatest (fun q => q = 0 ∨ ∃ e, rho.events[q - 1]? = some e ∧ e.node = v) i := by
  rfl

open Classical in
theorem lastOwn_spec (v : V) (i : Nat) :
    lastOwn S rho v i ≤ i ∧ (lastOwn S rho v i = 0 ∨
      ∃ e, rho.events[lastOwn S rho v i - 1]? = some e ∧ e.node = v) := by
  rw [lastOwn_eq]
  exact ⟨Nat.findGreatest_le i, Nat.findGreatest_spec
    (P := fun q => q = 0 ∨ ∃ e, rho.events[q - 1]? = some e ∧ e.node = v) (m := 0)
    (Nat.zero_le i) (Or.inl rfl)⟩

open Classical in
theorem lastOwn_mono (v : V) {i i' : Nat} (h : i ≤ i') :
    lastOwn S rho v i ≤ lastOwn S rho v i' := by
  rw [lastOwn_eq, lastOwn_eq]
  exact Nat.findGreatest_mono_right _ h

open Classical in
/-- No own event between `lastOwn v i` and `i` changes `v`'s engine state. -/
theorem stateAt_lastOwn (v : V) (i : Nat) :
    stateAt S rho hn v i = stateAt S rho hn v (lastOwn S rho v i) := by
  have hq := (lastOwn_spec S rho v i).1
  suffices h : ∀ m, lastOwn S rho v i ≤ m → m ≤ i →
      stateAt S rho hn v m = stateAt S rho hn v (lastOwn S rho v i) from h i hq le_rfl
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ m hm ih =>
    intro hmi
    have hnot := Nat.findGreatest_is_greatest (P := fun q => q = 0 ∨
      ∃ e, rho.events[q - 1]? = some e ∧ e.node = v) (Nat.lt_succ_of_le hm) hmi
    simp only [not_or, not_exists, not_and] at hnot
    cases he : rho.events[m]? with
    | none => rw [stateAt_succ_none S rho hn v he, ih (by omega)]
    | some e => rw [state_of_other S rho hn v m e he (hnot.2 e he), ih (by omega)]

/-- The trace cut after `v`'s last own event before engine cut `i` is a read point at `v`'s
stored clock at `i`, which is the time of that engine cut. -/
theorem lastOwn_readPoint (hv : rho.ExecutionValid) (v : V) (i : Nat) :
    Regimes.ReadPoint (simTraceAt S rho hn) (cutMap S rho hn (lastOwn S rho v i))
        (stateAt S rho hn v i).now ∧
      rho.cutTime (lastOwn S rho v i) = (stateAt S rho hn v i).now := by
  have hs := stateAt_lastOwn S rho hn v i
  obtain ⟨-, hq⟩ := lastOwn_spec S rho v i
  generalize lastOwn S rho v i = q at hs hq ⊢
  rw [simTraceAt_eq, hs]
  cases q with
  | zero =>
    rw [cutMap_zero]
    exact ⟨⟨fun k hk => absurd hk (Nat.not_lt_zero k), by
      rw [stateAt_eq]; exact simTrace_time_nonneg S rho hn hv 0⟩, by rw [stateAt_eq]; rfl⟩
  | succ j =>
    obtain ⟨e, he, hev⟩ : ∃ e, rho.events[j]? = some e ∧ e.node = v := by
      simpa only [Nat.add_one_ne_zero, false_or, Nat.add_sub_cancel] using hq
    rw [now_after_local_event S rho hn hv he hev]
    exact ⟨readPoint_after_event S rho hn hv he, by simp [Model.Run.cutTime, he]⟩

/-- **Every engine output of a node honest at its engine cut is read at the trace cut after its
last own event**, at its stored clock: the trace state there is the node's engine state. Only
honesty at `rho.cutTime i` is used. -/
theorem engine_read_eq_at (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hh : v ∉ rho.faultyAt (rho.cutTime i)) (g : Out) :
    (chainTrace rho).read g v i =
      outOf ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn (lastOwn S rho v i)))
        (stateAt S rho hn v i).now g := by
  have hnT := (now_bounds_cut S rho hn hv v hi).2
  have hhq : v ∉ rho.faultyAt (rho.cutTime (lastOwn S rho v i)) := fun h =>
    hh (rho.faultyAt_mono ((lastOwn_readPoint S rho hn hv v i).2.trans_le hnT) h)
  rw [read_eq_out S rho hn, simTraceAt_state S rho hn hv hhq ((lastOwn_spec S rho v i).1.trans hi),
    ← stateAt_lastOwn]

/-- **The engine reader at its read point.** An engine node ready with catch-up `c + 1` at engine
cut `i` is read at the trace cut `cutMap q` after its last own event, at its stored clock `t`:
a read point at which it is ready with catch-up `c`, in `[0, horizon]`, and its engine
confirmed read is the chain of `readAfter` there. -/
theorem engine_read_point (hv : rho.ExecutionValid) {c : Time} (hc : 0 ≤ c) {v : V}
    {i : Nat} (hi : i ≤ rho.events.length) (hr : rho.point.Ready (c + 1) v (rho.cutTime i)) :
    Regimes.ReadPoint (simTraceAt S rho hn) (cutMap S rho hn (lastOwn S rho v i))
        (stateAt S rho hn v i).now ∧
      0 ≤ (stateAt S rho hn v i).now ∧ (stateAt S rho hn v i).now ≤ rho.horizon ∧
      Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho) c (rho.ownKey v)
        (stateAt S rho hn v i).now ∧
      (chainTrace rho).read .confirmed v i =
        chainTo ((simTraceAt S rho hn).state (rho.ownKey v)
            (cutMap S rho hn (lastOwn S rho v i))).fg.blocks
          ((Regimes.readAfter (simTraceAt S rho hn) (rho.ownKey v)
            (cutMap S rho hn (lastOwn S rho v i)) (stateAt S rho hn v i).now).slot + 1)
          (Regimes.readAfter (simTraceAt S rho hn) (rho.ownKey v)
            (cutMap S rho hn (lastOwn S rho v i)) (stateAt S rho hn v i).now) := by
  have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
  have hih := hlaws.cutTime_le_horizon i hi
  change rho.cutTime i ≤ rho.horizon at hih
  obtain ⟨hn0, hnT⟩ := now_bounds_cut S rho hn hv v hi
  have hnh : (stateAt S rho hn v i).now ≤ rho.horizon := hnT.trans hih
  refine ⟨(lastOwn_readPoint S rho hn hv v i).1, hn0, hnh,
    ready_transport_at S rho hn hv hn0 hnh (ready_at_stored_now S rho hn hv hi hc hr), ?_⟩
  rw [engine_read_eq_at S rho hn hv hi hr.1, outOf]
  rfl

/-- Ancestry, inside the blocks held while honest, of the reads of two nodes each honest at its
read time with every earlier cut no later is a prefix of their confirmed chains. -/
theorem read_prefix (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    {y z : Fin (Fintype.card V)} {j j' : Nat} {t t' : Time}
    (ht : 0 ≤ t) (hj : ∀ k < j, (simTraceAt S rho hn).time k ≤ t) (hy : y ∈ honestKeysAt S rho t)
    (ht' : 0 ≤ t') (hj' : ∀ k < j', (simTraceAt S rho hn).time k ≤ t')
    (hz : z ∈ honestKeysAt S rho t')
    (ha : Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
      (Regimes.readAfter (simTraceAt S rho hn) y j t)
      (Regimes.readAfter (simTraceAt S rho hn) z j' t')) :
    chainTo ((simTraceAt S rho hn).state y j).fg.blocks
        ((Regimes.readAfter (simTraceAt S rho hn) y j t).slot + 1)
        (Regimes.readAfter (simTraceAt S rho hn) y j t) <+:
      chainTo ((simTraceAt S rho hn).state z j').fg.blocks
        ((Regimes.readAfter (simTraceAt S rho hn) z j' t').slot + 1)
        (Regimes.readAfter (simTraceAt S rho hn) z j' t') := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨hri, hΦi, hsi⟩ := held_state hrun ht hj hy
  obtain ⟨hrj, hΦj, hsj⟩ := held_state hrun ht' hj' hz
  have hC : Regimes.readAfter (simTraceAt S rho hn) y j t ∈
      ((simTraceAt S rho hn).state y j).fg.tree :=
    (Regimes.sa_tips (A := ((simTraceAt S rho hn).state y j).ac) hΦi t).1.1
  have hC' : Regimes.readAfter (simTraceAt S rho hn) z j' t' ∈
      ((simTraceAt S rho hn).state z j').fg.tree :=
    (Regimes.sa_tips (A := ((simTraceAt S rho hn).state z j').ac) hΦj t').1.1
  have ha' := anc_in_store hrj hU hsj ha hC'
  have hm : Regimes.readAfter (simTraceAt S rho hn) y j t ∈
      ((simTraceAt S rho hn).state z j').fg.tree := by
    by_cases he : Regimes.readAfter (simTraceAt S rho hn) y j t =
        Regimes.readAfter (simTraceAt S rho hn) z j' t'
    · exact he ▸ hC'
    · exact (Anc.mem ha' he).1
  rw [chainTo_agree hri hrj hU hsi hsj hC hm]
  exact chainTo_prefix hrj ha'

end Consensus.Goldilocks.Obligations.Growing

end
