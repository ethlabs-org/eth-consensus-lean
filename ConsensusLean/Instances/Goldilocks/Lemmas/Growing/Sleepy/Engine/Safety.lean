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

/-! # Finite sleepy safety of the engine under growing faults

* `sleepy_safe_finite_at`: ready-reader safety of the canonical growing trace through `b`, from
  the finite service and the two count shapes through `b` (the static `sleepy_safe_finite`
  without a constant-fault premise).
* `sleepy_safe_engine_at`: the engine's confirmed output is `ReadySafe` with catch-up
  `catchUp + 1` under the L0 sleepy budget with look-ahead `5Δ` through the horizon.

An engine reader is honest at its engine cut, the time of the event before it, while the trace
cut that follows (`cutMap i`) is at the time of the next event (or after the horizon). The reader
is read instead at the trace cut after its last own event, `cutMap q`, at its stored clock: a read
point at which it is ready (the extra unit of catch-up pays for the clock's lag), honest at the
read time with every earlier cut no later. Its state there is its state at the engine cut, and
`Regimes.Growing.ReadySafeOn` applies at those read points. -/

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
private theorem held_state (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
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

/-- **Finite ready-reader safety of the canonical growing trace** through `b ≥ 0`, from the finite
service and the two count shapes through `b`. -/
theorem sleepy_safe_finite_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) {b : Time} (hb0 : 0 ≤ b)
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ b)
    (hB : Compose.Growing.SleepyBounds (simTraceAt S rho hn) (honestKeysAt S rho) b) :
    Regimes.Growing.ReadySafeOn (simTraceAt S rho hn) (honestKeysAt S rho)
      (Regimes.catchUp (S.params (pubOf E) hn)) 0 b :=
  Regimes.Growing.sleepy_safe_at (simTraceAt_goldilocksRun S rho hn hv) hnc hb0 hsync hB

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
private noncomputable def lastOwn (v : V) (i : Nat) : Nat :=
  Nat.findGreatest (fun q => q = 0 ∨ ∃ e, rho.events[q - 1]? = some e ∧ e.node = v) i

open Classical in
private theorem lastOwn_spec (v : V) (i : Nat) :
    lastOwn S rho v i ≤ i ∧ (lastOwn S rho v i = 0 ∨
      ∃ e, rho.events[lastOwn S rho v i - 1]? = some e ∧ e.node = v) := by
  unfold lastOwn
  exact ⟨Nat.findGreatest_le i, Nat.findGreatest_spec
    (P := fun q => q = 0 ∨ ∃ e, rho.events[q - 1]? = some e ∧ e.node = v) (m := 0)
    (Nat.zero_le i) (Or.inl rfl)⟩

open Classical in
private theorem lastOwn_mono (v : V) {i i' : Nat} (h : i ≤ i') :
    lastOwn S rho v i ≤ lastOwn S rho v i' :=
  Nat.findGreatest_mono_right _ h

open Classical in
/-- No own event between `lastOwn v i` and `i` changes `v`'s engine state. -/
private theorem stateAt_lastOwn (v : V) (i : Nat) :
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

/-- **The engine reader at its read point.** An engine node ready with catch-up `c + 1` at engine
cut `i` is read at the trace cut `cutMap q` after its last own event, at its stored clock `t`:
a boundary read point at which it is ready with catch-up `c`, in `[0, horizon]`, and its engine
confirmed read is the chain of `readAfter` there. -/
private theorem engine_read_point (hv : rho.ExecutionValid) {c : Time} (hc : 0 ≤ c) {v : V}
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
  have hs := stateAt_lastOwn S rho hn v i
  obtain ⟨hqi, hq⟩ := lastOwn_spec S rho v i
  have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
  have hih := hlaws.cutTime_le_horizon i hi
  change rho.cutTime i ≤ rho.horizon at hih
  obtain ⟨hn0, hnT⟩ := now_bounds_cut S rho hn hv v hi
  have hnh : (stateAt S rho hn v i).now ≤ rho.horizon := hnT.trans hih
  have hready := ready_transport_at S rho hn hv hn0 hnh
    (ready_at_stored_now S rho hn hv hi hc hr)
  generalize lastOwn S rho v i = q at hs hqi hq ⊢
  -- the read point at the stored clock, which is the time of engine cut `q`
  have hrp : Regimes.ReadPoint (simTraceAt S rho hn) (cutMap S rho hn q)
        (stateAt S rho hn v i).now ∧ rho.cutTime q = (stateAt S rho hn v i).now := by
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
  have hhq : v ∉ rho.faultyAt (rho.cutTime q) := fun h =>
    hr.1 (rho.faultyAt_mono (hrp.2.trans_le hnT) h)
  have hst := simTraceAt_state S rho hn hv hhq (hqi.trans hi)
  refine ⟨hrp.1, hn0, hnh, hready, ?_⟩
  rw [read_eq_out S rho hn, outOf]
  unfold Regimes.readAfter
  rw [hst, ← hs]

/-- Ancestry, inside the blocks held while honest, of the reads of two nodes each honest at its
read time with every earlier cut no later is a prefix of their confirmed chains. -/
private theorem read_prefix (hv : rho.ExecutionValid)
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

/-- **Finite safety of the engine's confirmed output under growing faults.** Under the finite
service and the L0 sleepy budget with look-ahead `5Δ` through the horizon, the confirmed reads of
nodes ready with catch-up `catchUp + 1` at their engine cuts agree, and each such node's reads
only extend. No constant-fault premise: each reader is honest at its own engine cut. -/
theorem sleepy_safe_engine_at (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn))
    (hsync : Compose.Growing.SleepyServiceBefore (simTraceAt S rho hn) (honestKeysAt S rho)
      (S.params (pubOf E) hn).Δ rho.horizon)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 rho.horizon) :
    (chainTrace rho).ReadySafe (Regimes.catchUp (S.params (pubOf E) hn) + 1) .confirmed 0 := by
  have hc0 : 0 ≤ Regimes.catchUp (S.params (pubOf E) hn) := by
    unfold Regimes.catchUp
    linarith [(S.params (pubOf E) hn).toParams.hΔ]
  have hsafe := sleepy_safe_finite_at S rho hn hv hnc hv.horizon_nonneg hsync
    (sleepy_bounds_at S rho hn hv le_rfl hhalf)
  constructor
  · intro u v i j hi hj hu hv'
    obtain ⟨hrp, h0, hh, hra, hread⟩ := engine_read_point S rho hn hv hc0 hi.1 hu
    obtain ⟨hrp', h0', hh', hra', hread'⟩ := engine_read_point S rho hn hv hc0 hj.1 hv'
    rw [hread, hread']
    rcases hsafe.agree _ _ _ _ _ _ hrp hrp' (cutMap_boundary S rho hn _ _)
        (cutMap_boundary S rho hn _ _) h0 hh h0' hh' hra hra' with hc | hc
    · exact Or.inl (read_prefix S rho hn hv hnc h0 hrp.1 hra.1 h0' hrp'.1 hra'.1 hc)
    · exact Or.inr (read_prefix S rho hn hv hnc h0' hrp'.1 hra'.1 h0 hrp.1 hra.1 hc)
  · intro v i j hi hij hj hvi hvj
    obtain ⟨hrp, h0, hh, hra, hread⟩ := engine_read_point S rho hn hv hc0 hi.1 hvi
    obtain ⟨hrp', h0', hh', hra', hread'⟩ := engine_read_point S rho hn hv hc0 hj.1 hvj
    rw [hread, hread']
    exact read_prefix S rho hn hv hnc h0 hrp.1 hra.1 h0' hrp'.1 hra'.1
      (hsafe.mono _ _ _ _ _ hrp hrp' (cutMap_boundary S rho hn _ _)
        (cutMap_boundary S rho hn _ _) (cutMap_mono S rho hn (lastOwn_mono S rho v hij))
        (now_mono S rho hn hv v hij) h0 hh' hra hra')

end Consensus.Goldilocks.Obligations.Growing

end
