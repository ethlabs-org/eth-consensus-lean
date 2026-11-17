module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.ReceiverService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PoolDelivery
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Window
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Transport
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Reads
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArmingSteps
import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace

public section

/-! # Outage engine part under growing faults: the query and its network inputs

`OutageQueryAt` (`Obligations/Growing/Queries/Defs`) packages a valid collision-free engine run
and its outage premise, with no constant-fault field: the trace is `simTraceAt` and the honest set
is `honestKeysAt` (the keys uncompromised at each time).

* `outage_pre_service_at`: the finite Sleepy service through the outage start, saturating at
  the engine horizon;
* `outage_psync_at`: the engine's partial synchrony from the outage stop;
* `outage_postStopService_at`: post-stop service on the canonical trace;
* the numbers of the query (`outage_node_lag_at`, `outage_window_cover_at`, `query_numbers_at`,
  the restored label) on the proof window `[a, z]` (`winStart`, `winEnd`: the outage widened by
  `(4k + 6)Δ` on both sides, clamped to `[0, horizon]`), whose length is at most the look-back
  `η·Δ = (12k + 7)Δ` (`look_back_le_winStart`);
* the holders `holdersAt`: the validators ready at `z` with the outage catch-up
  `outCatch = max cDur (η·Δ − 1)`, and its opponents `opponentsAt`: the other validators awake in
  the look-back `[max 0 (z − η·Δ), z]`, both read on the view retained through `z`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V] [DecidableEq V]

/-- A call of the trace is at or before the engine horizon. -/
theorem OutageQueryAt.call_le_horizon (Q : OutageQueryAt S A V) {y : Fin (Fintype.card V)}
    {j : Nat} (hj : Q.trace.IsCall y j) : Q.trace.time j ≤ Q.run.2.horizon := by
  obtain ⟨l, hl⟩ := hj
  exact simTraceAt_labelled_time_le S Q.run.2 Q.hn Q.valid (by rw [hl.2]; simp)

/-- **Pre-outage service through the start**, saturating at the finite engine horizon: only
labelled recipient cuts require service. -/
theorem outage_pre_service_at (Q : OutageQueryAt S A V) :
    Compose.Growing.SleepyServiceBefore Q.trace Q.keys Q.params.Δ Q.start := by
  let b := min Q.start Q.run.2.horizon
  have h0 : Q.run.2.log.SyncUntil Q.run.2.point Q.start :=
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.net.1
  have hnet : Q.run.2.log.SyncUntil Q.run.2.point b :=
    CommLog.Delivers.reindex h0 (f := id) (fun _ => le_rfl) (fun _ => rfl) (fun _ => rfl)
      (min_le_left _ _)
  have service := sleepyServiceBefore_of_syncUntil_at S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision)
    (min_le_right Q.start Q.run.2.horizon) hnet
  refine ⟨service.deltaF, ?_, ?_, ?_⟩
  · intro x i m hx hi h0 y j l hy hj hb hd
    exact service.message x i m hx hi h0 y j l hy hj
      (le_min hb (hd.trans (Q.call_le_horizon ⟨_, Compose.projAC_callAt.mp hj⟩))) hd
  · intro x i B hx hi h0 y j l hy hj hb hd hF
    exact service.acRelay x i B hx hi h0 y j l hy hj
      (le_min hb (hd.trans (Q.call_le_horizon ⟨_, Compose.projAC_callAt.mp hj⟩))) hd hF
  · intro x i B hx hi h0 y j hy hj hb hd hF
    exact service.relay x i B hx hi h0 y j hy hj
      (le_min hb (hd.trans (Q.call_le_horizon hj))) hd hF

/-- PSync from the outage's stop on the engine log. -/
theorem outage_psync_at (Q : OutageQueryAt S A V) : Q.run.2.log.PSync Q.run.2.point Q.stop :=
  (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.net.2

/-- Post-stop service on the query's canonical node trace. -/
theorem outage_postStopService_at (Q : OutageQueryAt S A V) :
    Generic.PostStopService Q.trace Q.keys Q.stop :=
  goldilocks_postStopService S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) (outage_psync_at Q)

/-- The catch-up duration of an outage query covers the node catch-up `18Δ`. -/
theorem outage_duration_supply_at (Q : OutageQueryAt S A V) :
    Regimes.catchUp Q.params ≤ Q.duration := by
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  simp only [OutageQueryAt.duration, System.cDur, Params.standard, contract_coefficients_catchUp]
  change 18 * Q.run.1.ΔAC ≤ (contract_catchUp S A : Nat) * Q.run.1.ΔAC
  linarith [mul_le_mul_of_nonneg_right hc (zero_le_one.trans hd)]

/-- (A1) The lag `4k + 6` is the node lag `(4k+6)Δ`. -/
theorem outage_node_lag_at (Q : OutageQueryAt S A V) :
    Q.T + (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  obtain ⟨-, hlag, -, -⟩ := Q.outage.times
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hk : (0 : Time) ≤ S.k := by positivity
  change Q.T + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC ≤ Q.start at hlag
  change Q.T + (4 * (S.k : Int) + 6) * Q.run.1.ΔAC ≤ Q.start
  push_cast at hlag
  linarith

private theorem outage_budget_at (Q : OutageQueryAt S A V) :
    Q.stop ≤ Q.start + (4 * (Q.params.k : Time) - 5) * Q.params.Δ := by
  have hbud := Q.outage.times.2.2.2
  have hk2 : (2 : Int) ≤ S.k := by exact_mod_cast S.two_le_k
  have hbcast : ((4 * S.k - 5 : Nat) : Int) = 4 * (S.k : Int) - 5 := by omega
  change Q.stop ≤ Q.start + ((4 * S.k - 5 : Nat) : Int) * Q.run.1.ΔAC at hbud
  change Q.stop ≤ Q.start + (4 * (S.k : Int) - 5) * Q.run.1.ΔAC
  rwa [hbcast] at hbud

/-- The start `a` of the proof window: `b₀ − (4k + 6)Δ`, clamped to `[0, horizon]`. -/
abbrev OutageQueryAt.winStart (Q : OutageQueryAt S A V) : Time :=
  min (max 0 (Q.start - ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC)) Q.run.2.horizon

/-- The end `z` of the proof window: `b₁ + (4k + 6)Δ`, clamped to the horizon. -/
abbrev OutageQueryAt.winEnd (Q : OutageQueryAt S A V) : Time :=
  min (Q.stop + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC) Q.run.2.horizon

/-- The look-back `η·Δ` of the outage premise. -/
noncomputable abbrev OutageQueryAt.lookBack (Q : OutageQueryAt S A V) : Time :=
  ((K S A).params.η : Time) * Q.run.1.ΔAC

/-- The participation catch-up of the outage premise, `max cDur (η·Δ − 1)`. -/
noncomputable abbrev OutageQueryAt.outCatch (Q : OutageQueryAt S A V) : Time :=
  max Q.duration (Q.lookBack - 1)

/-- **The look-back covers the proof window**: `[max 0 (z − η·Δ), z]` starts at or before `a`,
since `z − a ≤ (budget + 2(4k + 6))Δ = (12k + 7)Δ` away from the clamps. -/
theorem look_back_le_winStart (Q : OutageQueryAt S A V) :
    max 0 (Q.winEnd - Q.lookBack) ≤ Q.winStart := by
  have h := (Compose.Growing.outage_window_numbers Q.outage.times.1
    (outage_node_lag_at Q) Q.outage.times.2.2.1 (outage_budget_at Q)
    Q.valid.horizon_nonneg).2.2
  simpa [Compose.Growing.outageWinStart_eq, Compose.Growing.outageWinEnd_eq,
    OutageQueryAt.winStart, OutageQueryAt.winEnd, OutageQueryAt.lookBack,
    OutageQueryAt.params, Params.standard, K, Nat.cast_add, Nat.cast_mul] using h

/-- **Readiness at `z` covers the proof window**: the outage catch-up `η·Δ − 1` reaches back to
`max 0 (z − η·Δ) ≤ a`. -/
theorem ready_window_le_winStart (Q : OutageQueryAt S A V) :
    max 0 (Q.winEnd - Q.outCatch - 1) ≤ Q.winStart :=
  le_trans (max_le_max le_rfl (by linarith [le_max_right Q.duration (Q.lookBack - 1)]))
    (look_back_le_winStart Q)

/-- (A4)/(A5) The proof window `[a, z]` starts by `t_{j₀−k}` (from `0`) and ends at or after
every update of a label `≤ j₀` within the horizon. -/
theorem outage_window_cover_at (Q : OutageQueryAt S A V) :
    0 ≤ Q.winStart ∧ Q.winStart ≤
        Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ∧
      ∀ d ≤ 6 * Q.params.Δ, Q.params.ts (Compose.coverLabel Q.params Q.start) + d ≤
          Q.run.2.horizon →
        Q.params.ts (Compose.coverLabel Q.params Q.start) + d ≤ Q.winEnd := by
  have h := (Compose.Growing.outage_window_numbers Q.outage.times.1
    (outage_node_lag_at Q) Q.outage.times.2.2.1 (outage_budget_at Q)
    Q.valid.horizon_nonneg).2.1
  simpa [Compose.Growing.outageWinStart_eq, Compose.Growing.outageWinEnd_eq,
    OutageQueryAt.winStart, OutageQueryAt.winEnd, OutageQueryAt.params,
    Params.standard, Nat.cast_add, Nat.cast_mul] using h

/-- The numbers of an outage query in node units: the gates of the cover label, the restored
label in `(j₀, j₀ + k]`, the budget and the proof window, whose end covers every time up to
`t_{j₀+k} + 6Δ` within the horizon. -/
theorem query_numbers_at (Q : OutageQueryAt S A V) :
    let j₀ := Compose.coverLabel Q.params Q.start
    Q.params.ts j₀ + 2 * Q.params.Δ ≤ Q.start ∧
      Q.start < Q.params.ts (j₀ + 1 : Nat) + 2 * Q.params.Δ ∧
      Q.stop - Q.start ≤ (4 * (Q.params.k : Time) - 5) * Q.params.Δ ∧
      Q.start ≤ Q.stop ∧ Q.stop ≤ Q.params.ts (j₀ + Q.params.k : Nat) + Q.params.Δ ∧
      Q.params.ts (j₀ : Nat) + Q.params.Δ < Q.stop ∧
      (∀ t, t ≤ Q.params.ts (j₀ + Q.params.k : Nat) + 6 * Q.params.Δ → t ≤ Q.run.2.horizon →
        t ≤ Q.winEnd) := by
  have h := (Compose.Growing.outage_window_numbers Q.outage.times.1
    (outage_node_lag_at Q) Q.outage.times.2.2.1 (outage_budget_at Q)
    Q.valid.horizon_nonneg).1
  simpa [Compose.Growing.outageWinEnd_eq, OutageQueryAt.winEnd,
    OutageQueryAt.params, Params.standard, Nat.cast_add, Nat.cast_mul] using h

/-- The restored label is the least `r` with `b₁ ≤ t_r + Δ`. -/
theorem restoredLabel_spec (Q : OutageQueryAt S A V) :
    Q.stop ≤ Q.params.ts (Compose.Growing.outageRestoredLabel Q.params Q.stop) + Q.params.Δ ∧
      ∀ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ →
        Compose.Growing.outageRestoredLabel Q.params Q.stop ≤ s := by
  exact Compose.Growing.outageRestoredLabel_spec Q.outage.times.1
    (outage_node_lag_at Q) Q.outage.times.2.2.1 (outage_budget_at Q)

/-- The holders: the validators ready at the window end with the outage catch-up, as keys (read on
the view retained through the window end). -/
noncomputable def OutageQueryAt.holdersAt (Q : OutageQueryAt S A V) :
    Set (Fin (Fintype.card V)) :=
  {x | Q.run.2.key x ∈ (Q.run.2.point.retain Q.winEnd).readyAt Q.outCatch Q.winEnd}

/-- The look-back opponents among the honest validators, as keys: awake at a time of the look-back
`[max 0 (z − η·Δ), z]` but not ready at `z` (read on the view retained through `z`). -/
noncomputable def OutageQueryAt.opponentsAt (Q : OutageQueryAt S A V) :
    Set (Fin (Fintype.card V)) :=
  {x | Q.run.2.key x ∈ (Q.run.2.point.retain Q.winEnd).awakeIn (max 0 (Q.winEnd - Q.lookBack))
    Q.winEnd \ (Q.run.2.point.retain Q.winEnd).readyAt Q.outCatch Q.winEnd}

theorem OutageQueryAt.mem_holdersAt {Q : OutageQueryAt S A V} {x : Fin (Fintype.card V)} :
    x ∈ Q.holdersAt ↔
      Q.run.2.key x ∈ (Q.run.2.point.retain Q.winEnd).readyAt Q.outCatch Q.winEnd :=
  Iff.rfl

theorem OutageQueryAt.mem_opponentsAt {Q : OutageQueryAt S A V} {x : Fin (Fintype.card V)} :
    x ∈ Q.opponentsAt ↔ Q.run.2.key x ∈ (Q.run.2.point.retain Q.winEnd).awakeIn
      (max 0 (Q.winEnd - Q.lookBack)) Q.winEnd \
        (Q.run.2.point.retain Q.winEnd).readyAt Q.outCatch Q.winEnd :=
  Iff.rfl

end Consensus.Goldilocks.Obligations.Growing

end
