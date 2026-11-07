module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Contracts
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArming
import ConsensusLean.Lemmas.Model.SysLog
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace

public section

/-! # Outage engine part under growing faults: the query and its network inputs

`OutageQueryAt` packages a valid collision-free engine run and its outage premise, with no
constant-fault field: the trace is `simTraceAt` and the honest set is `honestKeysAt` (the keys
uncompromised at each time). `OutageQuery.toAt` forgets the constant-fault field of a static
query.

* `outage_pre_service_at`: the finite Sleepy service through the outage start, saturating at
  the engine horizon;
* `outage_psync_at`: the engine's partial synchrony from the outage stop;
* `outage_receiver_service_at`: every receiver gets the receiver service after the stop;
* `outage_pool_delivery_query_at`: an update of a restored label, by a node honest at it, holds
  every vote of that slot by a node honest at its cast;
* the numbers of the query (`outage_node_lag_at`, `outage_window_cover_at`, `query_numbers_at`,
  the restored label), the cohort `holdersAt` and its late wakers `lateKeysAt`, read on the view
  retained through the cohort time `cohortAt = outageEnd` (no cohort look-ahead). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Blocks Shape
variable (S : Setup) (A : ContractAssumptions S) (V : Type)
  [Fintype V] [DecidableEq V]

/-- **An outage query under growing faults**: a valid collision-free run with its outage
premise. -/
structure OutageQueryAt where
  run : (Sys (goldilocks S) V).Run
  hn : 1 ≤ Fintype.card V
  T : Time
  start : Time
  stop : Time
  valid : (Sys (goldilocks S) V).Valid run
  noCollision : ¬ run.2.HashCollision
  outage : (Sys (goldilocks S) V).Outage (K S A) T start stop run

variable {S A V}

/-- A static outage query, with its constant-fault field forgotten. -/
def _root_.Consensus.Goldilocks.Obligations.OutageQuery.toAt (Q : OutageQuery S A V) :
    OutageQueryAt S A V :=
  ⟨Q.run, Q.hn, Q.T, Q.start, Q.stop, Q.valid, Q.noCollision, Q.outage⟩

namespace OutageQueryAt
abbrev params (Q : OutageQueryAt S A V) := S.params (Model.pubOf Q.run.1) Q.hn
noncomputable abbrev trace (Q : OutageQueryAt S A V) := simTraceAt S Q.run.2 Q.hn
noncomputable abbrev keys (Q : OutageQueryAt S A V) := honestKeysAt S Q.run.2
noncomputable abbrev duration (Q : OutageQueryAt S A V) :=
  (Sys (goldilocks S) V).cDur (K S A) Q.run
end OutageQueryAt

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
    (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.2.1.1
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
  (Model.sysOf_delivers_iff _ _ _ _).mp Q.outage.2.1.2

/-- **The receiver service after the stop**, for every receiver. -/
theorem outage_receiver_service_at (Q : OutageQueryAt S A V) (y : Fin (Fintype.card V)) :
    Compose.Growing.ReceiverServiceAfterAt Q.keys (Q.trace.HonestBlocksAt Q.keys) Q.stop y
      Q.trace.projAC :=
  receiverServiceAfterAt_of_psync S Q.run.2 Q.hn Q.valid
    (noCollRun_simTraceAt S Q.run.2 Q.hn Q.valid Q.noCollision) (outage_psync_at Q) y

/-- **Post-stop pool delivery**: an update of a slot `m` with `b₁ ≤ t_m + Δ`, by a node honest at
it, holds every slot-`m` vote of a node honest at its cast. -/
theorem outage_pool_delivery_query_at (Q : OutageQueryAt S A V) :
    ∀ w c m ℓ, w ∈ Q.keys (Q.trace.time c) → SA.UpdateAt Q.trace.projAC w c m ℓ →
      Q.stop ≤ Q.params.ts m + Q.params.Δ →
      ∀ x i e, x ∈ Q.keys (Q.trace.time i) → SA.VoteAt Q.trace.projAC x i e → e.msg.slot = m →
        e.msg ∈ (Q.trace.state w c).ac.pool m :=
  outage_pool_delivery_at S Q.run.2 Q.hn Q.valid
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
  obtain ⟨⟨-, hlag, -, -⟩, -⟩ := Q.outage
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hk : (0 : Time) ≤ S.k := by positivity
  change Q.T + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC ≤ Q.start at hlag
  change Q.T + (4 * (S.k : Int) + 6) * Q.run.1.ΔAC ≤ Q.start
  push_cast at hlag
  linarith

/-- (A4)/(A5) The no-sleep window `[a, z]` starts by `t_{j₀−k}` (from `0`) and ends at or after
every update of a label `≤ j₀` within the horizon. -/
theorem outage_window_cover_at (Q : OutageQueryAt S A V) :
    0 ≤ (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ∧
      (Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run ≤
        Q.params.ts ((Compose.coverLabel Q.params Q.start : Int) - Q.params.k) ∧
      ∀ d ≤ 6 * Q.params.Δ, Q.params.ts (Compose.coverLabel Q.params Q.start) + d ≤
          Q.run.2.horizon →
        Q.params.ts (Compose.coverLabel Q.params Q.start) + d ≤
          (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run := by
  obtain ⟨⟨hT, -, hb01, -⟩, -⟩ := Q.outage
  have hlag := outage_node_lag_at Q
  have hΔ := Q.params.toParams.hΔ
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hk : (0 : Time) ≤ S.k := by positivity
  have hkj := (Compose.armed_label_lt (σ := 0) hT hlag (by simp [SA.SAParams.ts]; exact hT)).2
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    linarith)
  have hhor : 0 ≤ Q.run.2.horizon := Q.valid.horizon_nonneg
  have hC : ((4 * S.k + 6 : Nat) : Int) = 4 * (S.k : Int) + 6 := by push_cast; ring
  set j₀ := Compose.coverLabel Q.params Q.start
  have hkj' : ((S.k : Nat) : Int) < j₀ := by exact_mod_cast hkj
  change 0 ≤ min (max 0 (Q.start - ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC))
      Q.run.2.horizon ∧
    min (max 0 (Q.start - ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC)) Q.run.2.horizon ≤
      4 * Q.run.1.ΔAC * ((j₀ : Int) - S.k) ∧
    ∀ d ≤ 6 * Q.run.1.ΔAC, 4 * Q.run.1.ΔAC * (j₀ : Int) + d ≤ Q.run.2.horizon →
      4 * Q.run.1.ΔAC * (j₀ : Int) + d ≤
        min (Q.stop + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC) Q.run.2.horizon
  change 4 * Q.run.1.ΔAC * (j₀ : Int) + 2 * Q.run.1.ΔAC ≤ Q.start at hg₁
  change Q.start < 4 * Q.run.1.ΔAC * (j₀ : Int) + 6 * Q.run.1.ΔAC at hg₂
  refine ⟨le_min (le_max_left _ _) hhor, (min_le_left _ _).trans (max_le ?_ ?_),
    fun d hd6 hdh => le_min ?_ hdh⟩
  · have : (0 : Time) ≤ (j₀ : Int) - S.k := by linarith
    positivity
  · rw [hC]
    linarith
  · rw [hC]
    linarith [mul_nonneg hk (zero_le_one.trans hd)]

/-- The first restored label: the least `r` with `b₁ ≤ t_r + Δ`. -/
noncomputable def OutageQueryAt.restoredLabel (Q : OutageQueryAt S A V) : Nat := by
  classical
  exact if h : ∃ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ then Nat.find h else 0

/-- The numbers of an outage query in node units: the gates of the cover label, the restored
label in `(j₀, j₀ + k]`, the budget and the no-sleep window, whose end covers every time up to
`t_{j₀+k} + 6Δ` within the horizon. -/
theorem query_numbers_at (Q : OutageQueryAt S A V) :
    let j₀ := Compose.coverLabel Q.params Q.start
    Q.params.ts j₀ + 2 * Q.params.Δ ≤ Q.start ∧
      Q.start < Q.params.ts (j₀ + 1 : Nat) + 2 * Q.params.Δ ∧
      Q.stop - Q.start ≤ (4 * (Q.params.k : Time) - 5) * Q.params.Δ ∧
      Q.start ≤ Q.stop ∧ Q.stop ≤ Q.params.ts (j₀ + Q.params.k : Nat) + Q.params.Δ ∧
      Q.params.ts (j₀ : Nat) + Q.params.Δ < Q.stop ∧
      (∀ t, t ≤ Q.params.ts (j₀ + Q.params.k : Nat) + 6 * Q.params.Δ → t ≤ Q.run.2.horizon →
        t ≤ (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run) := by
  intro j₀
  obtain ⟨⟨hT, -, hb01, hbud⟩, -⟩ := Q.outage
  have hlag := outage_node_lag_at Q
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hk2 : (2 : Int) ≤ S.k := by exact_mod_cast S.two_le_k
  obtain ⟨hg₁, hg₂⟩ := Compose.coverLabel_gates (sp := Q.params) (b₀ := Q.start) (by
    have : (0 : Time) ≤ (4 * Q.params.k + 4) * Q.params.Δ := by positivity
    have hΔ := Q.params.toParams.hΔ
    linarith)
  have hbcast : ((4 * S.k - 5 : Nat) : Int) = 4 * (S.k : Int) - 5 := by omega
  have hb : ((4 * S.k - 5 : Nat) : Int) ≤ 4 * (S.k : Int) - 5 := hbcast.le
  change Q.stop ≤ Q.start + ((4 * S.k - 5 : Nat) : Int) * Q.run.1.ΔAC at hbud
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt Q.run.1.ΔAC_pos)
  change 4 * Q.run.1.ΔAC * (j₀ : Int) + 2 * Q.run.1.ΔAC ≤ Q.start at hg₁
  change Q.start < 4 * Q.run.1.ΔAC * (j₀ : Int) + 6 * Q.run.1.ΔAC at hg₂
  change 4 * Q.run.1.ΔAC * (j₀ : Int) + 2 * Q.run.1.ΔAC ≤ Q.start ∧
    Q.start < 4 * Q.run.1.ΔAC * ((j₀ + 1 : Nat) : Int) + 2 * Q.run.1.ΔAC ∧
    Q.stop - Q.start ≤ (4 * (S.k : Time) - 5) * Q.run.1.ΔAC ∧ Q.start ≤ Q.stop ∧
    Q.stop ≤ 4 * Q.run.1.ΔAC * ((j₀ + S.k : Nat) : Int) + Q.run.1.ΔAC ∧
    4 * Q.run.1.ΔAC * ((j₀ : Nat) : Int) + Q.run.1.ΔAC < Q.stop ∧
    ∀ t, t ≤ 4 * Q.run.1.ΔAC * ((j₀ + S.k : Nat) : Int) + 6 * Q.run.1.ΔAC →
      t ≤ Q.run.2.horizon →
      t ≤ min (Q.stop + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC) Q.run.2.horizon
  push_cast
  refine ⟨hg₁, by linarith, by linarith, hb01, by linarith, by linarith,
    fun t ht hth => le_min ?_ hth⟩
  linarith

/-- The restored label is the least `r` with `b₁ ≤ t_r + Δ`. -/
theorem restoredLabel_spec (Q : OutageQueryAt S A V) :
    Q.stop ≤ Q.params.ts Q.restoredLabel + Q.params.Δ ∧
      ∀ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ → Q.restoredLabel ≤ s := by
  classical
  obtain ⟨-, -, -, -, hK, -, -⟩ := query_numbers_at Q
  have h : ∃ s : Nat, Q.stop ≤ Q.params.ts s + Q.params.Δ := ⟨_, hK⟩
  unfold OutageQueryAt.restoredLabel
  simp only [h, ↓reduceDIte]
  exact ⟨Nat.find_spec h, fun s hs => Nat.find_min' h hs⟩

/-- The cohort: the validators uncompromised at the cohort time and awake at the window start,
as keys (read on the view retained through the cohort time). -/
noncomputable def OutageQueryAt.holdersAt (Q : OutageQueryAt S A V) :
    Set (Fin (Fintype.card V)) :=
  {x | Q.run.2.key x ∈ (Q.run.2.point.retain ((Sys (goldilocks S) V).cohortAt (K S A) Q.stop
    Q.run)).awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)}

/-- The cohort's late wakers, as keys (read on the view retained through the cohort time). -/
noncomputable def OutageQueryAt.lateKeysAt (Q : OutageQueryAt S A V) :
    Set (Fin (Fintype.card V)) :=
  {x | Q.run.2.key x ∈ (Q.run.2.point.retain ((Sys (goldilocks S) V).cohortAt (K S A) Q.stop
    Q.run)).lateWakers ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
      ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run)}

theorem OutageQueryAt.mem_holdersAt {Q : OutageQueryAt S A V} {x : Fin (Fintype.card V)} :
    x ∈ Q.holdersAt ↔ Q.run.2.key x ∈ (Q.run.2.point.retain ((Sys (goldilocks S) V).cohortAt
      (K S A) Q.stop Q.run)).awakeAt ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run) :=
  Iff.rfl

theorem OutageQueryAt.mem_lateKeysAt {Q : OutageQueryAt S A V} {x : Fin (Fintype.card V)} :
    x ∈ Q.lateKeysAt ↔ Q.run.2.key x ∈ (Q.run.2.point.retain ((Sys (goldilocks S) V).cohortAt
      (K S A) Q.stop Q.run)).lateWakers ((Sys (goldilocks S) V).outageStart (K S A) Q.start Q.run)
        ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run) :=
  Iff.rfl

/-- With no cohort look-ahead, the cohort is charged at the window end. -/
theorem OutageQueryAt.cohortAt_eq (Q : OutageQueryAt S A V) :
    (Sys (goldilocks S) V).cohortAt (K S A) Q.stop Q.run =
      (Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run := by
  change min ((Sys (goldilocks S) V).outageEnd (K S A) Q.stop Q.run + ((0 : Nat) : Int) *
    Q.run.1.ΔAC) Q.run.2.horizon = _
  simp only [Nat.cast_zero, zero_mul, add_zero]
  exact min_eq_left (min_le_right _ _)

/-- The sleepy look-ahead of the contract is `5Δ`. -/
theorem OutageQueryAt.aheadDur_eq (Q : OutageQueryAt S A V) :
    (Sys (goldilocks S) V).aheadDur (K S A) Q.run = 5 * Q.params.Δ := by
  change ((5 : Nat) : Int) * Q.run.1.ΔAC = 5 * Q.run.1.ΔAC
  norm_num

end Consensus.Goldilocks.Obligations.Growing

end
