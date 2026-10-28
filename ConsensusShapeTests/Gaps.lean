module
public import ConsensusShapeTests.Regimes
public import ConsensusShapeTests.Vacuity
public import ConsensusShapeTests.Network
public import ConsensusShapeTests.Problem
public import ConsensusShapeTests.Blocks
public import ConsensusShapeTests.Goldilocks
public import Mathlib.Tactic
@[expose] public section

/-! # Gap dispositions (M1–M39)

Each row of the merged gap list (`gapreview/gaps-merged.md`, M1–M39) and the
"vacuous system" row has one disposition, and is backed by a test, an
`example` below, a sheet reference (checked here by naming the declaration),
or a stated reason. Plan: iteration 6, §8.

Kinds: **by construction** (the fixed L0 definition already says it; an
`example` shows the one-liner), **test** (a named test theorem), **sheet** (a
`GoldilocksTarget` theorem or `GoldilocksExtra` field, `GoldilocksSheet.lean`),
**obligation** (a numbered FG-SA migration obligation in the sheet),
**scope** (outside the definition, with the reason), **removed** (the gap's
object no longer exists).

* **M1 weak continuation**: generic: the healed regime stays healthy to the horizon
  ("stay in recovery"; `example` M1); precise forms: sheet `weakSafe`, `weakInclude`,
  `weakGrow`; cut/seed uniformity: obligation (10).
* **M2 corruption growth**: scope: static adversary (`EnvPoint.honest` is fixed per
  run); sheet §3 (A6).
* **M3 FE/F4 pattern**: `Pattern.range`; Goldilocks final progress `range (3R+κ)`
  (`pp223_numbers`, `finRec_span`); `range_head` (with the span loss); FE/F4 equivalence
  is migration gate F-2.
* **M4 psync not mandated**: by construction: `DAClaims.healedSafe`/`healedLive`,
  `FinalClaims.live` are fields of `Behaviour`, fixed in `Good` (`example` M4); test
  `healed_witness_late`.
* **M5 final safety under asynchrony**: by construction: `FinalClaims.accountable` has
  premise `True`; `Good.final_agree` needs no network premise (`example` M5).
* **M6 syncUntil not checked**: removed: no premise language; `SyncUntil` is an L0
  network definition used only inside the fixed outage regime and the prefix forms.
* **M7 late GST**: `Realizable.healthy` ∀ Δ, g (`regimes_realizable`); test
  `healed_witness_late` (Δ = 7, GST 1000, no receipt before 1000).
* **M8 trivial outage**: `OutageActive` in `Realizable.outage` (a sleeper in the window,
  `b₀ + Δ ≤ b₁`, a protected source, an eligible reader); tests `outage_async_log`,
  `outage_witness_late` (armed at ≥ 1000·Δ), `outage_control`.
* **M9 dynamic participation**: by construction: the sleepy regime is `ReadyAbove θ`
  with `θ ≤ ½`; test `sleepy_with_sleeper` (sleepy with a sleeper, not healthy).
* **M10 thresholds**: `Params.Admissible`; tests `admissibility_rejections` (θ 3/5, φ
  9/10, cover 3/5, α 1/4, budget 0, catch-up 0), `standard_admissible`,
  `outage_times_teeth`, `healthy_needs_two_thirds`.
* **M11 wake at GST**: `HealthyOn` counts a fixed awake set (no catch-up); progress from
  `readyFrom`; test `healthy_wake_at_gst`.
* **M12 inclusion of every proposal**: sheet `includeSleepy`, `includeHealed`.
* **M13 window-only P1**: sheet `outageWindow`; test `outageWindow_prefix_only`.
* **M14 outage: stable / finalized**: closed: stable aliased to confirmed
  (`stable_is_confirmed`, sheet `confirmed_persists`); finalized via
  `Good.persists_final_compatible` (sheet `outage_final_compatible`).
* **M15 pinned params**: `goldilocksContract`, `goldilocks_admissible`,
  `reference_bounds`; test `pp223_numbers`.
* **M16 concrete instance**: migration (out of this iteration): `GoldilocksTarget` is
  the reviewed target, unproved.
* **M17 eventual liveness**: scope: liveness is bounded-latency (`TxLive` with a
  deadline); eventual liveness is weaker and implied on every run whose horizon passes
  the deadline.
* **M18 adaptive corruption**: scope: static adversary.
* **M19 weights / committees**: scope: equal-weight validators (`Fintype V`, counts).
* **M20 cross-node nesting**: sheet `crossNest`, `liveDC`.
* **M21 recovery fault bound**: by construction: `HealthyOn.faultsBelow` and `1 − φ ≤ α`
  (`Good.final_safe_healthy`); test `faulty_third_not_healthy`
  (`example` M21).
* **M22 instance vs FG-SA**: migration obligations (1)–(12) in the sheet.
* **M23 cover / budget**: sheet `budget_implies_V`; cover ½ vs FG-SA `OutageE`:
  obligation (4).
* **M24 reader scope**: by construction: `ReadySafe` (ready readers) for
  available/stable, `Safe`/`AccountablySafe` (every honest reader) for final (`example`
  M24).
* **M25 ready vs awake**: healthy counts a fixed set of honest validators awake
  throughout (Francesco override 2, no churn); readers and progress count ready; test
  `healthy_rotating_sleeper` (⅔ awake at each tick, rejected); obligation (6).
* **M26 single Δ**: scope: one `Δ` (`Δ_F = Δ`).
* **M27 Δ = 1 witnesses**: `Realizable` quantifies every `Δ`; test `healed_witness_late`
  at `Δ = 7`.
* **M28 recovery starts**: by construction: `healPoint = max g 0 + heal·Δ` (catch-up
  inside `heal`), progress from `readyFrom c g = max g 0 + c + 1` (`example` M28).
* **M29 faulty proposer witnesses**: `ProgressFits` (a recurrence fits only `.sized 1`);
  tests `allProposers_unfit`, `allProposers_no_witness`, `recurrence_has_teeth`.
* **M30 safety vs liveness regime**: by construction: same `Healthy` regime; safety's
  progress window `[ready, heal]` is inside liveness's `[ready, horizon]`
  (`Progress.mono`; `example` M30).
* **M31 validity**: scope: no transaction/state validity; `TxLive` serves every
  submission.
* **M32 capacity**: scope: no bounded blocks, admission or backlog.
* **M33 chain quality**: scope: no quantitative chain quality or growth beyond the
  sheet's growth extras.
* **M34 conditional accountability**: reason: accountability is unconditional and from
  time `0` (premise `True`), which is stronger.
* **M35 one GST / one outage**: partially closed: the prefix forms
  (`Good.sleepySafe_prefix`, `healedSafe_prefix`, `outage_prefix`) cover the past before
  any later asynchrony (test `prefix_sync_then_async`); a run after an outage is
  partially synchronous with GST `b₁` (`example` M35), so the after-GST claims apply
  when their participation holds; several GSTs or outages: scope.
* **M36 leak, HP latency**: scope; sheet §3 (K1–K5, FL7/FL8).
* **M37 model adequacy**: `System.Adequate` (L0) with `Model.sysOf_adequate`; the log is
  the engine's (`Model.sysOf_log_faithful`, `Model.Run.held_iff_served`); test
  `silent_run_valid`.
* **M38 global escape**: removed: local accountability only; test
  `local_accountability_teeth`.
* **M39 HEAD**: scope: HEAD is protocol-internal; sheet §3.
* **vacuous system**: `Good = Behaviour ∧ Adequate ∧ Realizable`; tests
  `false_progress_not_good`, `empty_valid_not_good`, `excuse_true_not_good`,
  `no_admissible_not_good`.
-/

namespace Consensus.Shape.Tests.Gaps
open Consensus Blocks Shape

section Generic

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

/- M1: the healed regime requires the fixed healthy set awake to the horizon
("stay in recovery"); a run that leaves it is outside the regime. -/
example (r : S.Run) (g : Time) (h : S.Healthy K g r) :
    (S.pt r).HealthyOn K.params.φ g (S.pt r).horizon := h.2

/- M4: partially synchronous safety and liveness are mandated: they are
fields of the fixed behaviour table. -/
example (h : Good S X K) (cap : Capability) (g : S.schema.Id)
    (hc : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g) (i : K.Idx)
    (gst : Time) :
    S.Holds (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K cap i gst r) (S.lat K cap i r)) :=
  (h.behaviour.da cap g hc hg).healedLive i gst

/- M5: final agreement below `α` faults, under any network (no regime). -/
example (h : Good S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) (r : S.Run)
    (hv : S.Valid r) (hb : (S.pt r).FaultsBelow K.params.α) :
    (S.trace r).Agree g 0 ∨ S.Excuse r :=
  h.final_agree hg r hv hb

/- M21: the healthy regime bounds the faults below `1 − φ ≤ α`, so final
safety holds there. -/
example (r : S.Run) (g : Time) (h : S.Healthy K g r) :
    (S.pt r).FaultsBelow (1 - K.params.φ) := h.2.faultsBelow

example (h : Good S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) (r : S.Run)
    (hv : S.Valid r) {gst : Time} (hH : S.Healthy K gst r) :
    (S.trace r).Safe g 0 ∨ S.Excuse r :=
  h.final_safe_healthy hg r hv hH

/- M24: available/stable safety is for ready readers (`ReadySafe`), final
accountability for every honest reader, unconditionally. -/
example (h : Good S X K) (cap : Capability) (g : S.schema.Id)
    (hc : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g) :
    S.Holds (S.Sleepy K) (fun r => (S.trace r).ReadySafe (S.cDur K r) g 0) :=
  (h.behaviour.da cap g hc hg).sleepySafe

example (h : Good S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) :
    S.Holds (fun _ => True) (fun r => S.AccountablySafe r K.params.α g 0) :=
  (h.behaviour.final g hg).accountable

/- M28: heal points are anchored at `max g 0` (catch-up inside `heal`);
progress windows start at `readyFrom c g = max g 0 + c + 1`. -/
example (r : S.Run) (cap : Capability) (i : K.Idx) (g : Time) :
    S.heal K cap i g r = max g 0 + (K.params.heal cap i : Time) * (S.pt r).env.Δ := rfl

example (r : S.Run) (g : Time) : S.ready K g r = max g 0 + S.cDur K r + 1 := rfl

/- M30: one regime for safety and liveness; liveness's progress window
`[ready, horizon]` gives safety's `[ready, heal]` whenever `heal ≤ horizon`. -/
example (r : S.Run) (cap : Capability) (i : K.Idx) (g : Time)
    (hh : S.heal K cap i g r ≤ (S.pt r).horizon)
    (h : S.prog X K cap i (S.ready K g r) (S.pt r).horizon r) :
    S.prog X K cap i (S.ready K g r) (S.heal K cap i g r) r :=
  X.mono le_rfl hh h

/- M35 (override 4): a run after an outage is partially synchronous with
GST `b₁`; nothing in the definition prevents taking GST = `b₁`. -/
example (r : S.Run) {T b₀ b₁ : Time} (h : S.Outage K T b₀ b₁ r) :
    (S.log r).PSync (S.pt r) b₁ := h.2.1.2

/- M35: the past is safe whatever the future does (prefix form). -/
example := @Good.sleepySafe_prefix
example := @Good.healedSafe_prefix
example := @Good.outage_prefix

/- M14: the finalized half through an outage. -/
example := @Good.persists_final_compatible

end Generic

/-! ### Tests named by the table (checked to exist) -/

-- M3
example := @Pattern.range
example := @range_head
example := @Tests.Goldilocks.pp223_numbers
-- M7, M27, M4
example := @regimes_realizable
example := @Tests.Realizable.healed_witness_late
example := @Tests.Realizable.healed_witness_late_control
-- M8
example := @Tests.Regimes.outage_async_log
example := @Tests.Realizable.outage_witness_late
example := @Tests.Controls.outage_control
-- M9
example := @Tests.Regimes.sleepy_with_sleeper
-- M10
example := @Tests.Vacuity.admissibility_rejections
example := @Tests.Vacuity.standard_admissible
example := @Tests.Regimes.outage_times_teeth
example := @Tests.Regimes.healthy_needs_two_thirds
-- M11
example := @Tests.Regimes.healthy_wake_at_gst
-- M13
example := @Tests.Goldilocks.outageWindow_prefix_only
-- M14
example := @Tests.Goldilocks.stable_is_confirmed
-- M15
example := @goldilocksContract
example := @goldilocks_admissible
example := @reference_bounds
example := @Tests.Goldilocks.pp223_numbers
-- M21
example := @EnvPoint.HealthyOn.faultsBelow
example := @Tests.Regimes.faulty_third_not_healthy
-- M23
example := @budget_implies_V
-- M25
example := @Tests.Good.healthy_rotating_sleeper
-- M29
example := @Tests.Vacuity.allProposers_unfit
example := @Tests.Realizable.allProposers_no_witness
example := @Tests.Blocks.recurrence_has_teeth
-- M35
example := @Tests.Good.prefix_sync_then_async
-- M37
example := @Model.sysOf_adequate
example := @Model.sysOf_log_faithful
example := @Model.Run.held_iff_served
example := @Tests.Network.silent_run_valid
-- M38
example := @Tests.Problem.local_accountability_teeth
-- vacuous system
example := @Tests.Good.false_progress_not_good
example := @Tests.Good.empty_valid_not_good
example := @Tests.Good.excuse_true_not_good
example := @Tests.Good.no_admissible_not_good

/-! ### Sheet references (checked to exist)

`GoldilocksTarget` theorems (§1) and `GoldilocksExtra` fields (§2). -/

-- M1
example := @GoldilocksExtra.weakSafe
example := @GoldilocksExtra.weakInclude
example := @GoldilocksExtra.weakGrow
-- M12
example := @GoldilocksExtra.includeSleepy
example := @GoldilocksExtra.includeHealed
-- M13
example := @GoldilocksExtra.outageWindow
-- M14
example := @GoldilocksTarget.confirmed_persists
example := @GoldilocksTarget.outage_final_compatible
-- M20
example := @GoldilocksExtra.crossNest
example := @GoldilocksExtra.liveDC

end Consensus.Shape.Tests.Gaps

end
