module
public import ConsensusProblem
public import Mathlib.Tactic
@[expose] public section

-- One row per line, by design.
set_option linter.style.longLine false

/-! # Gap dispositions (M1–M39)

One line per row of the merged gap list (`gapreview/gaps-merged.md`) and the
"vacuous system" row (plan: iteration 6, §8). Kinds: **construction** (the
fixed L0 definition says it; `example` below), **test**, **sheet**
(`GoldilocksTarget` theorem or `GoldilocksExtraAt` field), **obligation** (FG-SA
migration obligation in the sheet), **scope** (outside the definition),
**removed** (the gap's object no longer exists). Cited names are checked to
exist in `Index.lean`.

* M1 weak continuation: construction, healed regime healthy to the horizon (`example`); sheet `weakSafe`, `weakInclude`, `weakGrow`; uniformity: obligation (10).
* M2 corruption growth: scope, static adversary (`EnvPoint.honest` fixed per run); sheet §3 (A6).
* M3 FE/F4 pattern: `Pattern.range`; final progress `range (3R+κ)` (`pp223_numbers`, `finRec_span`); `range_head` (span loss); equivalence: gate F-2.
* M4 psync mandated: construction, `Behaviour.healedSafe` and `Behaviour.healthyLive` (every provided output) are `Behaviour` fields (`example`); test `healed_witness_late`.
* M5 final safety under asynchrony: construction, `Behaviour.finalAccountable` has premise `True`; `Good.final_agree` (`example`).
* M6 syncUntil unchecked: removed, no premise language; `SyncUntil` is used only inside the fixed outage regime and the prefix forms.
* M7 late GST: `Realizable.healthy` ∀ Δ, g (`regimes_realizable`); test `healed_witness_late` (Δ = 7, GST 1000).
* M8 trivial outage: `OutageActive` in `Realizable.outage`; tests `outage_async_log`, `outage_witness_late` (≥ 1000·Δ), `outage_control`.
* M9 dynamic participation: construction, sleepy is `ReadyAbove θ`, `θ ≤ ½`; test `sleepy_with_sleeper`; stress witnesses (`Realizable.sleepyStress`, `notReadyAtMost_one_not_realizable`).
* M10 thresholds: `Params.Admissible`; tests `admissibility_rejections`, `standard_admissible`, `outage_times_teeth`, `healthy_needs_two_thirds`.
* M11 wake at GST: `HealthyOn` counts a fixed awake set; progress from `ready`; test `healthy_wake_at_gst`.
* M12 inclusion of every proposal: sheet `includeSleepy`, `includeHealed`.
* M13 window-only P1: sheet `outageWindow`; test `outageWindow_prefix_only`.
* M14 outage stable/finalized: closed; stable = confirmed (`stable_is_confirmed`, sheet `confirmed_persists`); `Good.persists_final_compatible` (sheet `outage_final_compatible`).
* M15 pinned params: `goldilocksContract`, `goldilocks_admissible`, `reference_bounds`; test `pp223_numbers`.
* M16 concrete instance: migration; `GoldilocksTarget` is the reviewed target, unproved.
* M17 eventual liveness: scope; every claim has a latency bound (`TxLive` deadline), so eventual-only liveness cannot be expressed; bounded latency implies it when the horizon passes the deadline.
* M18 adaptive corruption: scope, static adversary.
* M19 weights / committees: scope, equal weights (`Fintype V`, counts).
* M20 cross-node nesting: sheet `crossNest`, `liveDC`.
* M21 recovery fault bound: construction, `HealthyOn.faultsBelow` and `1 − φ ≤ α` (`Good.final_safe_healthy`; `example`); test `faulty_third_not_healthy`.
* M22 instance vs FG-SA: obligations (1)–(12).
* M23 cover / budget: sheet `budget_implies_V`; cover ½ vs `OutageE`: obligation (4).
* M24 reader scope: construction, `ReadySafe` (ready readers) for available/stable, `AccountablySafe` (every honest reader) for final (`example`).
* M25 ready vs awake: healthy = fixed awake set (no churn), readers and progress ready; test `healthy_rotating_sleeper`; obligation (6).
* M26 single Δ: scope (`Δ_F = Δ`).
* M27 Δ = 1 witnesses: `Realizable` quantifies every `Δ`; test `healed_witness_late` (Δ = 7).
* M28 recovery starts: construction, `heal = max g 0 + heal·Δ`, `ready = max g 0 + c + 1` (`example`).
* M29 faulty proposer witnesses: `ProgressFits` (recurrence only on `.sized 1`); tests `allProposers_unfit`, `allProposers_no_witness`, `recurrence_has_teeth`.
* M30 safety vs liveness regime: construction, one `Healthy` regime; safety window `[ready, heal]` ⊆ liveness window (`Progress.mono`; `example`).
* M31 validity: scope; `TxLive` serves every submission.
* M32 capacity: scope.
* M33 chain quality: scope beyond the sheet's growth extras.
* M34 conditional accountability: final accountability is unconditional from time `0` (stronger); accountability for conflicting available reads is out of scope.
* M35 one GST / one outage: partially closed; prefix forms (`Good.sleepySafe_prefix`, `healedSafe_prefix`, `outage_prefix`; test `prefix_sync_then_async`); after an outage, GST `b₁` (`example`); several GSTs/outages: scope.
* M36 leak, HP latency: scope; sheet §3 (K1–K5, FL7/FL8).
* M37 model adequacy: `System.Adequate` with `sysOf_adequate`, `sysOf_log_faithful`, `Run.held_iff_served`; test `silent_run_valid`.
* M38 global escape: removed, local accountability only; test `local_accountability_teeth`.
* M39 HEAD: scope, protocol-internal; sheet §3.
* vacuous system: `Good = Behaviour ∧ Adequate ∧ Realizable`; tests `false_progress_not_good`, `empty_valid_not_good`, `excuse_true_not_good`, `no_admissible_not_good`; progress cannot read submissions (`censoring_progress_rejected`) or demand near-full participation (`notReadyAtMost_one_not_realizable`).
-/

namespace Consensus.Shape.Tests.Gaps
open Consensus

section Generic

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

/- M1: the healed regime requires the fixed healthy set awake to the horizon
("stay in recovery"); a run that leaves it is outside the regime. -/
example (r : S.Run) (g : Time) (h : S.Healthy K g r) :
    (S.pt r).HealthyOn K.params.φ g (S.pt r).horizon := h.2

/- M4: partially synchronous safety and liveness are mandated: they are
fields of the fixed behaviour table (liveness for every provided output). -/
example (h : Good S X K) (cap : Capability) (g : S.schema.Id)
    (hg : S.schema.output cap = some g) (i : K.Idx) (gst : Time) :
    S.Holds (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K cap i gst r) (S.lat K cap i r)) :=
  h.behaviour.healthyLive cap g hg i gst

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
  h.behaviour.sleepySafe cap g hc hg

example (h : Good S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) :
    S.Holds (fun _ => True) (fun r => S.AccountablySafe r K.params.α g 0) :=
  h.behaviour.finalAccountable g hg

/- M28: heal points are anchored at `max g 0` (catch-up inside `heal`);
progress windows start at `ready = max g 0 + c + 1`. -/
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

end Generic

end Consensus.Shape.Tests.Gaps

end
