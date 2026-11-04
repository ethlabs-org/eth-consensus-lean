module
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
public import Mathlib.Tactic
@[expose] public section

-- One row per line, by design.
set_option linter.style.longLine false

/-! # Gap dispositions (M1–M39)

One line per row of the merged gap list (`gapreview/gaps-merged.md`) and the
"vacuous system" row (plan: iteration 6, §8). Kinds: **construction** (the
fixed L0 definition says it; a theorem below), **test**, **sheet** and **obligation** (a row
or a migration obligation of the archived target sheet, `archive/consensus-lean-baseline`, with
its tests; not declarations of this library), **scope** (outside the definition), **removed**
(the gap's object no longer exists).

* M1 weak continuation: construction, healed regime healthy to the horizon (`m1_healthy_awake_to_horizon`); sheet `weakSafe`, `weakInclude`, `weakGrow`; uniformity: obligation (10).
* M2 corruption growth: scope, static adversary (`EnvPoint.honest` fixed per run); sheet §3 (A6).
* M3 FE/F4 pattern: `Pattern.range`; final progress `range (3R+κ)` (sheet `pp223_numbers`, `finRec_span`); sheet `range_head` (span loss); equivalence: gate F-2.
* M4 psync mandated: construction, `Behaviour.healedSafe` and `Behaviour.healthyLive` (every provided output) are `Behaviour` fields (`m4_psync_live_mandated`); test `healed_witness_late`.
* M5 final safety under asynchrony: construction, `Behaviour.finalAccountable` has premise `True`; `CorrectProtocol.final_agree` (`m5_final_agree`).
* M6 syncUntil unchecked: removed, no premise language; `SyncUntil` is used only inside the fixed outage regime and the prefix forms.
* M7 late GST: `Realizable.healthy` ∀ Δ, g (`regimes_realizable`); test `healed_witness_late` (Δ = 7, GST 1000).
* M8 trivial outage: `OutageActive` in `Realizable.outage`; tests `outage_async_log`, `outage_witness_late` (≥ 1000·Δ), `outage_control`.
* M9 dynamic participation: construction, sleepy is `ReadyAbove θ`, `θ ≤ ½`; test `sleepy_with_sleeper`; stress witness with at most two honest awake (`Realizable.sleepyStress`, `notReadyAtMost_one_not_realizable`, `notReadyAtMost_below_not_realizable`).
* M10 thresholds: `Params.Admissible`; tests `admissibility_rejections`, `standard_admissible`, `outage_times_teeth`, `healthy_needs_full_participation`.
* M11 wake at GST: `HealthyOn` counts every honest validator awake from `max g 0` (full participation); progress from `ready`; test `healthy_wake_at_gst`.
* M12 inclusion of every proposal: sheet `includeSleepy`, `includeHealed`.
* M13 window-only P1: sheet `outageWindow` and its test `outageWindow_prefix_only`.
* M14 outage stable/finalized: closed; stable = confirmed (sheet test `stable_is_confirmed`, sheet `confirmed_persists`); `CorrectProtocol.persists_final_compatible` (sheet `outage_final_compatible`).
* M15 pinned params: removed, the pinned sheet is archived; the live contract numbers are `goldilocksContract` at `contract_coefficients`.
* M16 concrete instance: closed by the Accepted endpoint (`meetsObligations`); the unproved target sheet is archived.
* M17 eventual liveness: scope; every claim has a latency bound (`TxLive` deadline), so eventual-only liveness cannot be expressed; bounded latency implies it when the horizon passes the deadline.
* M18 adaptive corruption: scope, static adversary.
* M19 weights / committees: scope, equal weights (`Fintype V`, counts).
* M20 cross-node nesting: dropped by owner (#104); compatibility follows from safety and local nesting; sheet `liveDC` retains its cross-time growth claim.
* M21 recovery fault bound: construction, `HealthyOn.faultsBelow` and `β ≤ α` (`CorrectProtocol.final_safe_healthy`; `m21_healthy_faults_below`, `m21_final_safe_healthy`); test `faulty_third_not_healthy`.
* M22 instance vs the archived development: removed, with the sheet's migration obligations (archived).
* M23 cover / budget: sheet `budget_implies_V`; the outage has no cover (owner, 2026-11-02): the cohort count gives `OutageE1` (`EnvPoint.CohortOn.two_mul_lt`), obligation (4).
* M24 reader scope: construction, `ReadySafe` (ready readers) for available/stable, `AccountablySafe` (every honest reader) for final (`m24_sleepy_ready_safe`, `m24_final_accountable`).
* M25 ready vs awake: healthy = every honest validator awake (full participation), readers and progress ready; test `healthy_rotating_sleeper`; obligation (6).
* M26 two delay bounds: `Env` and `Public` carry `Δ` and `ΔF` (`docs/decisions.md` 2026-11-02, two-bound network); `Realizable` quantifies every `Δ > 1` and `ΔF > 1` (half-open delivery, 2026-11-04), the healthy regime within `ΔF ≤ rowRatio·Δ`.
* M27 small-Δ witnesses: `Realizable` quantifies every `Δ > 1` (from `Δ = 2`); test `healed_witness_late` (Δ = 7).
* M28 recovery starts: construction, `heal = max g 0 + heal·Δ`, `ready = max g 0 + c + 1` (`m28_heal_anchor`, `m28_ready_anchor`).
* M29 faulty proposer witnesses: `ProgressFits` (recurrence only on `.sized 1`); `ProgressTolerant` asks a bad proposer slot in every window (`Recurrence.BadSlotSlack`, witness `RealizableActive.badProposer`); tests `allProposers_unfit`, `allProposers_no_witness`, `recurrence_has_teeth`, `recur_single_one_not_tolerant`, `recur_single_one_bad_slots`.
* M30 safety vs liveness regime: construction, one `Healthy` regime; safety window `[ready, heal]` ⊆ liveness window (`Progress.mono`; `m30_prog_to_heal`).
* M31 validity: scope; `TxLive` serves every submission.
* M32 capacity: scope.
* M33 chain quality: scope beyond the sheet's growth extras.
* M34 conditional accountability: final accountability is unconditional from time `0` (stronger); accountability for conflicting available reads is out of scope.
* M35 one GST / one outage: partially closed; prefix forms (`CorrectProtocol.sleepySafe_prefix`, `healedSafe_prefix`, `outage_prefix`; test `prefix_sync_then_async`); after an outage, GST `b₁` (`m35_outage_psync`); several GSTs/outages: scope.
* M36 leak, HP latency: scope; sheet §3 (K1–K5, FL7/FL8).
* M37 model adequacy: `System.Adequate` with `sysOf_adequate`, `sysOf_log_faithful`, `Run.held_iff_served`; test `silent_run_valid`.
* M38 global escape: removed, local accountability only; test `local_accountability_teeth`.
* M39 HEAD: scope, protocol-internal; sheet §3.
* vacuous system: `CorrectProtocol = Behaviour ∧ Adequate ∧ Realizable`; tests `false_progress_not_correct`, `empty_valid_not_correct`, `excuse_true_not_correct`, `no_admissible_not_correct`; progress cannot read submissions (`censoring_progress_rejected`) or demand near-full participation (`notReadyAtMost_one_not_realizable`).
* dependency-gated network: closed by construction; raw arrivals do not require dependency readiness.
  `Network.RawArrival.poisoned_arrival` admits the timely honest send/receipt with a withheld prerequisite.
  The former audit's `not_psync_of_poisoned` exclusion no longer holds; buffering and admission belong
  to the family, while release guards and message/FG-attestation deadlines are unchanged.
-/

namespace Consensus.Shape.Tests.Gaps
open Consensus

section Generic

variable {V : Type} [Fintype V] [DecidableEq V] {Prog : Type} {S : System V}
  {X : Progress S Prog} {K : Contract Prog}

/- M1: the healed regime requires every honest validator awake to the horizon
("stay in recovery"); a run that leaves it is outside the regime. -/
theorem m1_healthy_awake_to_horizon (r : S.Run) (g : Time) (h : S.Healthy K g r) :
    (S.pt r).HealthyOn K.params.β g (S.pt r).horizon := h.2.1

/- M4: partially synchronous safety and liveness are mandated: they are
fields of the fixed behaviour table (liveness for every provided output). -/
theorem m4_psync_live_mandated (h : CorrectProtocol S X K) (cap : Capability) (g : S.schema.Id)
    (hg : S.schema.output cap = some g) (i : K.Idx) (gst : Time) :
    S.Holds (fun r => S.Healthy K gst r ∧ S.prog X K cap i (S.ready K gst r) (S.pt r).horizon r)
      (fun r => (S.trace r).TxLive (S.cDur K r) g (S.heal K cap i gst r) (S.lat K cap i r)) :=
  h.behaviour.healthyLive cap g hg i gst

/- M5: final agreement below `α` faults, under any network (no regime). -/
theorem m5_final_agree (h : CorrectProtocol S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) (r : S.Run)
    (hv : S.Valid r) (hb : (S.pt r).FaultsBelow K.params.α) :
    (S.trace r).Agree g 0 ∨ S.Excuse r :=
  h.final_agree hg r hv hb

/- M21: the healthy regime bounds the faults below `β ≤ α`, so final
safety holds there. -/
theorem m21_healthy_faults_below (r : S.Run) (g : Time) (h : S.Healthy K g r) :
    (S.pt r).FaultsBelow K.params.β := h.2.1.faultsBelow

theorem m21_final_safe_healthy (h : CorrectProtocol S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) (r : S.Run)
    (hv : S.Valid r) {gst : Time} (hH : S.Healthy K gst r) :
    (S.trace r).Safe g 0 ∨ S.Excuse r :=
  h.final_safe_healthy hg r hv hH

/- M24: available/stable safety is for ready readers (`ReadySafe`), final
accountability for every honest reader, unconditionally. -/
theorem m24_sleepy_ready_safe (h : CorrectProtocol S X K) (cap : Capability) (g : S.schema.Id)
    (hc : cap = .available ∨ cap = .stable) (hg : S.schema.output cap = some g) :
    S.Holds (S.Sleepy K) (fun r => (S.trace r).ReadySafe (S.cDur K r) g 0) :=
  h.behaviour.sleepySafe cap g hc hg

theorem m24_final_accountable (h : CorrectProtocol S X K) {g : S.schema.Id} (hg : S.schema.output .final = some g) :
    S.Holds (fun _ => True) (fun r => S.AccountablySafe r K.params.α g 0) :=
  h.behaviour.finalAccountable g hg

/- M28: heal points are anchored at `max g 0` (catch-up inside `heal`);
progress windows start at `ready = max g 0 + c + 1`. -/
omit [Fintype V] [DecidableEq V] in
theorem m28_heal_anchor (r : S.Run) (cap : Capability) (i : K.Idx) (g : Time) :
    S.heal K cap i g r = max g 0 + (K.params.heal cap i : Time) * (S.pt r).env.Δ := rfl

omit [Fintype V] [DecidableEq V] in
theorem m28_ready_anchor (r : S.Run) (g : Time) : S.ready K g r = max g 0 + S.cDur K r + 1 := rfl

/- M30: one regime for safety and liveness; liveness's progress window
`[ready, horizon]` gives safety's `[ready, heal]` whenever `heal ≤ horizon`. -/
omit [Fintype V] [DecidableEq V] in
theorem m30_prog_to_heal (r : S.Run) (cap : Capability) (i : K.Idx) (g : Time)
    (hh : S.heal K cap i g r ≤ (S.pt r).horizon)
    (h : S.prog X K cap i (S.ready K g r) (S.pt r).horizon r) :
    S.prog X K cap i (S.ready K g r) (S.heal K cap i g r) r :=
  X.mono le_rfl hh h

/- M35 (override 4): a run after an outage is partially synchronous with
GST `b₁`; nothing in the definition prevents taking GST = `b₁`. -/
theorem m35_outage_psync (r : S.Run) {T b₀ b₁ : Time} (h : S.Outage K T b₀ b₁ r) :
    (S.log r).PSync (S.pt r) b₁ := h.2.1.2

end Generic

end Consensus.Shape.Tests.Gaps

end
