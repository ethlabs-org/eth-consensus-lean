# Accepted proof dependencies

This is the integration ledger for the Goldilocks `Accepted` endpoint.
The master status view records the complete compiled endpoint leaf inventory.
`Accepted` is **proved and certified** (full tier PASSED on main b75cd7c586bcdb708d0c94e125307cf32edf051d, 1351 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 12:06): `acceptedEndpoint` is in `Solution`
at the standard axioms [propext, Classical.choice, Quot.sound]. Historical/planned
sections below record how the endpoint was wired; an OPEN in them is past status,
not current evidence.

## Completion gate

1. `lake build` succeeds for the integrated family and the entire Accepted skeleton.
2. Every unfinished proof is a named declaration in `Lemmas/` or `Proofs/`, never
   an axiom or a `sorry` in Spec, Statements, instances, tests, Main or Solution.
3. Every reachable `sorry`, down to transport, simulation, node, healing, sleepy,
   outage and final leaves, has an exact statement in Lean, an owner, dependencies,
   and a paper argument with a pinned location, or an explicit **OPEN** flag.
4. The dependency graph has no circular supplier assumptions and introduces no
   additional premise in generic `Accepted`. Conditional publisher interfaces must
   expose their concrete implementation obligation as a separate OPEN leaf.
5. Snapshot, import boundaries and trusted-surface review pass before landing.
   The incomplete skeleton stays outside Main/Solution's sorry-free closure.

Current status: **proved and certified** (full tier PASSED on main b75cd7c586bcdb708d0c94e125307cf32edf051d, 1351 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 12:06). Every Accepted field
assembles named, proved suppliers, with no `sorry` in the closure of `Refinement.Accepted`
or `Solution`. The healing coefficient is closed: `accepted_heal` is the fixed
`catchUp + healMargin` (4078bc74). The master view below is compiled reachability. The
Healing statements outside that closure (`docs/roadmap.md`) are whole-run statements over
infinite runs, which Accepted's finite model runs never satisfy (`docs/goldilocks-mapping.md`
§"Healing"), so Accepted uses the finite-horizon `…UpTo` forms instead.

## Master status: every Accepted field, grouped by leaf owner

Current compiled audit: source `70e90b44` (main after `final_reset_premises` e621acd7, `healthy_confirmed_supply` db4b864f, `healthy_repair_schedule` f4997e9f and `outage_repair` 70e90b44, #136),
regenerated in an Amp orb with `scripts/accepted-status.py`. The JSON records
the exact source pin separately from its publication commit.
Machine-readable rows and per-field edges are in `docs/accepted-status.json`.
Regenerate with `python3 scripts/accepted-status.py` after building `ConsensusLean`
and `spec-surface`, on every ledger update. Historical former sorry declarations
since fd7f498 remain in the inventory; body closure alone is not `lean-proved`.
Paper status is `unknown` unless an authoritative owner supplies a classification.
The post-wiring audit uses `spec-surface dependencies --from
Consensus.Goldilocks.Refinement.accepted --modules
ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted`, including type
and body edges and cycle-safe transitive traversal. Names below have prefix
`Consensus.Goldilocks.Refinement.`. Each set enumerates **direct sorry owners**;
an assembly depending on them is not an additional leaf.

Compiled closure: no direct owner in the audit at 70e90b44; `accepted` at
[propext, Classical.choice, Quot.sound] (`#print axioms` at 70e90b44). Since dea4a19e (#136, sorry
groups A, B and C deleted) no declaration in the import closure of `Refinement.Accepted` and
`Solution` depends on `sorryAx` (`axiom-audit` at dea4a19e). Since 9089d1d7 (#136, sorry group D:
`Healing.voter_unlock_keeps_lock`, `Healing.reset_inv` and their 14 sorry-dependent users deleted)
ConsensusLean, ConsensusLeanTest and Solution have **0 compiled sorry owners**. That is not 0
outstanding mathematical statements: the Healing statements `HealingRunStatements`,
`PhaseServiceStatements`, `NonInterference` and `FrozenTreeAgreement` lost their only
(sorry-dependent) inhabitants and are stated with their proof open (`docs/roadmap.md`), and further
statements were never proved. `ResetExistence`, `CommonPathAcquisition` and `AvailableHealing`, which
lost theirs at the same time, are proved again: their consumers read only HS.3 (b), which follows from
HS.2 (`frozen_tree_agreement_clean`), so neither HS.3 (a) nor `reset_inv` is needed. The exact-head full tier on
70e90b443ce1d0871b8efd21e131ee54367559e9 (`check.sh --full`) passed, exit 0, 801 s, recorded on
[#63](https://github.com/ethlabs-org/consensus-lean/issues/63) (row 11-02 18:03, milestone
closure): kernel replay, `lake comparator --paranoid` with its fixtures and the Solution/test
audit passed. Step 10 logged 15 lexical sorry/admit matches (14 sorry holes plus an admit-named
structure field) and skipped the default-target lake check; the good/bad fixtures passed. This is
distinct from the Accepted Challenge certification, which has its own full tier: `check.sh --full` on
main 2a9b34a11bb9f754a5526593fab6d72366c325a7 passed, 1371 s, zero SKIP lines, recorded on
[#63](https://github.com/ethlabs-org/consensus-lean/issues/63) (row 11-03 02:28): kernel replay of every
leaf, the default-target lake check, the axiom audit, `lake comparator --paranoid` and the rebuild canary,
with their controls; 0 sorry/admit. After a90299c1 strengthened `Realizable.sleepyStress` (trusted
semantics) and the trusted-layer review documentation batch landed, the full tier was rerun: `check.sh --full`
on main ebb2f2ec2783911997e7f4945684f54382690ea6 passed, exit 0, 1381 s, zero SKIP lines, recorded on
[#63](https://github.com/ethlabs-org/consensus-lean/issues/63) (row 11-03 04:45): cold build 243 s, every-leaf
kernel replay 235 s with controls, the default-target lake check 561 s with the standard three axioms and the
good/bad fixtures, `lake comparator --paranoid` 174 s over 25,065 declarations with controls, the rebuild canary
16 s with both controls; 0 lexical sorry/admit. After the trusted changes that followed (the retired
`SleepySafePrefix` row 13841d74, the flat catch-up 4df95240, half-open L0 delivery 5eafeb1d, 333300b4 and
09ddfad9, and the Goldilocks head-drop b15ffd4a), the full tier was rerun: `check.sh --full` on main
c361faa46d43bdbdbd6cca76f301e374bb8236ef passed, 1381 s, zero SKIP lines, recorded on
[#63](https://github.com/ethlabs-org/consensus-lean/issues/63) (row 11-03 09:04, combined phase 2 and head-drop
certification): every-leaf kernel replay with its controls 227 s, the default-target lake check with the
good/bad fixtures 578 s with only the standard three axioms, `lake comparator --paranoid` 175 s over 25,043
declarations, the rebuild canary 15 s with the proof hash unchanged; 0 lexical sorry/admit.
`AcceptedEndpoint` was certified as of c361faa4. After the trusted landings that followed (the bound rename
da7938f4, the citations 73e26bcc, the Baseline archive 656fe151, Part R 5d35a662, sweep item 6 ee7382ae, sweep
item 3 08204077 and the outage budget 4k − 5 b75cd7c5), the full tier was rerun: `check.sh --full` on main
b75cd7c586bcdb708d0c94e125307cf32edf051d (tree 1d3f211b) passed, 1351 s, zero SKIP lines, recorded on
[#63](https://github.com/ethlabs-org/consensus-lean/issues/63) (row 11-03 12:06, trusted sweep certification):
cold build 231 s, every-leaf kernel replay with its controls 228 s, the default-target lake check with its
controls 554 s with only the standard three axioms, `lake comparator --paranoid` with its controls 173 s over
25,042 declarations, the rebuild canary 16 s with the proof hash unchanged; 0 lexical sorry/admit.
`AcceptedEndpoint` is certified as of b75cd7c5; commits after it are not covered.
The four Healing statements above remain stated with their proof open.

| Set | Owner | Direct leaf list |
|---|---|---|
| C | Spec orb, joint coefficient synthesis | none since 4078bc74 (`accepted_heal` is the closed `catchUp + healMargin`; half-open phase 2: `healMargin = 24·L_drain + 8k + 52δt + 52X + 44`, was `catchUp + 2·healMargin + 3`) |
| F | Four-anchor/final service owner (H1 Sol, H3 coefficients) | none since e621acd7 (`final_reset_premises` is closed by `final_reset_premises_of_query`) |
| H | Healing paper/T3; Spec orb integration | none since f4997e9f (`healthy_preparation_initialize` proved at 2d943744, `healthy_repair_schedule` at f4997e9f) |
| N | Healing paper/T3; Spec orb integration | none since db4b864f (`healthy_confirmed_supply` proved from the preparation initializer) |
| O | Healing/outage owner; Spec orb integration | none since 70e90b44 (`outage_repair` proved) |

| Accepted field / branch | Reachable OPEN leaves by owner set | Direct adapter sorry? |
|---|---|---|
| outputValid | none | no |
| nested | none | no |
| finalMonotone | none | no |
| finalAccountable | none | no |
| healthyLive, final | none | no |
| healthyLive, available/stable | none | no |
| sleepySafe, available/stable | none | no |
| sleepyLive, available/stable | none | no |
| healedSafe, available/stable | none | no |
| persists | none | no |
| progressFits, progressTolerant, admissible | none | no |
| serves | none (schema provides final output) | no |
| claims and the whole of accepted | none | no |

The rerun (fresh audit of the combined #142 + #143 integration, #136) finds **6 direct sorry owners** in Accepted's closure, matching `scripts/sorry-inventory.py` on the same source. Since 4078bc74 (`accepted_heal` closed, S6) there are **5**; since `healthy_preparation_initialize` is proved (2d943744) there were **4**; since `final_reset_premises` (e621acd7), `healthy_confirmed_supply` (db4b864f) and `healthy_repair_schedule` (f4997e9f) are proved there was **1**, `outage_repair`; since 70e90b44 (`outage_repair` proved) there is **none** (`docs/accepted-status.json`, audit at 70e90b44). At #141 there were 10. `final_window_extract` now has a closed body (`final_window_extract_of'` from the leaves `final_reset_premises` and `final_duty_proposal`); `final_duty_proposal` has a proved body (`final_duty_proposal_run`, FinalDutyProposal.lean), bounded by `0 < s` and `ts s ≤ horizon`, so the final set had 1 leaf, and since e621acd7 it has none. `healthy_current_live_candidates`, `healthy_current_record_viable`, `healthy_prepare` and `healthy_current_mature_or_anchor` are no longer direct owners (bodies closed on main after #141; they are sorry-dependent). At #141 the reduction from 13 was retirement/consolidation (`final_inherited_progress`, `final_row_signers`) and a closed body (`healthy_bounded_repairing_opening`), not proof closure of the retired leaves. `simTrace_vote_forwarded`
is fully sorry-free; `sleepy_query_sync` and `sleepy_safety_inputs` have proved bodies,
not direct sorries. Since 4078bc74 their full closures are sorry-free
(`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`): `accepted_heal` is a closed
definition, so `K S A = acceptanceContract A (accepted_coefficients S A)` carries no sorry. Kev's independent read-back and axiom
split are recorded on [#132](https://github.com/ethlabs-org/consensus-lean/issues/132).
`healthy_preserve` has a proved body
(since R0 it preserves only records and recent locks), while its coefficient type dependencies remain. `outage_arm` is proved at 649f0286;
103bfbd moves the two cut adapters' holes into actual-tip comparability/ancestry,
without reducing their count. At the pre-wiring baseline the two nonfinal
healthyLive branches and sleepySafe/sleepyLive were direct adapter holes; all
four now have assembly bodies. Capability budgets remain distinct even though
available and stable both project to confirmed output. Collision escapes,
empty-validator handling, exact cDur, deadline scaling and endpoint premises
are unchanged. No Main/Solution certification is claimed.

`healthy_old_row_realize` and `healthy_vote_row_replacement` (OPEN, unreachable from
accepted) were deleted at fa194fa6 (#136, sorry group A); the first-arrival/self-entry join and
the label-bounded replacement they stated stay open on paper. `sleepy_safe_finite` (Healing box finite R.1) is
**proved and unreached**, via `Regimes.sleepy_safe_before` at c3f8f4d.
Their absence from the closure means the current joint leaves do not yet call
them; reachability alone says nothing about proof status. Likewise imported implementation
modules are not automatically proof dependencies. The older draft inventories
below describe planned internal decompositions, not extra leaves in this closure.

The approved safety-duration change landed at 5d33450: `sleepy_safe_engine`
is proved at node catchUp + 1, and `sleepy_safety_inputs` now requires
`Regimes.catchUp nodeParams + 1 ≤ engine cDur`. The Accepted endpoint is unchanged.
The joint `accepted_catchUp` synthesis remains OPEN; no fixed coefficient is chosen. Since
engine Δe ≥ 1, increasing an engine-scale coefficient C by one adds Δe:
`(C + 1) * Δe = C * Δe + Δe ≥ C * Δe + 1`. Do not identify literal +1
with Δe or Δp. The bridge proof uses unit clock lag, an initial or last complete
local-event ReadPoint, effective-record equality and ordered-record monotonicity.
It does not prove the remaining safety-input supplier or unconditional Accepted safety.

### Proved internal suppliers from today's landings

The following proofs advance the internal routes without closing the joint
Accepted leaves. The grouped owner sets above remain unchanged: a proof outside
the current dependency closure does not remove a reachable sorry merely because
it is intended to implement that supplier. Original public wrappers remain available.
Names use the namespace stated in each row (under `Consensus.Goldilocks`).

| Owner / namespace | Proved declarations and landing | Exact scope / remaining join |
|---|---|---|
| Healing source-service / `Healing` | `proposal_stored_locks_compatible_old`, `optimistic_prefix_compatible_old` (2d53602); `proposal_start_supported` (c37143b, standard axioms) | Actual stored provenance and proposal timing; proposal start support now follows clean source votes. `vote_old_live_lock_below_parent` remains OPEN: head/stamp held-at-proposal and proposal-domain joins (healing §81). |
| Healing source-service / `Healing` | `historical_activation_cutZ_before` (e73ed60), `reset_sync_window_before`, `historical_activation_before` (79be99e) | Bounded comparison/vote activation through Q from ResetPremises; cutZ-windowed service is derived from node reset premises. Engine Healthy→reset/service transport remains separate; no new Catch premise. |
| Healing transfer / `SA` | `result_prefix_vote_extends_of_stored`, `next_vote_extends_before` (daf14e2) | Current-cut stored compatibility, carry, viability and merged-view inputs remain explicit. Later transfer uses only earlier predecessor/current-label votes; these primitives do not produce their service/viability inputs. |
| Healing retention / `Healing` | `high_floor_source_before` (f65e35a) | Source-state height extracts an earlier high origin; earlier-origin pairwise and target compatibility remain hypotheses. No read of an unheld receiver root supplies the height. |
| Healing retention / `Healing` | `high_origin_held_at_vote`, `high_origin_height_at_vote` (47c97a0) | Counted-head relay gives receiver heldness and height agreement from HighOrigin, an honest later-label cast and current F ancestry; no floor-viability induction hypothesis. |
| Healing retention / `Healing` | `first_carry_of_finalized_anc`, `later_carry_of_finalized_anc` (0e96018) | Explicit current global F ancestry and HighOrigin retained; first carry also consumes stored fast-lock provenance, later carry earlier predecessor-batch VoteExtends. Existing first_carry/later_carry are wrappers. |
| Healing box / `Compose` | `honest_votes_eq_proposal_at_update_before`, `updater_F_anc_proposal_before`, `proposal_held_at_update_before`, `proposal_majority_at_update_before`, `adopt_result_before`, `update_adopts_before` (7271f79) | Held→Adopt chain is finite through update time≤b, using SyncBefore, bounded slot-point fault bounds and SleepyInvariantUpTo. No whole-run agreement premise; finite end-to-end inclusion subsequently closed at 5b33645. |
| Healing box / `Refinement` | `sleepy_safe_engine` (5d33450), `sleepy_safe_finite` (c3f8f4d) | Both proved. Engine safety uses node catchUp+1; Accepted still owes safety-input production and joint coefficients. Finite node safety remains outside the Accepted closure. |

| Declaration | Paper argument/status |
|---|---|
| `Consensus.Goldilocks.Refinement.accepted_catchUp_ge_sleepy` | Proved by the value (`accepted_catchUp = 19`). Covers 18Δ+1≤19Δ for Δ≥1 (node Δ = engine Δ since half-open delivery). Reached by Sleepy safety and liveness. |
| `Consensus.Goldilocks.Refinement.accepted_latency_ge_sleepy` | OPEN, Spec orb joint synthesis: available/stable latency≥4idx+6, covering (4idx+6)Δ (half-open phase 2; was ≥8idx+12 covering (4idx+6)(Δe+1)). Other regimes may raise it; not a final joint value or new endpoint premise. Reached by Sleepy liveness slot selection. |
| `Consensus.Goldilocks.Refinement.healthy_confirmed_supply` | Proved (db4b864f): `healthy_confirmed_supply_of_initializer` (HealthyConfirmedEndpoint, cb3e1846) applied to `healthy_preparation_initialize`; statement unchanged. Only the selected accepted proposal is covered; no new endpoint assumption. |
| `Consensus.Goldilocks.Refinement.sleepy_safety_inputs` | Body proved via finite SVC at the horizon, duration arithmetic and fault bounds. No direct sorry; full closure sorry-free since 4078bc74 (accepted_heal closed), not a #128 statement obstruction. |
| `Consensus.Goldilocks.Refinement.confirmed_duration_supply` | Body closed at 7547caee using accepted_catchUp_ge_sleepy and exact scale arithmetic; proved, no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.sleepy_query_sync` | Body proved via finite SVC at Q.deadline with Q.bounded. No direct sorry; full closure sorry-free since 4078bc74 (accepted_heal closed). |
| `Consensus.Goldilocks.Refinement.simTrace_vote_forwarded` | Proved with a sorry-free closure (standard axioms only); same-event signed envelope release and first-release freshness. |
| `Consensus.Goldilocks.Refinement.sleepy_query_population` | Body closed via duration monotonicity and sleepy_faultBound; proved, no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.sleepy_query_slot` | Body closed at 7547caee: actual recurrence/grid selection at exact cDur with strict freshness and 6Δp margin; proved, no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.confirmed_slot_event` | Body closed via scheduled actual event and joined readiness transport, not eligibility-as-event by definition; proved, no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.healthy_preparation_initialize` | Proved (HealthyResetEnvelope.lean; moved unchanged from HealthySuppliers to sit downstream of the reset envelope): the joint (E) tuple from `healthy_reset_envelope` (ΔF = rowDelay, a ≤ ready + R·Δ), the seed of `ResetPremisesUpTo.reset_seed`, base slot slot(ready)+1 and the query the maximum of the lower bound; every timing bound, including the reserve and the W record/cache/expiry/service terms, is one step from `accepted_heal_ge_reset` (ready + (R+8k+4X+26)Δ + 2 ≤ heal). Closure: standard axioms only. |
| `Consensus.Goldilocks.Refinement.healthy_prepare` | Body proved: finite ready→heal record and recent stored-lock preparation from W and the preparation schedule; since R0 it consumes no inventory. Sorry-dependent, not a direct owner. |
| `Consensus.Goldilocks.Refinement.healthy_repair_schedule` | Proved (f4997e9f) through the reserved route: `healthy_preparation_initialize` at the same `Q`, `h0`, `hb`, `hp`, then `healthy_repair_schedule_of_preparation` (580f1e4); the reserve is the schedule's own, paid by `accepted_heal_ge_reset`. Statement and section parameters unchanged. |
| `Consensus.Goldilocks.Refinement.healthy_preserve` | Body proved from the given base: records by induction and recent locks by `lock_origin` (R0 removed the cache and inventory steps). Only shared coefficient type dependencies remain; no direct sorry. |
| `Consensus.Goldilocks.Refinement.healthy_cut_agreement` | Body closed at 103bfbd using actual-tip comparability and confirmed_prefix_of_anc; `healthy_cut_tips_comparable` is proved; no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.healthy_cut_monotone` | Body closed at 103bfbd using directed tip ancestry and confirmed_prefix_of_anc; `healthy_cut_tips_ancestor` is proved; no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.healthy_cut_tips_comparable` | Proved: comparability of actual stored-clock read tips at arbitrary InCuts, including pre-endCut heal-time cuts; no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.healthy_cut_tips_ancestor` | Proved: directed ancestry of actual stored-clock read tips, with original ordered-cut/readiness domain; no direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.outage_pre_service` | Engine/outage: migrated to SleepyServiceBefore at 4d69fdd3; the old #127 duplicate-fresh signature obstruction is historical. Proved, no direct owner in the compiled audit at 70e90b44. #128 applicability to the exact Outage premises is not established. |
| `Consensus.Goldilocks.Refinement.outage_arm` | PROVED at 649f0286, unchanged signature: exact endCut(T), lookup success or F fallback, and actual engine read prefix via DCA ancestry. No recency assumption; unused service argument retained. Arming does not prove protection/repair. |
| `Consensus.Goldilocks.Refinement.outage_repair` | Proved (70e90b44; moved to OutageRepair.lean at 273f499a); no direct owner in the compiled audit at 70e90b44. |

## Historical per-field axiom audit at 259d0330 (superseded above)

Audited main at `259d0330ace0464632c03344568c6fe518f33b98` with `#print axioms`
for every `accepted*` declaration and the nonframing/receipt/Sleepy bridges.
`lake exe spec-surface dependencies --from ... --modules ...` supplied the compiled
dependency graph; traversing it identifies the following exact direct `sorryAx` owners.
Names in this section have prefix `Consensus.Goldilocks.Refinement.`.
`C` abbreviates the set `{accepted_catchUp, accepted_heal, accepted_latency}`. Since 4078bc74 none of
them reaches `sorryAx`; the table below is since 4078bc74 (audit at 70e90b44)
(`docs/accepted-status.json`, `fields`). `accepted_coefficients_catchUp` and
`accepted_coefficients_heal` are proved by `rfl`; neither is an owner.
The rows that reach the final branch name their current owners from the fresh audit
(`docs/accepted-status.json`, route A, #136). Since e621acd7 the final branch has no direct sorry
owner: `final_reset_premises`, `final_window_extract` and `final_duty_proposal` have closed bodies. `final_inherited_progress` and `final_row_signers` are retired
(route A), not proved; their earlier rows are kept under `retired` in the status ledger.
`final_cache_acceptance` has a closed body and, since 4078bc74, a sorry-free closure. It is not a
direct OPEN leaf.
These are named sets of leaves, not extra assumptions.

| Audited root | Reachable direct sorry owners |
|---|---|
| accepted_catchUp | none |
| accepted_heal | none |
| accepted_latency | none |
| accepted_coefficients, accepted_coefficients_catchUp | none |
| accepted_outputValid | none |
| accepted_nested | none |
| accepted_finalMonotone | none |
| accepted_finalAccountable | none |
| accepted_healthyLive_final | none |
| accepted_healthyLive | none |
| accepted_sleepySafe | none |
| accepted_sleepyLive | none |
| accepted_healedSafe | none |
| accepted_persists | none |
| accepted_progressFits, accepted_progressTolerant, accepted_admissible | none |
| accepted_claims, accepted | none (audit at 70e90b44) |
| engine_signings_nonFraming, engine_att_protected | none |
| simTrace_forwardOrigin, simTrace_forwardHeldProcessed | none |
| sleepy_ready, sleepy_faultBound, sleepy_read_cut, sleepy_proposal, sleepy_inBy | none |
| sleepy_safe_finite | none (`#print axioms` at 70e90b44) |
| sleepy_include_finite | none (`#print axioms` at 70e90b44) |
| sleepy_grow_finite | none (`#print axioms` at 70e90b44) |
| sleepy_safe_engine | none (`#print axioms` at 70e90b44) |

Nonframing is not a separate `Accepted` field: the audited signing/protection
theorems provide it. Roots marked `none` use only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. A direct sorry in an adapter does not
reference its intended future suppliers, so this graph is not the remaining-work
plan. At 70e90b44 the Accepted Sleepy fields have no direct sorry owner. All Run
unforgeability suppliers are proved, as recorded below.

## Mechanical report contract

The concrete existential assembly now builds. It is a skeleton, not a proof:
numeric witnesses and adapters remain OPEN, and transitive suppliers are reported
from its compiled closure. Fixed assumptions precede finite guarantee witnesses.

```toml sorry-inventory
modules = [
  "ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Evidence",
  "ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Transport",
  "ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Provenance",
  "ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps",
  "ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Sleepy",
  "ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted",
]
roots = ["Consensus.Goldilocks.Refinement.accepted"]
```

Only tables headed `Declaration` and `Paper argument/status` below
claim existing compiled declarations. The report validates every such row even
when outside the assembly closure. Planned publication/network, healing-plan and
external FinitePlan draft tables are **noncompiled scope**, explicitly excluded
from row validation and sorry coverage. Their OPEN text is not compiled evidence.
Argument text is preserved from the owners; mechanical mapping does not validate
the paper argument or certify any proof. Source files use repository-relative
paths; names in compiled rows are fully qualified.

## Concrete acceptance assembly

The root fixes standard fractions, the row ratio `r` of the assumptions with gap `c = cF r`,
`finalWindow A = [0, c, 2c, 3c]` (route A, #136; `[0,2,4,6]` at `r = 1`), `3c ≤ δt` (so δt≥6)
and outage look-back η = 0 (plain sleepy; 2026-11-02, was a positive assumption). Engine-unit
outage lag is 4k+6 (slow arming only: the label before the outage label is armed by b₀;
half-open phase 2, was 8k+12 at Δp=Δe+1 and 8k−8 before 2026-11-02) and budget is 4k−5
(2026-11-03, Francesco; was 4k−6, and min(η,4k−6) before 2026-11-02), the gap bound of the
lock window (`exists_unpolluted_label`).
The outage no-sleep margin is 4k+6 and the recovery delay 9 (Δ units; half-open phase 2, were
max(38, 8k+16) and 18 at Δp=Δe+1).
Only catch-up (positive Nat), heal and latency (Nat-valued functions at each gap)
are existential. They are independent of validator set, execution and horizon.
Every positive outer gap X is an index; tolerance uses X=span+2. Timeout has no X.
The three numeric leaves must be solved jointly with the named endpoint suppliers;
their arbitrary separate instantiation would not prove the endpoint. Local-pattern
sufficiency remains OPEN, not supplied by the timeout inequality alone.
The model maps the FG row delay to the actual engine bound, `rowDelay = ΔF` (half-open:
Δ_F,p = Δ_F,e; no order between ΔF and Δ is assumed). The healthy regime's ratio `ΔF ≤ r·Δ`
gives `6Δ + ΔF ≤ 4Δ·cF r` (`cF_spec`), so the row gap is `c = cF r` (2 at r = 1). Route A (#136): window coverage is the
proved anchor route (`final_anchor_coverage` over `cacheCoverage_of_anchor_window_upTo`);
its inputs `AnchorRun` (reset premises, catch-up, honest anchor proposals, drain, horizon)
and `AnchorSteps` (three gap-`c` anchor steps) come from `final_window_extract`. Its body is
`final_window_extract_of'` (CarrierProcessed.lean; (H4) carrier processing proved) from the
leaves `final_reset_premises` ((H1) reset premises = M1′, and (H3) placement with
`u_min = finalSeedMin Q a = slot a + 2k + 5` = the heal coefficient, corrected by #145; one leaf
because (H3) uses the reset `a` of (H1); proved by `final_reset_premises_of_query`,
FinalResetPremises.lean) and `final_duty_proposal` ((H2) duty → proposal adapter,
guarded by `0 < s` and `ts s ≤ horizon`; proved by `final_duty_proposal_run`, FinalDutyProposal.lean).
`FinalQuery` and `FinalWindowData` are in FinalWindowDefs.lean, so that the window assembly comes
before Accepted.lean.
For the `AnchorSteps` rows, the reusable finite signer results are landed in
`Healing/Outcome/Service.lean` (`ResetPremisesUpTo.row_of_report`, `row_signers_of_reports`);
the paper handoff is workbench b386900 `notes/cards/final_row_signers.md`.
The paper route (workbench `route_a_gap2.md`, read-back passed on #136) is conditional on
the duty-to-proposal adapter, the M1′ bound, an `accepted_heal` that satisfies (H*), and
the mechanical links. Final latency is 4(X+3c)+1, c = cF r (4(X+6)+1 at r = 1; half-open
phase 2, was 8(X+3c)+2); nonfinal latency is 4X+6 (was 8X+12); neither depends on δt.
Superseded argument: [general fixed timeout](https://github.com/fradamt-agent/workbench/blob/fd8cb311fac057347fb49e32cf17841e27a75e76/repos/goldilocks/notes/healing-simple/four-anchor-window.md#general-fixed-timeout-d4).

| Declaration | Paper argument/status |
|---|---|
| `Consensus.Goldilocks.Refinement.accepted_catchUp` | Fixed at `19` (half-open phase 2; was `37` at Δp=Δe+1 from 2026-11-03, Francesco's request, and `max 37 (8k + 4)` before): no proof needs more than the Sleepy margin `18Δ + 1 ≤ 19Δ`. |
| `Consensus.Goldilocks.Refinement.accepted_heal` | Closed (4078bc74): `accepted_catchUp + healMargin S X` at every capability (half-open phase 2, `healMargin = 24·L_drain + 8k + 52δt + 52X + 44`, the final route's margin `M_f`; was `accepted_catchUp + 2·healMargin S X + 3`), a named parameter-only value (`ResetCoefficients`), chosen to fit the proved reset envelope (owner: adjust the constants to what can be proved). `accepted_heal_ge_reset` is the coefficient inequality (★) of the nonfinal envelope and S0; `accepted_heal_ge_final` the final route's heal-bound margin at λ = 2Δ. A later leaf that needs more raises `healMargin`; consumers use only these ≥-forms. |
| `Consensus.Goldilocks.Refinement.accepted_latency` | OPEN: finite latency at every gap; final local-pattern service and cache acceptance unresolved. Spec orb. |
| `Consensus.Goldilocks.Refinement.accepted_outputValid` | Proved through shape_outputValid; compiled closure has no sorryAx. |
| `Consensus.Goldilocks.Refinement.accepted_nested` | Reduction to shape_nested; exact generic field, no collision escape. |
| `Consensus.Goldilocks.Refinement.accepted_finalMonotone` | Reduction to shape_finalMonotone; exact generic field. |
| `Consensus.Goldilocks.Refinement.accepted_finalAccountable` | Body closed through shape_finalAccountable at fixed 1/3; no leaves are reachable (no direct owner in the compiled audit at 70e90b44). Encoding/transport is proved. |
| `Consensus.Goldilocks.Refinement.accepted_healthyLive` | Assembly: available/stable use healthy_confirmed_supply and proved payload projection; final uses accepted_healthyLive_final (sorry-free since e621acd7). `healthy_confirmed_supply` is proved since db4b864f; the compiled closure has no direct sorry owner. |
| `Consensus.Goldilocks.Refinement.final_reset_premises` | Body closed (route A, #136): `final_reset_premises_of_query` (FinalResetPremises.lean), the reset kernel `exists_reset_of_drain_awake` with `drainOutputs_of_service` and `accepted_heal_ge_final`. (H1) `ResetPremisesUpTo` through the horizon at `Q.gst` with the run proposer and digest, for a reset `a` and bound `ΔR` (Sol's M1′), and (H3) the placement `(P)` with `u_min = finalSeedMin Q a = slot a + 2k + 5` (the heal coefficient; #145 removed a time summand that made (H3) false at large GST). One leaf: (H3) depends on the `a` of (H1). No producer is assumed. |
| `Consensus.Goldilocks.Refinement.final_duty_proposal` | Body closed (route A, #136): (H2) duty → proposal adapter (Kev): for `0 < s` with `ts s ≤ horizon`, `HonestReadyIn` at slot `s` gives `HonestProposalRun` at `s`; proved by `final_duty_proposal_run` (FinalDutyProposal.lean). Reaches sorryAx only through the `FinalQuery` type (accepted coefficients). |
| `Consensus.Goldilocks.Refinement.final_window_extract` | Body closed (route A, #136): `final_window_extract_of'` from `final_reset_premises` and `final_duty_proposal`; (H4) carrier processing is proved (`carrier_processed_of_honest`). Gives four honest anchors at start+[0,c,2c,3c] (c = cF r), the slack `ts(A3) + Δ ≤ deadline`, `AnchorRun` and `AnchorSteps` (reusable signer results: `row_of_report`, `row_signers_of_reports` in Healing/Outcome/Service.lean; paper handoff workbench b386900 `notes/cards/final_row_signers.md`). |
| `Consensus.Goldilocks.Refinement.final_anchor_coverage` | Body closed: `AnchorRun` and `AnchorSteps` give A3 chain-finalized coverage of A0 through `cacheCoverage_of_anchor_window_upTo`; uses `6 ≤ δt` for `P₃.slot ≤ P₀.slot + δt`. |
| `Consensus.Goldilocks.Refinement.final_cache_acceptance` | Body closed; no direct owner in the compiled audit at 70e90b44 (the type dependency on the coefficients is sorry-free since 4078bc74). Consumes only A3 chain-finalized coverage of A0, supplied by `final_anchor_coverage` (route A): actual cache ancestry at the exact engine-scaled query endpoint and later horizon-bounded ready CutAfter reads. Not arbitrary-delay acceptance or receipt alone. |
| `Consensus.Goldilocks.Refinement.final_payload_projection` | Body closed conditional on window extraction with CacheCoverage of the extracted window (one premise; route A, #136): raw own-block release via simTrace_block_released and final-output chain membership at engine endCut. Preserves existing cDur, reader condition, latency scaling and collision escape; no forwarding-envelope origin assumption. |
| `Consensus.Goldilocks.Refinement.accepted_healthyLive_final` | Assembly (route A, #136): extraction (`final_window_extract`, body closed from the proved `final_reset_premises` and `final_duty_proposal`), anchor coverage (`final_anchor_coverage`, body closed), cache acceptance and payload projection. Since e621acd7 its closure is sorry-free (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound`). The first-crossing / bounded-crossing assembly and its leaves `final_inherited_progress`, `final_row_signers` are retired (git history before #136 route A). No new public Healthy premises; the accepted coefficients are closed since 4078bc74. |
| `Consensus.Goldilocks.Refinement.accepted_sleepySafe` | Assembly over partly OPEN sleepy_safety_inputs and proved sleepy_safe_engine, with directional readiness and empty-V handling. |
| `Consensus.Goldilocks.Refinement.accepted_sleepyLive` | Assembly over selected serviced Sleepy proposal, finite inclusion and proved payload projection; suppliers OPEN. |
| `Consensus.Goldilocks.Refinement.accepted_healedSafe` | Assembly over finite preparation, progress-free preservation and arbitrary-cut adapters; since f4997e9f (`healthy_repair_schedule`) the compiled closure has no direct sorry owner. |
| `Consensus.Goldilocks.Refinement.accepted_persists` | Assembly over pre-service, effective-record arming and actual repair; no late-wake SyncRun inference. No direct owner in the compiled audit at 70e90b44. |
| `Consensus.Goldilocks.Refinement.proposal_releasable` | Proved (f614a12): scheduled proposal dependencies are in the actual engine closure; Steps wrapper of scheduled_proposal_releasable. |
| `Consensus.Goldilocks.Refinement.simTrace_att_unforgeable` | Proved (c52d387): actual canonical attestation origin/authentication history. |
| `Consensus.Goldilocks.Refinement.simTrace_block_unforgeable` | Proved (f9963e2): valid canonical calls carrying an honest proposer's block have an earlier own-block cut. |
| `Consensus.Goldilocks.Refinement.simTrace_carried_vote_unforgeable` | Proved (62d11ce): carried vote source and recursive object history. |
| `Consensus.Goldilocks.Refinement.simTrace_msg_unforgeable` | Proved (62d11ce): actual message signing/admission provenance. |
| `Consensus.Goldilocks.Refinement.simTrace_vote_released` | Proved (54a9a89): valid execution plus canonical GoldilocksRun gives release of emitted votes at their emission time. |

## Ownership and architecture

The four-anchor skeleton above follows route A (#136; workbench `route_a_gap2.md`,
`window_start_h0.md`, `anchor_row_supplier.md`, `anchor_tick_ac_producer.md`). Its
statements are under review, not proved. The cache endpoint is the original query plus the SAME joint
`accepted_latency` coefficient times engine Δe; no separate output-delay witness,
catch-up substitution or guessed 2Δ bound is introduced. `FinalWindowData` contains
operational witnesses, not any of the five desired supplier conclusions.
Canonical store coherence and actual parent membership must be derived from successful
acceptance and no observed collision; the total σ map's default values supply no such facts.
The row supplier must derive normalization and coherent prior-report history from the
finite canonical execution and Healthy. Its target-quorum branch explicitly identifies
the parent's current height and entry root; stale-finality validity alone is insufficient.

The spec orb owns this table and integrates rows sent by other owners. Owners edit
their assigned Lean modules, not this table concurrently.

| Area | Owner | Placement/status |
|---|---|---|
| Family, finite adapters, integration | Spec orb | family-repair worktree; OPEN |
| Finite sleepy transport | Healing box | Lemmas/Refinement/Sleepy; three direct OPEN consumers, two supplier definitions |
| Healing/R.3/R.4/R.5 | Healing paper orb and T3 | exact supplier declarations pending finite adapters |
| Always fields | Healing box | Lemmas/Refinement/Evidence and Transport |
| Simulation/provenance, scheduled proposal | R.6 box | Provenance, Steps and all Run suppliers proved; no remaining Run unforgeability leaves |
| Network/publication | Engine thread | new Lemmas/Refinement/Forwarding and NetworkTransport |

Replay order uses only validator count and genesis root. The local family repair
indexes it by those values so run-selected proposer parameters preserve the actual
restart order. Credentials supplies ideal selection validity; receivers check role
syntax, not a preconfigured proposer schedule. Selection gates duty execution before
mutation. The protocol timing target is Δp = Δe (half-open delivery; was Δp = Δe + 1), with delivery-time relay.

The runtime publisher is installed by #124: successful block-acceptance cuts,
including own proposals, populate a durable node-root-to-own-wrapper map and queue
fresh signed wrappers in acceptance order. `pollBatch` emits the ordinary body
followed by the queued wrappers, preserving parent-first order. The unsigned relay
remains for compatibility; it is not the acceptance publisher. Successful releases
still require actual event/candidate-prefix indices and release guards, not a
fabricated timestamp order. Shape parsing is not acceptance provenance. The
runtime implementation and the `forwardObj`/`decodeForward` format do not by
themselves prove acceptance provenance or total successful release: both proof
obligations remain OPEN. Validated declaration rows will record the separate
publication proof work.

`NoCollTransport` targets the canonical `simTrace` since #123, whose construction
lives at the protected statement boundary. The proof in 38cfe5f covers every
canonical occurrence, including refused calls, using observed header injectivity
and tagged genesis separation. It needs valid execution and no observed collision,
not a caller-supplied GenesisFresh or arbitrary simulation witness.

## Always-field leaves

All names below have prefix `Consensus.Goldilocks.Refinement.`; status is per row,
with remaining obligations owned by the Healing box. Exact statements live in
`Lemmas/Refinement/Evidence.lean` and `Transport.lean`. Paper locations are
`goldilocks-claims.tex` at `4ea71d05`, R.7/R.8/F.2/F.3/G1.5, and
`shared/composition.tex` §Blocks/§Model, as mapped in `goldilocks-mapping.md`.
Arguments are implementation derivations, not quotations. “Argument supplied”
does not mean its dependencies are proved.

| Declaration | Statement and dependencies | Paper argument/status |
|---|---|---|
| `Consensus.Goldilocks.Refinement.held_in_view` | Valid run, honest reader, non-genesis block held at mapped cut ⇒ canonical object in indexed view; tree_cases, accepted_in_view | F.2/G1.5: obtain earlier acceptance and its source event, including equal-time events. Argument supplied relative to simulation. |
| `Consensus.Goldilocks.Refinement.held_att_in_view` | Any held block's payload attestation is in reader view; held_in_view, payloadObjs, transitive containment | Genesis payload empty; canonical block carries each attestation. Argument supplied. |
| `Consensus.Goldilocks.Refinement.evidenceInView` | Finalized header payload attestations occur in reader view; simulation, finalized read, cache/chain and decode bridges | G1.5(b): identify held block, round-trip payload, apply held evidence. Argument supplied. |
| `Consensus.Goldilocks.Refinement.engine_outputValid` | ExecutionValid ⇒ every output valid; local coherence, chainTo, held_in_view | R.8/F.2: slot induction, linkage, strict parent slots, canonical provenance; no collision escape. Argument supplied; recheck after tagging. |
| `Consensus.Goldilocks.Refinement.engine_nested` | ExecutionValid ⇒ finalized nested in confirmed; simulation, outputs_nested | R.8/C0.1 at actual shape clock; empty validator type vacuous. Argument supplied. |
| `Consensus.Goldilocks.Refinement.engine_finalMonotone` | ExecutionValid ⇒ finalized monotone; simulation, finalized_monotone | R.8/C0.2: ordered mapped cuts and preserved store ancestry give prefix. Argument supplied. |
| `Consensus.Goldilocks.Refinement.noCollTransport` | ExecutionValid and no observed collision ⇒ NoCollRun on canonical simTrace | Proved (38cfe5f): all-occurrences provenance, including refused calls, observed header injectivity and tagged genesis separation; no provided freshness premise. |
| `Consensus.Goldilocks.Refinement.compatible_reads` | Canonical NoCollRun, honest bounded reads and compatible node tips ⇒ compatible engine chains | Proved: R.7/F.3 coherent union identifies cross-store parent walks. |
| `Consensus.Goldilocks.Refinement.convicted_count` | Finite key set with slashable canonical witnesses in A ⇒ cardinality ≤ convicted(A) | G1.5: injective rho.key image is contained in convicted. No honesty/collision premise. Argument supplied. |
| `Consensus.Goldilocks.Refinement.final_accountable_of_noColl` | Canonical NoCollRun and valid honest bounded reads ⇒ compatible or ≥2q−n convicted | R.7/G1.3–G1.5: node witnesses, held payload evidence, inject keys. Argument supplied relative to bridges. |
| `Consensus.Goldilocks.Refinement.finalizedAccountable` | FinalizedAccountable, retaining provided freshness/no-collision | Proved through canonical simulation and collision transport; no sorryAx. |
| `Consensus.Goldilocks.Refinement.shape_outputValid` | HoldsAlways output validity for every schema lookup | R.8: unfold valid runs and apply engine_outputValid. Argument supplied. |
| `Consensus.Goldilocks.Refinement.shape_nested` | Increasing schema ranks ⇒ HoldsAlways Nested | R.8: finalized/confirmed bridge or confirmed reflexivity. Argument supplied. |
| `Consensus.Goldilocks.Refinement.shape_finalMonotone` | Final schema lookup ⇒ HoldsAlways monotonicity | R.8: lookup identifies finalized. Argument supplied. |
| `Consensus.Goldilocks.Refinement.shape_finalAccountable` | Contract α≤1/3 ⇒ accountable safety, NO freshness premise | Proved: collision escape or convicted bound; 2q−n≥n/3, with freshness-free encoding and source transport. |

## Provenance leaves

Owner: R.6 box. Exact statements integrated and proved in Provenance and Steps.
Names have the same refinement prefix. No simTrace signing correspondence may
be used upstream of selected-duty/node agreement.

| Declaration | Dependencies / argument | Paper argument/status |
|---|---|---|
| `Consensus.Goldilocks.Refinement.engine_event_signing_history` | Actual store reachability, entry bounds, selected poll transitions, restart record; joint event/duty induction | Proved |
| `Consensus.Goldilocks.Refinement.engine_signing_history` | Event history and duty-prefix history | Proved |
| `Consensus.Goldilocks.Refinement.engine_restart_record` | Durable and restore definitions | Proved |
| `Consensus.Goldilocks.Refinement.engine_signings_nonFraming` | Signing history, G0.5/FG.client_safety | Proved; compiled closure has no sorryAx |
| `Consensus.Goldilocks.Refinement.engine_seen_att_signed` | Credentials, actual poll release→queued-sign inverse, same-event prefixes | Proved |
| `Consensus.Goldilocks.Refinement.engine_att_protected` | Nonframing, seen inverse, conflicts encoding; G0.5 corollary | Proved; compiled closure has no sorryAx |
| `Consensus.Goldilocks.Refinement.scheduled_proposal_releasable` | Actual EngineProposalAt, selected slot-start, pool/att provenance, drain/guard | Proved (f614a12) from actual engine inventory |

## Finite sleepy transport leaves

Owner: Healing box, integrated by the spec orb. Exact declarations are in
`Lemmas/Refinement/Sleepy.lean`, namespace `Consensus.Goldilocks.Refinement`.
All use canonical `simTrace` and, where needed, `runProposer S rho hn`.
No direct OPEN theorem remains in this module; finite inclusion closed at 5b33645.
sleepy_safe_engine is proved at catchUp+1; sleepy_safe_finite is proved via Regimes.sleepy_safe_before;
sleepy_grow_finite now uses proved finite inclusion and safety.
The two supplier definitions remain contracts, not proved suppliers.
Here Δp is the node parameter, c = catchUp = 18Δp, and b≤horizon.

| Declaration | Contract and dependencies | Paper argument/status |
|---|---|---|
| `Consensus.Goldilocks.Refinement.sleepy_ready` | Valid run, 0≤t≤horizon and engine Ready c at t ⇒ node ReadyAt; canonical awake/key equivalence | Proved; ready_transport supports the engine's existing cDur |
| `Consensus.Goldilocks.Refinement.sleepy_faultBound` | SleepyOn(1/2,c,0,b) ⇒ node FaultBound at ts(s)+d≤b for d∈{0,Δp,2Δp}; ready-implies-joined and key counts | Proved |
| `Consensus.Goldilocks.Refinement.SleepyServiceSupplier` | SyncUntil b ⇒ node SyncBefore H Δp b on valid runs with 0≤b≤horizon | Definition only; strict deadline slack and acceptance relay OPEN; repaired window may differ |
| `Consensus.Goldilocks.Refinement.sleepy_read_cut` | Ready reader at 0≤t≤horizon ⇒ CutAfter and Boundary at cutMap(endCut t), with output clock t; terminal filler included | Proved; ready_read_cut takes arbitrary nonnegative cDur |
| `Consensus.Goldilocks.Refinement.sleepy_safe_finite` | Valid run, canonical NoCollRun, SyncBefore through b and bounded slot quorum ⇒ ReadySafeOn 0 b | Proved at c3f8f4d via Regimes.sleepy_safe_before; not reached by Accepted |
| `Consensus.Goldilocks.Refinement.sleepy_include_finite` | Same finite premises, ready proposal at 0≤τ≤b, τ+6Δp≤t≤b, ready reader and CutAfter at t ⇒ proposal ancestry of read | Proved at 5b33645 through bounded later adoption and read service |
| `Consensus.Goldilocks.Refinement.sleepy_grow_finite` | Same service/quorum/noColl, t≥0, k≥1, b=t+(4k+6)Δp, selected-schedule recurrence and ready reader at b ⇒ fresh proposal after t included in ready b reads, excluded from ready t reads, with read extension | Body closed with proved finite inclusion and safety |
| `Consensus.Goldilocks.Refinement.SleepyRecurrenceSupplier` | Engine single-pattern recurrence on family grid ⇒ node recurrence for runProposer, same c and [0,b] | Definition only; grid/duration adapter OPEN |
| `Consensus.Goldilocks.Refinement.sleepy_proposal` | Valid run and ready node proposal at 0≤τ≤horizon ⇒ ready key and engine HonestProposal of encoded header | Proved through simTrace_block_released; ready_proposal supports arbitrary cDur |
| `Consensus.Goldilocks.Refinement.sleepy_inBy` | Valid run, NoCollRun, ready proposal and node inclusion at all ready CutAfter t reads, 0≤τ≤t≤horizon ⇒ engine InBy confirmed | Proved through confirmed_inBy; finalized_inBy supplies the final-output analogue |
| `Consensus.Goldilocks.Refinement.sleepy_safe_engine` | Valid run, NoCollRun, SyncBefore/quorum through horizon ⇒ engine ReadySafe (node catchUp+1) confirmed | Proved at 5d33450: arbitrary cuts via unit clock lag and last complete local event; standard axioms only |

R.1/R.2 motivate these reductions, but do not prove the engine bridges. The node-level
SleepySafePrefix row is retired (the prefix claim is Good.sleepySafe_prefix); IncludeSleepy
and GrowSleepy require whole-run SleepyRun. Neither supplies these finite consumers
directly. No unconditional Accepted endpoint is asserted. Timing/grid/catch-up/latency
scaling, finite locality, arbitrary-cut clocks and canonical collision encoding remain OPEN.

## Publication and network leaves

Engine thread owns Forwarding and NetworkTransport; R.6 owns ForwardOrigin and
ForwardHeldProcessed in PublicationProvenance. The runtime is installed by #124.
The following proved implementation rows are pinned to publisher branch 42efa6e;
they do not discharge total successful publication or the remaining network suppliers.

| Declaration (Refinement namespace) | Statement/status |
|---|---|
| `publisherExecution`, `publisherExecution_actual_iff` | Proved construction/characterization: actual executed batch prefix and all three release guards; actual event, timestamp and release. |
| `publisherExecution_objects_seen` | Proved AcceptedObjectsSeen for that concrete execution; no validity or network assumptions. |
| `stateAt_wrappersCover` | Proved by unconditional event induction: every held non-genesis root has a durable wrapper-map entry. |
| `onBlock_queues_acceptance` | Proved: WrappersCover and an actual successful onBlock cut append the acceptance wrapper. |
| `apply_forward_origin` | Proved: a queue member is old or comes from an actual successful cut at st.now. |
| `PSyncFGRowTransport` | Named OPEN proposition: PSync plus actual attestation send/admission supplies bounded processing, with ΔF=sp.Δ. |

Publication/network targets and their current status (proved rows are distinguished
from the remaining planned targets):

| Declaration or planned target | Required statement/status |
|---|---|
| `simTrace_forwardOrigin` | Proved, R.6: actual successful honest-origin wrapper release ⇒ actual acceptance at claimed stamp; delivery and own-tick branches. Compiled closure has no sorryAx. |
| `forwarding_at_acceptance` | Actual honest acceptance ⇒ successful matching wrapper release in same event |
| `forwarding_parent_earlier` | Child release ⇒ exact same-origin parent release earlier in actual release order and strictly earlier parent acceptance cut |
| `simTrace_forwardHeldProcessed` | Proved, R.6: pre-delivery held wrapper ⇒ earlier canonical processing at time≥stamp, or receiver's own actual acceptance. Compiled closure has no sorryAx. |
| `psync_block_processed` | PSync service to actual processing, explicit horizon/call bounds |
| `syncBefore_block_processed` | Deadline-cut service to actual processing; not whole-run Sync |
| `parent_wrapper_processing_before_child` | Parent-first prior recursive payload processing from held dependency and provenance |
| `network_psync_to_gst` | Previous service plus finite acceptance induction gives node GST premise |
| `network_syncUntil_to_syncBefore` | Bounded service plus finite acceptance induction gives node SyncBefore |

Claims Premises Sync/GST, Refinement, R5/OC and composition forwarding motivate
the targets; they do not prove the encoding/scheduling reductions. NoColl belongs
to acceptance/ancestry, not raw service. Revised publisher instantiation must be
a separate concrete OPEN obligation, not silently assumed by Accepted.

## Healing finite supplier inventory

Owner: healing paper orb and T3. Source: [healing plan at df71f0b](https://github.com/fradamt-agent/workbench/blob/df71f0b910b31159e99efe070f9b330fed800377/repos/goldilocks/notes/healing-simple/healing-plan.md).
Initial vocabulary is preserved in a separate, unintegrated `FinitePlan.lean` draft:
`ObservesThrough`, `ReadyService`, `CatchThrough`, `RecordsEventualThrough`,
`RecordsBoundedThrough`. The remaining scopes await exact Lean adapters.
Every supplier join is **OPEN** until its actual statement and argument are integrated.

| Section / planned leaf | Scope |
|---|---|
| §3 fresh_parent_catch | Healthy serviced interval, horizon-bounded cutoff, pre-epoch honest acceptance and receiver F below block ⇒ acceptance strictly before FirstCutFrom(epoch+2Δp) |
| §3 finite_ready_service | Bounded progress and full service deadline ⇒ actual positive-slot ReadyProposal; selected→proposal/support acceptance OPEN |
| §4 finite_reset | Local service for each used trigger, deadlines within horizon ⇒ re-epoched IsReset using HZ(r), cutZ(r), epoch Catch |
| §5 finite_raw_retention | Reset, explicit Tb and raw Protected ⇒ finalized ancestry or full viable-tree membership; CastAt gives frozen alternative |
| §6 finite_clean_drain | Live locks at bounded cuts have clean evidence; duty transfer additionally uses retention |
| §7 finite_ready_unanimous | ReadyProposal with bounded vote deadlines ⇒ all honest votes agree; no same-phase premise |
| §7 finite_ready_update | Actual bounded update ⇒ exact result/no veto/fast selection and source or higher-report alternative |
| §7 finite_record_base | Inherited current record ⇒ below recent actual raw origin or current F; equality-time cases explicit |
| §8 safety closure | Finite repaired base plus Healthy ⇒ bounded ReadySafe, without progress after preparation |
| §9 finite inclusion | ONE ready proposal after each trigger; strict recurrence needs no shift, closed-interval ReadyService uses t+1; deadlines/windows within horizon |

Separate PRE-reset phase-local retention/drain/acquisition (reset producer inputs)
from POST-reset global retention/drain to avoid a cycle. Preferred architecture:
one finite preparation theorem → shared recovered invariant → progress-free safety
and per-trigger liveness. Finite observation cuts need explicit adapters.

RC/post-heal boundary: finite preparation supplies RC only through its observation
cutoff. A separate recovered-state preservation theorem must extend it to each
later cut under health, without further progress. Whole-run `SA.Inv` quantifies
future honest calls and `Protected` includes retrospective raw selections; finite
PropPlus cannot supply that interface by truncation. Preserve the paper's B/W/Q/O
distinctions and actual frozen evidence in the adapter statements. The prior SA
`admitted_sources_after_two_leases` is horizon guarded and covers supported live
sources, not current all-admission RC. The 8Δ bound remains conditional on RC.
Catch additionally depends on implementing fresh `forwardObj` generation at
acceptance, separately from the existing parser and dependency policy.

| Draft sorry (namespace `Consensus.Goldilocks.Healing.FinitePlan`) | Argument / owner |
|---|---|
| `ready_after_trigger` | §9: instantiate ReadyService at t+1; integer positivity makes proposal strictly after t. Healing paper/T3; Lean OPEN. |
| `records_bounded_to_eventual` | §§7–8: forget covering producer bound k≤Q; retain genesis/F branches and introduce OriginFrom. Healing paper/T3; Lean OPEN. |
| `recovered_effective_safe` | §8: rewrite read_eq, use recovered compatibility/monotonicity. Healing paper/T3; Lean OPEN. Construction of RecoveredEffectiveThrough and engine observation coverage remain separate OPEN suppliers. |

Finite scope cautions: `HealthyRun` entails unbounded wakefulness; `SyncOn` bounds
sends but not receiver observations. Existing `Protected`, `OriginFrom` and reset
minimality can refer beyond Q. Each needs an explicit bounded adapter, not a renamed
whole-run assumption. RecRet has distinct forms: E bounds consumers only, B also
bounds covering producer by Q, C bounds it by the consumer cut. E does not imply
B/C from bounded progress. B→E preserves the old-origin antecedent and whole-trace
HonestBlocks carrier; it is not prefix-local. Prefer a recovered effective-record
invariant with chain agreement and progress-free preservation. Eventual-origin
retention is an optional sufficient route, not its definition.

§11 supplies conditional coefficients, not unconditional timing proofs:
δt=6+f; h=104k+628+48δt+12f+144(m+2)+b; available/stable
heal=c+1+2(h+8) engine units, assuming ΔF≤fΔp, Tb≤bΔp and
Δp≤2Δe (Δp = Δe since 2026-11-04) plus finite-margin proofs. No arbitrary b=8 and no extra 2W.

Paper update at workbench `925bc1a`, healing-plan §§14–15: local prefix repair
from an actual non-vetoed result D≥B permits either writing D or retaining E≥D;
strict overwrite is unnecessary. DCA inclusion additionally needs head≥B.
These local arguments, conditional event preservation and temporal facts from
ResilienceReader are PAPER-CLOSED, not elaborated supplier proofs. Actual restored
result production/non-veto, preservation of the head path, RecRet orientation and
recovered suffix agreement/base closure remain OPEN. Ready-reader time alone does
not certify a successful result. Legacy OutageRepairReady is not the minimal
current-node ancestry interface; none of these local facts alone discharges R5
or healedSafe.

Final recurrence follows the owner's corrected good-window shape: every X slots
there is a window containing two honest ready proposers separated within a bounded
internal span. Use a generic `.recur` pattern for that window and gap X, not
Pattern.single with a maximal gap tied to timeout. X is arbitrary; δt may depend
only on the window's internal span, never on X. The revised paper gives a larger
conditional sparse candidate, not a proved two-proposer pattern. Do not silently
substitute its stronger premise for the owner's two-proposer target, require
consecutive proposers, or fix gap 2.

Source: [corrected recurrence note at e291a44](https://github.com/fradamt-agent/workbench/blob/e291a44494699ad5288f84be354e65335ad0f4fd/repos/goldilocks/notes/healing-simple/final-recurrence-contract.md).
For fixed window-local exposure a and c=cF, put L=a+c, D=L+1 and δt≥D.
The conditional construction has N=ceil(δt/2)+2ceil(D/2), offsets
P=[0,2,…,2N] and span S=2N. Its outer recurrence gap X is arbitrary subject
to tolerance X≥S+2, with δt unchanged across X. Conditional latency is
4Δp(X+S)+d_out, not a proved protocol guarantee. For c=2,a=1,δt=4,
this needs seven nonadjacent proposers at [0,2,…,12], not two.

The argument bootstraps the arbitrary current entry at a mature anchor, then
services a new entry and its actual successor within D each. OPEN suppliers:
window-local H4 (target a≤1), current-entry progress bootstrap, usable records
and bounded T_C, productive non-⊥ AC blocks, surviving chain and cache acceptance.
Timing enumeration and periodic guards check arithmetic only. Two-proposer
minimality remains OPEN: a slot-2 justification of a slot-0 entry whose previous height is not justified creates
its successor but does not yet finalize slot 0. This is not an infinite-run
counterexample to recurring pairs, nor evidence for a δt–X necessity.

Historical boundary (read-back from thread T-01a19232-fc9c-7223-b619-3ae2d94fc930):
the old round theorem uses four distinct slots 0,R,c,2R+κ with
c∈[R+κ,2R], full HEALING_INPUT and δt=2R independent of recurrence frequency.
It does not automatically transfer to current loose BJ. N2 is refuted for the
window fold by stale-row finality at slot 12 and supplies no present negative.
The scratch eviction cycle assumes missing later-entry source service; it is not
a full FG-SA counterexample or a refutation under adequate post-heal service.

Required new OPEN leaf: cross-window coverage-or-replacement under actual AC
service. It must permit timeout and eviction without assuming pending-pair
monotonicity, and establish eventual fresh-proposal coverage by actual successor
service or a justified replacement. Current two-proposer recurrence across several
windows has no proved bound on the number of windows. Keep the seven-anchor route
conditional and unadopted; no δt–X dependence has been established.

Current synthesis keeps the contract parameterized by a fixed local pattern and
arbitrary outer X; generous fixed δt is permitted independently of X. The four
offsets [0,3,5,7] with cF=2 and δt=4 have a conditional local argument
(workbench a2a9f61, follow-up 9191c67); [0,2,4] is conditional on the first
anchor creating an entry. Neither fixes the final recurrence. Two or three
anchors across bounded multiple windows remain OPEN, with no full Healthy GST0
impossibility established.

The source-service supplier must provide usable same-entry rows already emitted
or available by the deadline, OR a retained JUSTIFIED crossing (or accepted
coverage). It must not require every validator to report every entry. GST0
clean-record induction on a coherent origin chain rules out persistent
pair-permission dirt; source timing and deduplication remain obligations.
The modeled n=13 next-slot split repair at t_s+10Δ supplies no δt–X tie.
Report-cover, cache acceptance and the old-entry parent/exposure audit remain OPEN.

The single-proposer-gap analysis in the contribution at workbench
`7a8fbe9943200799dc9a866f9b5103051ef2ae51` is superseded as a contract design:
neither δt≥a+c+g−1 nor its maximal-g formulas select the final recurrence.
Loose guarantees do not justify stronger assumptions. The earlier UPat/Mstar/
contiguous O1 route also remains parked. The r9 loose-BJ A/B/C service reasoning
must be connected to the revised window, not silently reused as a completed bridge.

OPEN internal suppliers, not new generic contract assumptions: H4 exposure including
faulty-created successors; parameter-bounded common-chain service time T_C and dirty
count d; loose-BJ dirty-index charging; selected honest ready proposer → actual
non-⊥ AC block on the surviving chain, with usable rows, delivery/inclusion and
eventual cache acceptance. Selection alone is not P4. The revised good-window
productivity and preservation obligations remain to be stated; C alone does not
bound dirty entries or prove finality progress. No final latency coefficient is selected.

## Healing pivot compatibility suppliers

The named pivot leaves below are now proved, by
the healing source-service work (OpenAI pivot prover, coordinated by the healing lead).
All retain `ResetPremises`, `Catch(2Δ)`, the ready proposal, and the existing drain.
They are proof obligations, not additional protocol premises.

| Declaration (`Consensus.Goldilocks.Healing.` prefix) | Consumer obligation | Dependencies / proof status |
|---|---|---|
| `proposal_stored_locks_compatible_old` | Proposal stored high locks compatible with each `OldSrc` | PROVED: stored provenance and proposal timing reduce to label u−1 optimism; `optimistic_prefix_compatible_old` uses historical votes for strict labels and explicit same-label fast/optimistic compatibility |
| `proposal_start_supported` | Proposal start below the actual honest vote head, under earlier-votes=P | PROVED at c37143b, standard axioms; clean source votes discharge the source-vote adapter |
| `vote_old_live_lock_below_parent` | Viable ancestor of each non-current live read-point lock below the proposal parent | PROVED, compiled sorry-free in the 5e49ee92 audit; the head/stamp held-at-proposal and proposal-domain joins formerly recorded here no longer leave a direct hole |

The deepest set remains `{start} ∪ OldSrc`; floor/root and same-slot optimistic
arguments are unchanged. The unused `hnoSlow`, `late_slow_lock_votes`,
`clean_slowLock_false`, and vacuous `clean_slow_transfer` route is retired.
The §67 raw-boundary/slow-exclusion plan is superseded, not a proof dependency.
No threshold/drain change or new upper bound on k is made. Source producers must
retain bounded `SA.Inv`, global `Anc U B fcRoot`, exact window cutoffs, receiver
F≤source and per-counted-vote writer evidence; they cannot assume these consumers.

## Approved conditional Sleepy supplier skeleton

The #127 migration landed at 14f5ce06: finite service consumers use
`Compose.SleepyServiceBefore` (fresh processing or retained stamped pool evidence),
and whole-run signatures remain wrappers. Seven Service modules and the combined
chain compiled; changed/landing gates passed with 22 skips and boundary passed.
#127 closed with a retained-pool concrete-instance check and compiled reduced-facts
regression, not a full engine replay; full tier was not run. At that migration the engine service
suppliers remained OPEN. They now have proved bodies via finite SVC; #128 is historical,
not a current obstruction. Their former shared accepted_heal type dependency is gone since 4078bc74.

`Lemmas/Refinement/NonfinalSuppliers.lean` contains the lead-reviewed Sleepy
signature slices. It imports AcceptanceDefs for its existing coefficients and
now feeds the Sleepy liveness endpoint; it does not enter Main/Solution. All names below are in
`Consensus.Goldilocks.Refinement`. No Healthy premise or endpoint duration changes.

| Named obligation | Status and exact remaining work |
|---|---|
| `confirmed_duration_supply` | Body closed using OPEN accepted_catchUp_ge_sleepy, including Healthy queries; no coefficient selected. |
| `sleepy_query_sync` | Body proved: canonical finite SVC through the exact engine deadline; full closure sorry-free since 4078bc74. |
| `sleepy_query_population` | Body closed at finite slot points via duration monotonicity; transitively OPEN through the catch-up bound. |
| `sleepy_query_producer` | OPEN transitively; assembly body now uses the separate slot and event leaves below, then proved own-proposal acceptance. |
| `sleepy_query_slot` | Body closed: recurrence/grid selects exact-cDur readiness, positive slot, strict freshness and 6Δp margin; joint lower bounds remain OPEN. |
| `confirmed_slot_event` | Body closed: actual scheduled canonical proposal from joined readiness; duration dependency retained. |
| imported `sleepy_include_finite` | Proved at 5b33645 from finite service/population and 6Δp margin. |

These six named supplier obligations contain **no direct sorry**.
The two named coefficient lower bounds are proved. Since 4078bc74 the closed supplier bodies no
longer reach sorryAx through a shared accepted_heal type dependency.
`sleepy_serviced_proposal_supply` assembles the selected actual proposal and concrete
service record; `sleepy_serviced_proposal_coverage` applies finite inclusion only to
that serviced proposal. Their bodies are not no-sorry proofs. Actual acceptance uses
`Compose.proposal_accepted`. The directional readiness proof preserves exact cDur.
Healthy preparation/preservation, arbitrary-cut safety and outage were separate
landings; their proof gaps remain OPEN as listed in the master view.

## Approved OPEN Healthy/base supplier skeleton

`Lemmas/Refinement/HealthySuppliers.lean` states the five lead-reviewed OPEN
obligations below, in `Consensus.Goldilocks.Refinement`. Signature approval is
not proof completion. The module preserves endpoint premises and separates
finite `[ready, heal]` preparation from health-only preservation.

| Named leaf | Remaining obligation |
|---|---|
| `healthy_preparation_initialize` | Proved: the joint (E) tuple from the reset envelope (`healthy_reset_envelope`) and the coefficient inequality `accepted_heal_ge_reset`; explicit record/cache/expiry/service timing W and a finite preparation schedule. R0 replaced the former `healthy_old_inventory_initialize`: nothing outside `healthy_preserve`'s own preservation plumbing read its coverage-or-below-hj inventory. |
| `healthy_old_row_realize` | Deleted at fa194fa6 (#136, sorry group A; it had no consumer). It stated the OPEN first-arrival/self-entry join: the exact old-source antecedent identifies E with root a.T and the receiver's replay height. |
| `healthy_prepare` | Record and recent stored-lock preparation at cutMap(endCut heal), from W, the preparation schedule and progress only on `[ready, heal]` (body proved; no inventory since R0). |
| `healthy_preserve` | Body proved: preservation of records and recent stored locks at every later canonical cut through engine end, including same-time intermediate states, under health without later progress. No timestamp bound on the boundary cut is asserted. |
| `healthy_vote_row_replacement` | Deleted at fa194fa6 (#136, sorry group A; it had no consumer). It stated the OPEN eventual-coverage-to-label-bounded replacement matching BaseFacts (replacement label ≤ predecessor slot), over `HealthyOldInventory` as an explicit premise. |

`healthy_old_inventory_preserve` delegates to the proved
`Healing.oldHonest_inventory_preserved` from 9f5d6e7. Monotone hj preserves
initialization; it does not produce it. Inventory and state facts deliberately
use eventual whole-run origins, **not finite-prefix preparation certificates**.
Timing exposes ready≤ts(s₀), record/cache service and old-lock expiry margins≤heal.

Remaining consumer adapters stay OPEN: arbitrary-cut read safety and temporal
monotonicity, old read-point lock compatibility/slow-boundary production, event
sources and vote extension, frozen viability and finite service, and endpoint
assembly. The five leaves do not discharge these joins. No ReadySafe-as-base or
new Healthy premise is introduced. `held_row_causal_source` remains external
provenance evidence only; it does not initialize or renew old-entry coverage.

## Healed safety and outage endpoints now assemble named OPEN suppliers

`accepted_healedSafe` and `accepted_persists` no longer contain direct sorries.
Their endpoint types and collision escapes are unchanged. This is skeleton
wiring, not closure of either proof. The common coefficient definitions moved
unchanged to `AcceptanceDefs.lean` to avoid a supplier/Accepted import cycle.
The table records the obligations as they were named; in the compiled audit at 70e90b44 none of
these five leaves is a direct owner.

| Named leaf | OPEN obligation |
|---|---|
| `healthy_cut_agreement` | Actual engine-cut agreement from Healthy state facts, including equality-time cuts before endCut(heal). Receives h0/hb and actual finite ready→heal progress; post-endCut facts alone are not that transport. |
| `healthy_cut_monotone` | Temporal prefix extension at arbitrary ordered engine cuts with both exact-cDur readiness tests; same-time/pre-endCut transport remains owed. |
| `outage_pre_service` | Canonical service through recipient deadlines ≤ outage start, not unrestricted late-wake service. |
| `outage_arm` | Effective-record arming at original endCut(T), including inherited records and lookup-none/frame.F fallback; frame membership and original read-prefix witness. |
| `outage_repair` | Slow-only recovery for every reader ready from `b₁ + recovery·Δ` (`recovery = 9`): O1 formation at labels `j₀ − 1` and `j₀`, O2 retention (base handoff, VA), O3 (the `k − 1` conflicting-label count, the cohort count at the reader gates, the veto-harmless lemma, S5), O4 reader bridge. |

`healthy_ready_safety` consumes initialization→preparation→preservation and the
two cut adapters. Its Accepted wrapper handles an empty validator type and heal
beyond the horizon without strengthening premises or shrinking InCuts.
`outage_protected` assembles finite pre-service, arming and repair with the
`ProtectedReadyFrom` quantifiers of `persists` (every ready reader from the
recovery point; 2026-11-02, replacing the ResilienceReader windows). The five leaf signatures were approved as OPEN.
Existing Healthy leaves and coefficient witnesses remain transitive gaps.
Full proof completion, frozen-service/source/vote joins and other Accepted
adapters remain OPEN; none are supplied by successful elaboration of this wiring.

## What the master inventory does not certify

The complete compiled leaf list does not discharge any OPEN supplier or promise
that joint leaves already expose every internal mathematical step. Healthy frozen
service, producer budgets, old-entry production and outage repair still need proofs
and may require further named subleaves. Signature approval and mapped reachability
are not proof completion or a Main/Solution certificate.
