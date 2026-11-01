# Accepted proof dependencies

This is the integration ledger for the Goldilocks `Accepted` skeleton.
The master status view records the complete compiled endpoint leaf inventory;
mathematical proof completion remains **OPEN**. Historical/planned sections below
are not elaborated evidence merely because a downstream theorem uses `sorry`.

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

Current status: **endpoint skeleton wired; mathematical proofs OPEN**. Every
Accepted field now assembles named suppliers rather than containing a direct
adapter sorry. Numeric witnesses remain three direct OPEN leaves. The master
view below is compiled reachability, not proof closure or evidence that every
joint supplier has been decomposed into its eventual proof obligations.

## Master status: every Accepted field, grouped by leaf owner

Baseline audited: main `e6a8ab76e0dbf5f43e4fabc654a44f17a9d20a3b`.
The post-wiring audit uses `spec-surface dependencies --from
Consensus.Goldilocks.Refinement.accepted --modules
ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted`, including type
and body edges and cycle-safe transitive traversal. Names below have prefix
`Consensus.Goldilocks.Refinement.`. Each set enumerates **direct sorry owners**;
an assembly depending on them is not an additional leaf.

| Set | Owner | Complete direct leaf list |
|---|---|---|
| C | Spec orb, joint coefficient synthesis | `accepted_catchUp`, `accepted_heal`, `accepted_latency` |
| F | Four-anchor/final service owner | `final_window_extract`, `final_inherited_progress`, `final_row_supply`, `final_cache_acceptance` |
| H | Healing paper/T3; Spec orb integration | `healthy_old_inventory_initialize`, `healthy_prepare`, `healthy_preserve`, `healthy_cut_agreement`, `healthy_cut_monotone` |
| N | Healing paper/T3; Spec orb integration | `healthy_confirmed_supply` |
| O | Healing/outage owner; Spec orb integration | `outage_pre_service`, `outage_arm`, `outage_repair` |
| S | Spec orb, with engine service/population and recurrence owners | `confirmed_duration_supply`, `sleepy_query_sync`, `sleepy_query_population`, `sleepy_query_slot`, `confirmed_slot_event` |
| R | Spec orb safety-input production | `sleepy_safety_inputs` |
| I | Healing box finite Sleepy | `sleepy_include_finite` |
| E | Healing box arbitrary-cut Sleepy transport | `sleepy_safe_engine` |

| Accepted field / branch | Reachable OPEN leaves by owner set | Direct adapter sorry? |
|---|---|---|
| outputValid | none | no |
| nested | none | no |
| finalMonotone | none | no |
| finalAccountable | C (contract/type dependencies) | no |
| healthyLive, final | C ∪ F | no |
| healthyLive, available/stable | C ∪ N | no |
| sleepySafe, available/stable | C ∪ R ∪ E | no |
| sleepyLive, available/stable | C ∪ S ∪ I | no |
| healedSafe, available/stable | C ∪ H | no |
| persists | C ∪ O | no |
| progressFits, progressTolerant, admissible | C | no |
| serves | none (schema provides final output) | no |
| claims and complete accepted | C ∪ F ∪ H ∪ N ∪ O ∪ S ∪ R ∪ I ∪ E | no |

This closure has **24 direct sorry owners**. At baseline the two nonfinal
healthyLive branches and sleepySafe/sleepyLive were direct adapter holes; all
four now have assembly bodies. Capability budgets remain distinct even though
available and stable both project to confirmed output. Collision escapes,
empty-validator handling, exact cDur, deadline scaling and endpoint premises
are unchanged. No Main/Solution certification is claimed.

OPEN but **not currently reachable from accepted**: `healthy_old_row_realize`,
`healthy_vote_row_replacement` (Healing paper/T3, first-arrival/self-entry and
label-bounded replacement), and `sleepy_safe_finite` (Healing box finite R.1).
Their absence from the closure means the current joint leaves do not yet call
them, not that they are proved or unnecessary. Likewise imported implementation
modules are not automatically proof dependencies. The older draft inventories
below describe planned internal decompositions, not extra leaves in this closure.

| Declaration | Paper argument/status |
|---|---|
| `Consensus.Goldilocks.Refinement.healthy_confirmed_supply` | OPEN, Healing paper/T3 with Spec orb integration: finite Healthy preparation, exact-cDur-ready actual producer selection and its budget, frozen service and deadline coverage remain inside this joint existential. Only the selected accepted proposal is covered; no new endpoint assumption. |
| `Consensus.Goldilocks.Refinement.sleepy_safety_inputs` | OPEN, Spec orb with engine/Healing box: joint duration, finite-horizon canonical SyncBefore and population production with no progress, query or ready-reader existence premise. Existing sleepy_safe_engine retains arbitrary-cut transport. |
| `Consensus.Goldilocks.Refinement.confirmed_duration_supply` | OPEN, Spec orb: joint coefficient bound, not positivity or readiness upgrade. |
| `Consensus.Goldilocks.Refinement.sleepy_query_sync` | OPEN, engine/Spec orb: canonical service through exact deadline. |
| `Consensus.Goldilocks.Refinement.sleepy_query_population` | OPEN, Spec orb: finite slot-point population transport. |
| `Consensus.Goldilocks.Refinement.sleepy_query_slot` | OPEN, recurrence/Spec orb: exact-cDur readiness, strict freshness and 6Δp service margin. |
| `Consensus.Goldilocks.Refinement.confirmed_slot_event` | OPEN, Spec orb: joined/eligible state and actual scheduled event; eligible slot is not an event. |
| `Consensus.Goldilocks.Refinement.healthy_old_inventory_initialize` | OPEN, Healing paper/T3: global old signed-entry inventory including unseen future arrivals, §§27/28. |
| `Consensus.Goldilocks.Refinement.healthy_prepare` | OPEN, Healing paper/T3: finite ready→heal record/cache/stored-lock preparation consuming inventory. |
| `Consensus.Goldilocks.Refinement.healthy_preserve` | OPEN, Healing paper/T3: all later canonical cuts, health only, no later progress. |
| `Consensus.Goldilocks.Refinement.healthy_cut_agreement` | OPEN, Spec orb/Healing: arbitrary-cut agreement, including pre-endCut equality-time transport. |
| `Consensus.Goldilocks.Refinement.healthy_cut_monotone` | OPEN, Spec orb/Healing: ordered-cut extension with both readiness tests and equality-time transport. |
| `Consensus.Goldilocks.Refinement.outage_pre_service` | OPEN, engine/outage: recipient-deadline service bounded by outage start. |
| `Consensus.Goldilocks.Refinement.outage_arm` | OPEN, outage: effective-record lookup or F fallback with original read prefix. |
| `Consensus.Goldilocks.Refinement.outage_repair` | OPEN, outage: lifetime, repair, old output compatibility and exact reader windows. |

## Historical per-field axiom audit at 259d0330 (superseded above)

Audited main at `259d0330ace0464632c03344568c6fe518f33b98` with `#print axioms`
for every `accepted*` declaration and the nonframing/receipt/Sleepy bridges.
`lake exe spec-surface dependencies --from ... --modules ...` supplied the compiled
dependency graph; traversing it identifies the following exact direct `sorryAx` owners.
Names in this section have prefix `Consensus.Goldilocks.Refinement.`.
`C` abbreviates the set `{accepted_catchUp, accepted_heal, accepted_latency}`.
`F` abbreviates `{final_window_extract, final_inherited_progress, final_row_supply,
final_cache_acceptance}`. These are named sets of leaves, not extra assumptions.

| Audited root | Reachable direct sorry owners |
|---|---|
| accepted_catchUp | accepted_catchUp |
| accepted_heal | accepted_heal |
| accepted_latency | accepted_latency |
| accepted_coefficients, accepted_coefficients_catchUp | C |
| accepted_outputValid | none |
| accepted_nested | none |
| accepted_finalMonotone | none |
| accepted_finalAccountable | C (contract/type dependencies, not encoding/transport gaps) |
| accepted_healthyLive_final | C ∪ F |
| accepted_healthyLive | C ∪ F ∪ {accepted_healthyLive} |
| accepted_sleepySafe | C ∪ {accepted_sleepySafe} |
| accepted_sleepyLive | C ∪ {accepted_sleepyLive} |
| accepted_healedSafe | C ∪ {accepted_healedSafe} |
| accepted_persists | C ∪ {accepted_persists} |
| accepted_progressFits, accepted_progressTolerant, accepted_admissible | C |
| accepted_claims, accepted | C ∪ F ∪ {accepted_healthyLive, accepted_sleepySafe, accepted_sleepyLive, accepted_healedSafe, accepted_persists} |
| engine_signings_nonFraming, engine_att_protected | none |
| simTrace_forwardOrigin, simTrace_forwardHeldProcessed | none |
| sleepy_ready, sleepy_faultBound, sleepy_read_cut, sleepy_proposal, sleepy_inBy | none |
| sleepy_safe_finite | sleepy_safe_finite |
| sleepy_include_finite | sleepy_include_finite |
| sleepy_grow_finite | sleepy_safe_finite, sleepy_include_finite |
| sleepy_safe_engine | sleepy_safe_engine |

Nonframing is not a separate `Accepted` field: the audited signing/protection
theorems provide it. Roots marked `none` use only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. A direct sorry in an adapter does not
reference its intended future suppliers, so this graph is not the remaining-work
plan: in particular the open Accepted Sleepy fields do not yet reach the Sleepy
consumer leaves. All Run unforgeability suppliers are proved, as recorded below.

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

The root fixes standard fractions, `finalWindow S = [0,δt−1,δt+1,δt+3]`,
δt≥4 and positive outage look-back η. Engine-unit outage lag is 8k−8 and budget
is min(η,4k−6), corrected in f416034 to imply the unchanged node time window at Δp=Δe+1.
Only catch-up (positive Nat), heal and latency (Nat-valued functions at each gap)
are existential. They are independent of validator set, execution and horizon.
Every positive outer gap X is an index; tolerance uses X=span+2. Timeout has no X.
The three numeric leaves must be solved jointly with the named endpoint suppliers;
their arbitrary separate instantiation would not prove the endpoint. Local-pattern
sufficiency remains OPEN, not supplied by the timeout inequality alone.
The one-Δ model maps Δ_F:=Δ_p, hence c_F=2; this deliberately excludes the
intended model's independent slower FG delivery. The engine-owned actual-row
service bridge, first-honest-descendant usable rows (exposure up to δt−2) or
earlier justification, inherited progress, productive chain and cache acceptance
remain OPEN. The four-anchor paper argument is conditional on those joins.
Pinned argument: [general fixed timeout](https://github.com/fradamt-agent/workbench/blob/fd8cb311fac057347fb49e32cf17841e27a75e76/repos/goldilocks/notes/healing-simple/four-anchor-window.md#general-fixed-timeout-d4).

| Declaration | Paper argument/status |
|---|---|
| `Consensus.Goldilocks.Refinement.accepted_catchUp` | OPEN: finite positive uniform catch-up; canonical timing adapter required. Spec orb. |
| `Consensus.Goldilocks.Refinement.accepted_heal` | OPEN: finite healing at each gap, joint with bounded preparation/preservation; no whole-run progress. Spec orb. |
| `Consensus.Goldilocks.Refinement.accepted_latency` | OPEN: finite latency at every gap; final local-pattern service and cache acceptance unresolved. Spec orb. |
| `Consensus.Goldilocks.Refinement.accepted_outputValid` | Proved through shape_outputValid; compiled closure has no sorryAx. |
| `Consensus.Goldilocks.Refinement.accepted_nested` | Reduction to shape_nested; exact generic field, no collision escape. |
| `Consensus.Goldilocks.Refinement.accepted_finalMonotone` | Reduction to shape_finalMonotone; exact generic field. |
| `Consensus.Goldilocks.Refinement.accepted_finalAccountable` | Body closed through shape_finalAccountable at fixed 1/3; only the three coefficient leaves are reachable through the contract type. Encoding/transport is proved. |
| `Consensus.Goldilocks.Refinement.accepted_healthyLive` | Assembly: available/stable use healthy_confirmed_supply and proved payload projection; final uses accepted_healthyLive_final. Named suppliers remain OPEN. |
| `Consensus.Goldilocks.Refinement.final_window_extract` | OPEN: actual ready four-anchor proposals/cuts on the canonical finite trace, surviving ancestry and carrier processing by query + latency(.final,i)·Δe. Joint accepted_latency synthesis must supply transport slack, not just A3≤deadline. |
| `Consensus.Goldilocks.Refinement.final_inherited_progress` | OPEN: inherited post-A0 entry has no birth lower bound; if uncrossed through A1's parent, distinct credited/pool current-entry progress reaches quorum. |
| `Consensus.Goldilocks.Refinement.final_first_crossing` | Body closed conditional on InheritedProgress: birth-s entry OR first post-A0 crossing by s+d−1 (justify OR timeout); only the latter has exposure age≤d−2. Canonical store coherence, actual mandatory inclusion and dedup are derived, not extra premises. |
| `Consensus.Goldilocks.Refinement.final_row_supply` | OPEN: designated protected first entry/actual bound successor, local no-timeout condition; already justified OR distinct honest exact valid paired targets, prior matching reports/dedup included. Report/delivery bounds apply only to the quorum branch. |
| `Consensus.Goldilocks.Refinement.final_bounded_crossings` | Body closed conditional on FirstCrossing and RowSupply: justification by s+d+1, actual bound successor with separate birth-s w≥1/post-A0 w≥2 cases, no timeout before designated service and chain finalization above A0 by A3. Uses actual pool inclusion/dedup and target-before-timeout at equality. |
| `Consensus.Goldilocks.Refinement.final_cache_acceptance` | OPEN, consumes only A3 chain-finalized coverage of A0, projected from bounded crossings by the assembly: actual cache ancestry at the exact engine-scaled query endpoint and later horizon-bounded ready CutAfter reads. Not arbitrary-delay acceptance or receipt alone. |
| `Consensus.Goldilocks.Refinement.final_payload_projection` | Body closed conditional on window extraction and CacheCoverage: raw own-block release via simTrace_block_released and final-output chain membership at engine endCut. Preserves existing cDur, reader condition, latency scaling and collision escape; no forwarding-envelope origin assumption. |
| `Consensus.Goldilocks.Refinement.accepted_healthyLive_final` | Assembly explicitly references extraction, inherited progress, first crossing, row supply, bounded crossings, cache acceptance and payload projection. First crossing, bounded crossings and payload projection are conditionally body closed; the other four suppliers remain sorry leaves. The three closed bodies' only transitive sorry owners are accepted_catchUp/heal/latency through their types, not canonical transport or supplier proofs. No new public Healthy premises; accepted coefficients remain OPEN. |
| `Consensus.Goldilocks.Refinement.accepted_sleepySafe` | Assembly over sleepy_safety_inputs and sleepy_safe_engine, with directional readiness and empty-V handling; both suppliers OPEN. |
| `Consensus.Goldilocks.Refinement.accepted_sleepyLive` | Assembly over selected serviced Sleepy proposal, finite inclusion and proved payload projection; suppliers OPEN. |
| `Consensus.Goldilocks.Refinement.accepted_healedSafe` | Assembly over finite preparation, progress-free preservation and arbitrary-cut adapters; suppliers OPEN. |
| `Consensus.Goldilocks.Refinement.accepted_persists` | Assembly over pre-service, effective-record arming and actual repair; suppliers OPEN, no late-wake SyncRun inference. |
| `Consensus.Goldilocks.Refinement.proposal_releasable` | Proved (f614a12): scheduled proposal dependencies are in the actual engine closure; Steps wrapper of scheduled_proposal_releasable. |
| `Consensus.Goldilocks.Refinement.simTrace_att_unforgeable` | Proved (c52d387): actual canonical attestation origin/authentication history. |
| `Consensus.Goldilocks.Refinement.simTrace_block_unforgeable` | Proved (f9963e2): valid canonical calls carrying an honest proposer's block have an earlier own-block cut. |
| `Consensus.Goldilocks.Refinement.simTrace_carried_vote_unforgeable` | Proved (62d11ce): carried vote source and recursive object history. |
| `Consensus.Goldilocks.Refinement.simTrace_msg_unforgeable` | Proved (62d11ce): actual message signing/admission provenance. |
| `Consensus.Goldilocks.Refinement.simTrace_vote_released` | Proved (54a9a89): valid execution plus canonical GoldilocksRun gives release of emitted votes at their emission time. |

## Ownership and architecture

The four-anchor skeleton above is pinned to workbench `b3ca078`,
`four-anchor-window.md` and `fixed-timeout-synthesis.md`. Its statements are under
review, not proved. The cache endpoint is the original query plus the SAME joint
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
mutation. The protocol timing target is Δp = Δe + 1, with delivery-time relay.

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
Three direct theorem leaves remain OPEN: sleepy_safe_finite, sleepy_include_finite and
sleepy_safe_engine. sleepy_grow_finite has a closed body but reaches the first two.
The two supplier definitions remain contracts, not proved suppliers.
Here Δp is the node parameter, c = catchUp = 18Δp, and b≤horizon.

| Declaration | Contract and dependencies | Paper argument/status |
|---|---|---|
| `Consensus.Goldilocks.Refinement.sleepy_ready` | Valid run, 0≤t≤horizon and engine Ready c at t ⇒ node ReadyAt; canonical awake/key equivalence | Proved; ready_transport supports the engine's existing cDur |
| `Consensus.Goldilocks.Refinement.sleepy_faultBound` | SleepyOn(1/2,c,0,b) ⇒ node FaultBound at ts(s)+d≤b for d∈{0,Δp,2Δp}; ready-implies-joined and key counts | Proved |
| `Consensus.Goldilocks.Refinement.SleepyServiceSupplier` | SyncUntil b ⇒ node SyncBefore H Δp b on valid runs with 0≤b≤horizon | Definition only; strict deadline slack and acceptance relay OPEN; repaired window may differ |
| `Consensus.Goldilocks.Refinement.sleepy_read_cut` | Ready reader at 0≤t≤horizon ⇒ CutAfter and Boundary at cutMap(endCut t), with output clock t; terminal filler included | Proved; ready_read_cut takes arbitrary nonnegative cDur |
| `Consensus.Goldilocks.Refinement.sleepy_safe_finite` | Valid run, canonical NoCollRun, SyncBefore through b and bounded slot quorum ⇒ ReadySafeOn 0 b | OPEN finite R.1 localization |
| `Consensus.Goldilocks.Refinement.sleepy_include_finite` | Same finite premises, ready proposal at 0≤τ≤b, τ+6Δp≤t≤b, ready reader and CutAfter at t ⇒ proposal ancestry of read | OPEN finite R.2 localization |
| `Consensus.Goldilocks.Refinement.sleepy_grow_finite` | Same service/quorum/noColl, t≥0, k≥1, b=t+(4k+6)Δp, selected-schedule recurrence and ready reader at b ⇒ fresh proposal after t included in ready b reads, excluded from ready t reads, with read extension | Body closed; transitive OPEN leaves sleepy_include_finite and sleepy_safe_finite |
| `Consensus.Goldilocks.Refinement.SleepyRecurrenceSupplier` | Engine single-pattern recurrence on family grid ⇒ node recurrence for runProposer, same c and [0,b] | Definition only; grid/duration adapter OPEN |
| `Consensus.Goldilocks.Refinement.sleepy_proposal` | Valid run and ready node proposal at 0≤τ≤horizon ⇒ ready key and engine HonestProposal of encoded header | Proved through simTrace_block_released; ready_proposal supports arbitrary cDur |
| `Consensus.Goldilocks.Refinement.sleepy_inBy` | Valid run, NoCollRun, ready proposal and node inclusion at all ready CutAfter t reads, 0≤τ≤t≤horizon ⇒ engine InBy confirmed | Proved through confirmed_inBy; finalized_inBy supplies the final-output analogue |
| `Consensus.Goldilocks.Refinement.sleepy_safe_engine` | Valid run, NoCollRun, SyncBefore/quorum through horizon ⇒ engine ReadySafe confirmed | OPEN arbitrary-cut clock/compatibility transport; endCut alone insufficient |

R.1/R.2 motivate these reductions, but do not prove the engine bridges. Existing
SleepySafePrefix requires SyncRun with receiver obligations beyond b; IncludeSleepy
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
Δp=Δe+1≤2Δe plus finite-margin proofs. No arbitrary b=8 and no extra 2W.

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
minimality remains OPEN: a slot-2 justification of a slot-0 unbound entry creates
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

The following named leaves in `Healing/Outcome/Pivot.lean` are **OPEN**, owned by
the healing source-service work (OpenAI pivot prover, coordinated by the healing lead).
All retain `ResetPremises`, `Catch(2Δ)`, the ready proposal, and the existing drain.
They are proof obligations, not additional protocol premises.

| Declaration (`Consensus.Goldilocks.Healing.` prefix) | Consumer obligation | Dependencies / proof status |
|---|---|---|
| `proposal_stored_locks_compatible_old` | Proposal stored high locks compatible with each `OldSrc` | OPEN fast/actual-slow source proposal support and frozen-domain viability |
| `proposal_start_supported` | Proposal start below the actual honest vote head, under earlier-votes=P | OPEN source HEAD support; first slow HEAD uses proved `SA.slow_first_votes_before` with explicit carry, merged, frame and stored producers |
| `vote_old_live_lock_below_parent` | Viable ancestor of each non-current live read-point lock below the proposal parent | OPEN source proposal support from label l+2, bounded retention and move-back provenance |

The deepest set remains `{start} ∪ OldSrc`; floor/root and same-slot optimistic
arguments are unchanged. The unused `hnoSlow`, `late_slow_lock_votes`,
`clean_slowLock_false`, and vacuous `clean_slow_transfer` route is retired.
The §67 raw-boundary/slow-exclusion plan is superseded, not a proof dependency.
No threshold/drain change or new upper bound on k is made. Source producers must
retain bounded `SA.Inv`, global `Anc U B fcRoot`, exact window cutoffs, receiver
F≤source and per-counted-vote writer evidence; they cannot assume these consumers.

## Approved conditional Sleepy supplier skeleton

`Lemmas/Refinement/NonfinalSuppliers.lean` contains the lead-reviewed Sleepy
signature slices. It imports AcceptanceDefs for its existing coefficients and
now feeds the Sleepy liveness endpoint; it does not enter Main/Solution. All names below are in
`Consensus.Goldilocks.Refinement`. No Healthy premise or endpoint duration changes.

| Named obligation | Status and exact remaining work |
|---|---|
| `confirmed_duration_supply` | OPEN: joint coefficient bound `18Δp ≤ cDur`, also for Healthy queries; positivity alone does not prove it. |
| `sleepy_query_sync` | OPEN: actual canonical finite service through the exact engine deadline. |
| `sleepy_query_population` | OPEN: population transport at slot points `{0,Δp,2Δp}` bounded by that deadline. |
| `sleepy_query_producer` | OPEN transitively; assembly body now uses the separate slot and event leaves below, then proved own-proposal acceptance. |
| `sleepy_query_slot` | OPEN: recurrence/grid selects a positive slot with strict freshness, `6Δp` service margin and exact-cDur-ready selected proposer. Readiness at `18Δp` cannot be upgraded. |
| `confirmed_slot_event` | OPEN: joined/eligible state and an actual scheduled canonical engine event within the horizon. Eligibility is not event existence; any duration bridge retains the coefficient dependency. |
| imported `sleepy_include_finite` | OPEN: finite inclusion from the explicit service/population premises and `6Δp` margin. |

These six named supplier obligations contain **five direct sorries**, because
`sleepy_query_producer` is an assembly, not an additional leaf.
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
| `healthy_old_inventory_initialize` | OPEN OldHonest initialization (healing §§27/28): selects explicit record/cache/expiry/service timing and establishes coverage-or-below-hj for the global signed-entry inventory, including entries arriving later. |
| `healthy_old_row_realize` | OPEN first-arrival/self-entry join: the exact old-source antecedent identifies E with root a.T and the receiver's replay height; E is not the source D, and no extra ToFGAt D is assumed. |
| `healthy_prepare` | OPEN record/cache/stored-lock preparation at cutMap(endCut heal), consuming inventory initialization and progress only on `[ready, heal]`. |
| `healthy_preserve` | OPEN preservation at every later canonical cut through engine end, including same-time intermediate states, under health without later progress. No timestamp bound on the boundary cut is asserted. |
| `healthy_vote_row_replacement` | OPEN eventual-coverage-to-label-bounded replacement matching BaseFacts: replacement label ≤ predecessor slot, not OriginBefore or a newly assumed causal source. |

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

| Named leaf | OPEN obligation |
|---|---|
| `healthy_cut_agreement` | Actual engine-cut agreement from Healthy state facts, including equality-time cuts before endCut(heal). Receives h0/hb and actual finite ready→heal progress; post-endCut facts alone are not that transport. |
| `healthy_cut_monotone` | Temporal prefix extension at arbitrary ordered engine cuts with both exact-cDur readiness tests; same-time/pre-endCut transport remains owed. |
| `outage_pre_service` | Canonical service through recipient deadlines ≤ outage start, not unrestricted late-wake service. |
| `outage_arm` | Effective-record arming at original endCut(T), including inherited records and lookup-none/frame.F fallback; frame membership and original read-prefix witness. |
| `outage_repair` | R.5 continuation, lifetime, old output/record compatibility, first arrivals and actual repair for the exact two resilience-reader windows. |

`healthy_ready_safety` consumes initialization→preparation→preservation and the
two cut adapters. Its Accepted wrapper handles an empty validator type and heal
beyond the horizon without strengthening premises or shrinking InCuts.
`outage_reader_windows` is only the definitional split of ResilienceReader,
retaining exact engine cDur; it does not establish node readiness or service.
`outage_protected` assembles finite pre-service, arming and repair with unchanged
ProtectedThrough quantifiers. The five leaf signatures were approved as OPEN.
Existing Healthy leaves and coefficient witnesses remain transitive gaps.
Full proof completion, frozen-service/source/vote joins and other Accepted
adapters remain OPEN; none are supplied by successful elaboration of this wiring.

## What the master inventory does not certify

The complete compiled leaf list does not discharge any OPEN supplier or promise
that joint leaves already expose every internal mathematical step. Healthy frozen
service, producer budgets, old-entry production and outage repair still need proofs
and may require further named subleaves. Signature approval and mapped reachability
are not proof completion or a Main/Solution certificate.
