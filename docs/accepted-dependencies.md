# Accepted proof dependencies

This is the integration ledger for the complete Goldilocks `Accepted` skeleton.
It is **incomplete**: a row describing a planned contract is not an elaborated Lean
statement. No proof work should start on an OPEN architecture join merely because
the downstream theorem compiles with `sorry`.

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

Current status: **NOT MET**. The proposer-free family is committed on
`work/amp/family-wip`; its frozen core passed the fast gate after snapshot refresh.
Provenance and finite sleepy interfaces are integrated, but their proofs remain OPEN.
Healing supplier types remain a separate draft outside the library. This is a partial
inventory, not evidence that the Accepted skeleton is complete.

## Ownership and architecture

The spec orb owns this table and integrates rows sent by other owners. Owners edit
their assigned Lean modules, not this table concurrently.

| Area | Owner | Placement/status |
|---|---|---|
| Family, finite adapters, integration | Spec orb | family-repair worktree; OPEN |
| Finite sleepy transport | Healing box | Lemmas/Refinement/Sleepy; nine OPEN leaves, two supplier definitions |
| Healing/R.3/R.4/R.5 | Healing paper orb and T3 | exact supplier declarations pending finite adapters |
| Always fields | Healing box | Lemmas/Refinement/Evidence and Transport |
| Simulation/provenance, scheduled proposal | R.6 box | Provenance and Steps |
| Network/publication | Engine thread | new Lemmas/Refinement/Forwarding and NetworkTransport |

Replay order uses only validator count and genesis root. The local family repair
indexes it by those values so run-selected proposer parameters preserve the actual
restart order. Credentials supplies ideal selection validity; receivers check role
syntax, not a preconfigured proposer schedule. Selection gates duty execution before
mutation. The protocol timing target is Δp = Δe + 1, with delivery-time relay.

Publication is not implemented by the existing unsigned relay: the revised publisher
needs an accepted-block-to-own-wrapper map and parent-first same-event draining of
all fresh wrappers, including own proposals. Successful releases require actual
event/candidate-prefix indices, not a fabricated timestamp order. Shape parsing is
not acceptance provenance. In the current family, `processOne` queues the raw
canonical object `o` through `relayIf`, and `goldilocksShape.gossip` emits `.relay`;
neither constructs `forwardObj` at acceptance. The `forwardObj`/`decodeForward`
format and dependency policy from #116 therefore do not establish fresh-wrapper
acceptance provenance. The concrete publisher adapter remains OPEN independently
of parser correctness.

`NoCollTransport` currently quantifies arbitrary `Simulates` traces. Caller audit
found no consumer needing that generality: the concrete accountability and read
bridges use `simTrace`. The intended repair is canonical-only transport, retaining
the weaker `Simulates` interface. **OPEN boundary repair:** the trusted statement
cannot import the current Lemmas-owned canonical construction; expose that
construction at an allowed definition boundary before changing the statement.
Tagged genesis roots alone do not establish source coverage of all occurrences.

## Always-field leaves

All names below have prefix `Consensus.Goldilocks.Refinement.`; all are existing
Lean sorries, owned by the Healing box. Exact statements live in
`Lemmas/Refinement/Evidence.lean` and `Transport.lean`. Paper locations are
`goldilocks-claims.tex` at `4ea71d05`, R.7/R.8/F.2/F.3/G1.5, and
`shared/composition.tex` §Blocks/§Model, as mapped in `goldilocks-mapping.md`.
Arguments are implementation derivations, not quotations. “Argument supplied”
does not mean its dependencies are proved.

| Declaration | Statement and dependencies | Paper argument/status |
|---|---|---|
| `held_in_view` | Valid run, honest reader, non-genesis block held at mapped cut ⇒ canonical object in indexed view; tree_cases, accepted_in_view | F.2/G1.5: obtain earlier acceptance and its source event, including equal-time events. Argument supplied relative to simulation. |
| `held_att_in_view` | Any held block's payload attestation is in reader view; held_in_view, payloadObjs, transitive containment | Genesis payload empty; canonical block carries each attestation. Argument supplied. |
| `evidenceInView` | Finalized header payload attestations occur in reader view; simulation, finalized read, cache/chain and decode bridges | G1.5(b): identify held block, round-trip payload, apply held evidence. Argument supplied. |
| `engine_outputValid` | ExecutionValid ⇒ every output valid; local coherence, chainTo, held_in_view | R.8/F.2: slot induction, linkage, strict parent slots, canonical provenance; no collision escape. Argument supplied; recheck after tagging. |
| `engine_nested` | ExecutionValid ⇒ finalized nested in confirmed; simulation, outputs_nested | R.8/C0.1 at actual shape clock; empty validator type vacuous. Argument supplied. |
| `engine_finalMonotone` | ExecutionValid ⇒ finalized monotone; simulation, finalized_monotone | R.8/C0.2: ordered mapped cuts and preserved store ancestry give prefix. Argument supplied. |
| `noCollTransport` | No collision plus PROVIDED GenesisFresh ⇒ NoCollRun; currently arbitrary simulating trace | F.3: observed header injectivity and genesis separation. OPEN all-occurrences source coverage and canonical-only signature repair; raw freshness is not an Accepted premise. |
| `compatible_reads` | Canonical NoCollRun, honest bounded reads and compatible node tips ⇒ compatible engine chains | R.7/F.3: coherent union identifies cross-store parent walks. Argument supplied; walk lemma unformalized. |
| `convicted_count` | Finite key set with slashable canonical witnesses in A ⇒ cardinality ≤ convicted(A) | G1.5: injective rho.key image is contained in convicted. No honesty/collision premise. Argument supplied. |
| `final_accountable_of_noColl` | Canonical NoCollRun and valid honest bounded reads ⇒ compatible or ≥2q−n convicted | R.7/G1.3–G1.5: node witnesses, held payload evidence, inject keys. Argument supplied relative to bridges. |
| `finalizedAccountable` | FinalizedAccountable, retaining provided freshness/no-collision | Compose canonical simulation, collision transport, prior row. OPEN transitively; does not derive freshness. |
| `shape_outputValid` | HoldsAlways output validity for every schema lookup | R.8: unfold valid runs and apply engine_outputValid. Argument supplied. |
| `shape_nested` | Increasing schema ranks ⇒ HoldsAlways Nested | R.8: finalized/confirmed bridge or confirmed reflexivity. Argument supplied. |
| `shape_finalMonotone` | Final schema lookup ⇒ HoldsAlways monotonicity | R.8: lookup identifies finalized. Argument supplied. |
| `shape_finalAccountable` | Contract α≤1/3 ⇒ accountable safety, NO freshness premise | R.7: collision escape or convicted bound; 2q−n≥n/3. OPEN freshness-free encoding and source transport, not arithmetic. |

## Provenance leaves

Owner: R.6 box. Exact statements integrated in Provenance and Steps; all remain sorries.
Names have the same refinement prefix. No simTrace signing correspondence may
be used upstream of selected-duty/node agreement.

| Declaration | Dependencies / argument | Status |
|---|---|---|
| `engine_event_signing_history` | Actual store reachability, entry bounds, selected poll transitions, restart record; joint event/duty induction | OPEN implementation proof |
| `engine_signing_history` | Event history and duty-prefix history | OPEN implementation proof |
| `engine_restart_record` | Durable and restore definitions | OPEN implementation proof |
| `engine_signings_nonFraming` | Signing history, G0.5/FG.client_safety | Argument route supplied; upstream OPEN |
| `engine_seen_att_signed` | Credentials, actual poll release→queued-sign inverse, same-event prefixes | OPEN implementation proof |
| `engine_att_protected` | Nonframing, seen inverse, conflicts encoding; G0.5 corollary | Upstream implementation bridge OPEN |
| `scheduled_proposal_releasable` | Actual EngineProposalAt, selected slot-start, pool/att provenance, drain/guard | OPEN implementation proof |

## Finite sleepy transport leaves

Owner: Healing box, integrated by the spec orb. Exact declarations are in
`Lemmas/Refinement/Sleepy.lean`, namespace `Consensus.Goldilocks.Refinement`.
All use canonical `simTrace` and, where needed, `runProposer S rho hn`.
There are nine OPEN theorem leaves and two supplier definitions, not proved suppliers.
Here Δp is the node parameter, c = catchUp = 18Δp, and b≤horizon.

| Declaration | Contract and dependencies | Status |
|---|---|---|
| `sleepy_ready` | Valid run, 0≤t≤horizon and engine Ready c at t ⇒ node ReadyAt; canonical awake/key equivalence | OPEN implementation bridge |
| `sleepy_faultBound` | SleepyOn(1/2,c,0,b) ⇒ node FaultBound at ts(s)+d≤b for d∈{0,Δp,2Δp}; ready-implies-joined and key counts | OPEN implementation bridge |
| `SleepyServiceSupplier` | SyncUntil b ⇒ node SyncBefore H Δp b on valid runs with 0≤b≤horizon | Definition only; strict deadline slack and acceptance relay OPEN; repaired window may differ |
| `sleepy_read_cut` | Ready reader at 0≤t≤horizon ⇒ CutAfter and Boundary at cutMap(endCut t), with output clock t; terminal filler included | OPEN event/clock bridge |
| `sleepy_safe_finite` | Valid run, canonical NoCollRun, SyncBefore through b and bounded slot quorum ⇒ ReadySafeOn 0 b | OPEN finite R.1 localization |
| `sleepy_include_finite` | Same finite premises, ready proposal at 0≤τ≤b, τ+6Δp≤t≤b, ready reader and CutAfter at t ⇒ proposal ancestry of read | OPEN finite R.2 localization |
| `sleepy_grow_finite` | Same service/quorum/noColl, t≥0, k≥1, b=t+(4k+6)Δp, selected-schedule recurrence and ready reader at b ⇒ fresh proposal after t included in ready b reads, excluded from ready t reads, with read extension | OPEN finite R.2; depends on inclusion/safety |
| `SleepyRecurrenceSupplier` | Engine single-pattern recurrence on family grid ⇒ node recurrence for runProposer, same c and [0,b] | Definition only; grid/duration adapter OPEN |
| `sleepy_proposal` | Valid run and ready node proposal at 0≤τ≤horizon ⇒ ready key and engine HonestProposal of encoded header | OPEN canonical release/key bridge |
| `sleepy_inBy` | Valid run, NoCollRun, ready proposal and node inclusion at all ready CutAfter t reads, 0≤τ≤t≤horizon ⇒ engine InBy confirmed | OPEN structural consumer; read_cut and chain transport |
| `sleepy_safe_engine` | Valid run, NoCollRun, SyncBefore/quorum through horizon ⇒ engine ReadySafe confirmed | OPEN arbitrary-cut clock/compatibility transport; endCut alone insufficient |

R.1/R.2 motivate these reductions, but do not prove the engine bridges. Existing
SleepySafePrefix requires SyncRun with receiver obligations beyond b; IncludeSleepy
and GrowSleepy require whole-run SleepyRun. Neither supplies these finite consumers
directly. No unconditional Accepted endpoint is asserted. Timing/grid/catch-up/latency
scaling, finite locality, arbitrary-cut clocks and canonical collision encoding remain OPEN.

## Publication and network leaves

Owner: engine thread. Planned exact declarations in the two new refinement lemma
modules; not yet integrated. All implementation obligations explicitly **OPEN**.

| Planned declaration | Required statement |
|---|---|
| `forwarding_origin` | Actual successful honest-origin wrapper release ⇒ actual acceptance at claimed stamp before release prefix |
| `forwarding_at_acceptance` | Actual honest acceptance ⇒ successful matching wrapper release in same event |
| `forwarding_parent_earlier` | Child release ⇒ exact same-origin parent release earlier in actual release order and strictly earlier parent acceptance cut |
| `forwarding_held_processed` | Pre-delivery held wrapper ⇒ earlier canonical processing at time≥stamp, or receiver's own actual acceptance |
| `accepted_objects_seen` | At publication prefix, carried block/parent wrapper are held and release/dependency/protection guards pass |
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

## Still missing from this inventory

Exact top-level Accepted assembly, remaining finite adapter types,
outage/final leaves, and a mechanical comparison against every reachable sorry.
The ledger is not a completion certificate until those are present and the gate runs.
