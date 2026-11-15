# Claim reduction interfaces: complete statement row

These are conditional statement interfaces, not completed suppliers or proofs.
Their concrete realizations and the reduction proofs remain separate obligations.

## Fixed outage policy

L9 now lives only in `OutageReadPoint.protection`. The actual-cut twin is deleted.
The local data fix threshold, catch-up, recovery, both independent look-aheads,
η, arming lag and budget. `OutageRecoveryBinding` matches all eight to the contract
by equality. `RunMap.delta_eq` fixes `P.Δ = E.ΔAC` in every covered environment.
The participation catch-up is derived as `max cDur (η·ΔAC − 1)`.
Reads remain non-strict. Certificate: cert obligation open: OC-K.

`ACServiceBefore` uses recipient-deadline cutoffs and the AC-owned `served` predicate.
Fresh delivery implies `served`; Goldilocks interprets it as fresh processing or
stamped retained evidence (`SA.MessageServedBefore`). Only message service and node
acceptance relay are required. Growing AC relay follows the `acBlock_prev`/`accept_next`
derivation in `Growing/Compose/Sync`. Instance interpretations remain pending.
The unused `ServiceTransport` is deleted; generic `Service` is unchanged.

## Guarded-window forward adaptation

The original height interface omitted the concrete delivery-spacing prerequisite and
quantified over arbitrary qualifying windows. The correction instead makes
FinalHeightSupply pointwise evidence for one W and makes FinalWindowSupply jointly
select W at the original query/deadline with
`6 * P.Δ + E.ΔFG ≤ 4 * P.Δ * (W.gap : Time)`, HealedFrom, healing.Run and those heights.
HealthyLivenessReduction therefore removes its independent FinalHeightSupply premise.
It consumes the acceptance, ancestry and three own-reader height projections returned
for that SAME W; FinalReadTransport.cache retains its exact
inputs, and DeadlinePremisesSupply independently produces Premises at E.ΔFG.
No arbitrary-window height law, timeoutDelay-to-spacing inference, gap enlargement or
latency enlargement is claimed. Joint guarded production remains OPEN; this fixes a
missing source prerequisite, not a valid-run counterexample, and supplies no proof.

## Verdict and ownership

The conditional reductions and the local-supplier capstone are STATED: six regime reductions,
the output-validity HoldsAlways wrapper, and `meetsObligations_of_local`.
Existing CHAIN-REP nesting and
final-monotonicity edges are reused, not duplicated. Every new edge is an admission-free
Prop definition, not a theorem. Compilation establishes well-formedness only: it does
not establish truth, sufficient premises, realizability, or nonvacuity.

Supplier interfaces below remain **UNPROVED**. Named source routes do not constitute
generic adapter proofs. Joint proposal and final-window production now take the
collision-free branch of the consuming `Holds` reductions. No guarded supplier is
an input of `OutputValidAlways` or the unconditional chain-representation edges.
The selected final window carries anchor-0 advertised readiness/non-genesis and
anchor-3 honest proposal evidence. Processing requires Healthy service and readiness
at the deadline, not readiness at an arbitrary later time.

The weak proposal-budget twins, cut-only carrier/cache twins, universal
`FinalProposerTransport` and separate `ActualResetSupply` are removed together with
their reduction and capstone inputs. `ProposalWitnessRefinement`, `FinalReadTransport`
and `ResetHealBudgetSupply` own those witnesses. The older inventory below describes
the source gaps; removed names there are historical comparisons, not live inputs.

L-CORR owns these generic signatures and their premise accounting. Each instance owns
its realization, including the lead instance downstream in dc D-INST/W10. The stored
read-context data has no default implementation. No interface is inferred from similar
dc predicate names. No source-realization or automatic arbitrary-AC generalization is claimed.

## Declaration inventory

Paths below are relative to `ConsensusLean/Instances/Goldilocks/`.

| Booked item | Declaration in `Lemmas/Generic/ClaimReductionEdges.lean` | Original telescope |
| --- | --- | --- |
| outputValid wrapper | `OutputValidAlways` | Growing/Obligations/Concrete/Fields:43–44 |
| finalAccountable | `FinalAccountabilityReduction` | Fields:68–70 |
| healthyLive | `HealthyLivenessReduction` | Fields:193–199; confirmed:167–174; Concrete/Final:325 |
| sleepySafe | `SleepySafetyReduction`, with `D : SleepyLayer1.Data A` | Fields:76–79 |
| sleepyLive | `SleepyLivenessReduction`, with `D : SleepyLayer1.Data A` | Fields:206–212 |
| healedSafe | `HealedSafetyReduction` | Fields:114–122 |
| persists | `PersistenceReduction` | Fields:150–153 |
| local-supplier assembly | `meetsObligations_of_local` in `CorrectnessEdges.lean`, with public-indexed `events : SleepyLayer1.Data` | Concrete/Endpoint:21–32 |

The conclusion telescopes preserve the original capability tests, all progress forms,
ready→horizon versus ready→heal intervals, ready-reader conditionality, HoldsAlways
versus Holds, and the original hash-collision excuse. No NoColl or constant-fault
premise is added to an unconditional claim. The capstone consumes one `LocalClaimSuppliers`
record per mapped valid run, not endpoint claims or reduction propositions. Its intended proof
composes the reductions. Admissibility, service, progress-fit, progress-tolerance and
`HealthyBetaFit` and `CommitteeHalfFit` remain separate inputs. The stored-read context and outage policy remain
explicit data families. No proof of the capstone is supplied.

Each reduction fixes one public-indexed EngineBinding B and uses exactly M = B.map E hE rho hv.
Local contracts C, outage policy D and stored-read context R are indexed by that M;
no fresh run, changed map, replacement proposal or unrestricted Prop callback is used.
Here the capstone's `D` denotes outage policy; the two sleepy reductions' `D`
denotes event data, passed as `events` by the capstone.
The capstone's AC families are indexed by public parameters with a positive population;
`shapeClaimsAt_of_isEmpty` proves every empty-population claim directly from its quantifiers.
The two public-restriction recovery lemmas preserve the unconditional and excused wrappers
separately. The final obligations still quantify over every finite validator type.

Final-cache and population-accountability contracts take the committee-indexed AC run as
their single source of requirements and genesis-root validity. `run_requirements` supplies
requirements at the actual committee starts, not at the default initial state; `run_root`
supplies genesis validity for the run's digest. These rows therefore take neither a separate
`A.Requirements` premise nor a genesis `RootOk` premise. Per-block root-validity hypotheses
in the engine representation remain independent and unchanged.

## New interface rows and source limitations

### Sleepy event and coverage suppliers

The reductions and `LocalClaimSuppliers` consume the following rows. All are OPEN
proof obligations, not final endpoint claims. The un-windowed sleepy fields of
`ACCorrectLocal`, `FiniteLocal` and `SleepyReadPoint` are removed: proposal and
inclusion now take the same run, binding, service, independent count windows and
anchored-frame premises as `Extension`.

| Input | Source and remaining obligation |
| --- | --- |
| `SleepyLayer1.EventSafety` | Concrete `GoldilocksEventSafety` and the existing sleepy invariant; actual composed-run frames only. Instance discharge remains OPEN. |
| `SleepyLayer1.OutputProvenance` | Actual-read output provenance; held membership plus ancestry to an event or frame floor. Held membership overlaps `LocalReadPoint.held` deliberately so the standalone generic `ReadAgreement` Prop target has a coherent genesis-root case without importing the unrelated payload fields. |
| `SleepyLayer1.Extension` | Same-reader ancestry at ordered cuts and evaluation times; not inferred from compatibility. Concrete discharge remains OPEN. |
| `SleepyLayer1.SourceProvenance` | Report source is an ancestor of a same-reporter confirmation event at an earlier or equal cut. The source need not equal the event block. |
| `PopulationQuorumSupply` | Shared FG requires `2 * (H t)ᶜ.ncard < P.n`; arbitrary admissible thresholds do not supply it. `Simulation.GoldilocksPopulationQuorumSupply` states the canonical-map discharge with explicit `1/2 ≤ K.params.θ`. It uses the population clause, independently of committee counts; proof OPEN. |
| `SleepyWindowSupply` | `Simulation.GoldilocksSleepyWindowSupply` states the canonical-map discharge with explicit threshold and two independent look-ahead equalities. One mapped point supplies both regimes; proof OPEN. Catch-up domination comes only from `ClaimDeadlineFit.catchUp`. Sleepy claims do not consume outage policy; neither regime interface depends on the other. |
| `SleepyLayer1.ProposalCoverage` | `GoldilocksProposalCoverage` states the concrete conditional head. Source routes: `sleepy_serviced_proposal_coverage_at` / `include_sleepy_at`, with committee facts and bounds supplied on the engine route by `sleepy_committee_at`. Both windows and anchored frames are explicit, hold is at least Δ and margin at least 6Δ; the hold must survive the horizon. Proof and local-data matching remain OPEN. Payload inclusion follows from this ancestry and `LocalReadPoint.payload`, with the ready read's honest-read projection; no separate inclusion supplier remains. |

The generic FG rows (`CacheProvenance`, `RowProvenance`, `ConditionalViability`)
and glue rows (`FramesFromSources`, `ReadAgreement`, `ReadyReadSafety`) remain
separate proof targets. Count transport never substitutes one look-ahead for the other.
`CommitteeTransport`, `PopulationTransport` and `FrameAcceptance` are separate
generic adapter targets; naming their sources does not discharge them.

**OPEN instance fit: slot constancy.** `GoldilocksWindowPremises` requires
`cm (sp.ts s + sp.Δ) = cm (sp.ts s)` at every slot. Generic `EventSafety`,
`Extension` and coverage contracts do not imply this for arbitrary committees.
Its source must be a property of the selected-committee RunMap together with the
concrete run interface, reviewed with the instance discharge; it is not added as
an unconditional generic law. `Simulation.GoldilocksSlotConstancy` states that
exact canonical-map obligation; its proof remains OPEN.
The separate committee-facts source is the committee-valid run interface, which
lands separately. Bare abstract collision freedom is not its proof, and the
canonical run transport in this tree does not yet carry that conjunct.

### Engine and regime suppliers

Every row is in `Milestones/Statements/Generic/ClaimTransports.lean` and remains OPEN.
Concrete source paths below are under `Lemmas/` unless otherwise stated.

| Interface | Source / exact consumer | Unresolved scope |
| --- | --- | --- |
| `ClaimDeadlineFit` | Concrete/Fields sleepySafe catch-up arithmetic; ReadPoint healthy proposal/healed; Accountable population threshold | Local catch-up ≤ engine cDur, local latency ≤ publication margin, max GST 0 + margin ≤ advertised nonfinal heal, α·n ≤ 2q−n, healthy population bound < 2q−n. These are arbitrary-contract numerical targets, not consequences of CorrectLocal. Nonnegative durations already come from C.durations. |
| `AdmissibleProposal` | confirmed_payload_projection_at; ProposalLiveReady's proposer readiness | Actual B,k must be non-genesis, nonnegative, hold through horizon and engine-cDur ready. The old ReadyProposal only gives local catch-up and honesty through hold. |
| `ProposalWitnessRefinement` | Concrete/Fields sleepyLive and healthyLive_confirmed | Selects the same query/progress/deadline witness jointly with AdmissibleProposal on the collision-free branch. No InBy or ProposalLiveReady conclusion is assumed; the weaker budget twins are deleted. |
| `EndReadTransport` | Growing/Simulation/Endpoint/Outputs.prefix_reader_at; confirmed_payload_projection_at; outage actual-time reads | `ready`/`boundary` are at claim time t; `output` evaluates at M.clock of the state at endCut t. No clock equality or next-micro-cut honesty is asserted. Readiness at t → a ready read point at the stored clock is a NEW UNRESOLVED target, not supplied by these fields. |
| stored-clock read point (MISSING) | Growing/Sleepy/Engine/ReadPoint.engine_read_point; Obligations/Sleepy.ready_at_stored_now, stored_now_ge_cutTime_sub_one, now_mono | A bridge at M.clock must use a source cut such as R.cut, not re-time M.cut i. Engine readiness c+1 must yield local readiness c at that stored-clock read point, with its boundary and output correspondence. Integration statement item: strengthen ClaimDeadlineFit.catchUp to C.catchUp + 1 ≤ cDur and state this bridge for review; neither change is implemented here. Sleepy safety/liveness, healthy nonfinal liveness, persistence and cross-reader healed safety remain unclosed until their stored-clock uses are discharged. |
| `DeadlinePremisesSupply` | Generic/Obligations.Premises; concrete final query production | Produces the exact Premises at query + final-latency·ΔAC, only under actual final progress, healthy regime, heal≤query, deadline≤horizon and a ready deadline reader. FinalWindowSupply alone does not produce this bundle. |
| `FinalWindowSupply` | Concrete/Final final payload projection | Selects the same W with anchor-0 non-genesis and advertised readiness, anchor-3 honest proposal, spacing and heights. The universal FinalProposerTransport twin is deleted. |
| `FinalReadTransport.processed` | concrete carrier-processing supply / final payload projection | Healthy service and deadline readiness produce strict-earlier BlockCallAt via CarrierProcessed, preserving own processing honesty. The cut-only carrier twin is deleted. |
| `FinalReadTransport.cache` | actual-reader cache coverage | Retains Premises, same W, acceptance, ancestry, all three height steps, carrier processing and population threshold at t. The cut-only cache twin is deleted; actual-read realization remains OPEN. |
| `ActualReadAccountability` | Growing/Simulation/Endpoint/Accountable.finalAccountable_readPoint | Keeps both own-read honesty times, bounded read points, local run/no-collision, original 2q−n population cardinality and ChainAtts witnesses. Requirements and genesis validity come from the actual run; no separate default-start Requirements input remains. |
| `HighCanonicalSupply` | Generic/Obligations.HighCanonical and ACHealing.heal_after_reset source prerequisites | Same run, horizon, reset and Premises; never derived by applying heal_after_reset itself. |
| `PreparationPremisesSupply` | Healthy/PreparationReset and Generic/Obligations.Premises | Exact nonfinal healthy-preparation progress interval and horizon. Final-only DeadlinePremisesSupply does not supply this. |
| `ResetHealBudgetSupply` | Healthy/PreparationInitialize.healthy_preparation_initialize_late_at:30 | Selects an actual reset a with max GST 0 ≤ slotTime(slotOf a + drain), and that slot time + margin ≤ advertised heal. Does not claim every reset is early. No unbudgeted healed slot. |
| `OutageServiceSupply` | Outage/Engine/Query.outage_pre_service_at, outage_psync_at | Supplies `ACServiceBefore` through b₀ and post-outage GST. AC-owned message service includes fresh and retained evidence; node acceptance relay remains explicit. Instance transport is pending. |
| `ResilienceTipTransport` | Concrete/Fields.persists; Outage/Engine/Repair.outage_protected_at:29 | Schema/capability target tip is confirmed at actual t. This is representation, not protected-read ancestry. |
| `StoredReadContext` / `StoredReadTransport` | Healthy/CutTips.healthy_cut_tips_ancestor_at:77 at E1 498dd8b5 | Concrete source is readAfter at cutMap(lastOwn …), stateAt.now. Goldilocks: `goldilocksStoredReadContext`, `goldilocksRunMap_storedReadTransport`; no implementation for an arbitrary AC. source_tip/current_tip explicitly request its correspondence to confirmedRead; now_bound retains the later stored-clock horizon bound. No clock equality or direct arbitrary-AC realization is claimed. |
| `HealedReadAncestry` | same healthy_cut_tips_ancestor_at | Translates HealthyPreparationQueryAt's fields into the same M's valid/clean run, nonfinal capability, Healthy, actual ready→heal progress, nonnegative/bounded heal, ordered engine cuts, BOTH ready reads and later stored-now≤horizon. Conclusion stays LOCAL BLOCK ANCESTRY between R.tip values; StoredReadTransport separately identifies the current reads. |

## Field-by-field premise discharge map

“Supplied” below means a named OPEN hypothesis of the intended edge, not proved evidence.

| Consumer premise | Named interface / derivation | Status |
| --- | --- | --- |
| growing local run, no collision | GrowingRunTransport.run/no_collision | Existing OPEN supplier; collision excuse is split only in Holds rows |
| engine/local Δ identity | M.delta_eq | Map data, realization OPEN |
| bounded own-read honesty, read boundary | EngineReadPoint.honest/boundary, RegimeTransport.ready + EngineReadPoint.ready | EngineReadPoint supplied for Goldilocks (`goldilocksRunMap_engineReadPoint`); OPEN for an arbitrary map; RegimeTransport.ready stays OPEN; actual engine cutTime retained |
| end-time readiness and output state/time | EndReadTransport.ready/boundary/output | ready/boundary at t, output at M.clock of state at endCut t; readiness at t → stored-clock ready read point is MISSING, with no next-cut honesty or clock equality |
| local versus engine catch-up, latency/heal | ClaimDeadlineFit.catchUp/latency_le_margin/healthy_start | NEW OPEN numerical targets; current catchUp only states C.catchUp ≤ cDur. Stored-clock bridge requires the proposed C.catchUp + 1 ≤ cDur strengthening on the integration head |
| nonnegative durations | ACCorrectLocal.durations | Existing local data; no extra numerical supplier |
| proposal hold through horizon and proposer cDur | ProposalWitnessRefinement → AdmissibleProposal; FinalWindowSupply for anchor 0 | OPEN targets; same jointly selected witnesses |
| sleepy finite service and independent count windows | RegimeTransport.sleepy → SleepyPrefixAt; SleepyWindowSupply → CommitteeWindow and PopulationWindow | OPEN suppliers with separate population/committee look-aheads; the prefix alone supplies neither window; no finite⇒unbounded inference |
| healthy finite service/awake/cardinal bounds | RegimeTransport.healthy plus bounded nonnegative horizon → HealthyPrefix | Existing OPEN supplier + engine bound arithmetic |
| accountable fraction and final population threshold | ClaimDeadlineFit.accountable/final_faults | NEW OPEN numerical targets |
| all progress forms and matching query budget | ProposalWitnessRefinement, ResetProgressSupply, FinalWindowSupply | All OPEN, no single-pattern-only exclusion |
| final four anchors / delivery spacing / three height steps | FinalWindowSupply jointly selects SAME W, guard at E.ΔFG and pointwise FinalHeightSupply evidence | Corrected OPEN production target; no independent arbitrary-window height supplier, no constant FrameWindow manufacture |
| actual final carrier processing | FinalReadTransport.processed | OPEN actual-read target; strict processing witness retained |
| actual-read final cache ancestry | FinalReadTransport.cache | OPEN target; no cut-clock cache twin |
| final deadline Premises | DeadlinePremisesSupply | NEW OPEN target, not FinalWindowSupply |
| preparation horizon Premises | PreparationPremisesSupply | NEW OPEN target; consumed before healing, not proved by healing |
| reset / canonicality / drain-slot time | HighCanonicalSupply and ResetHealBudgetSupply | OPEN targets; the budget supplier selects the reset, and heal_after_reset only consumes it |
| healed temporal ancestry | HealedReadAncestry + StoredReadTransport | NEW OPEN local ancestry and separate mapping, not compatibility⇒ancestry |
| outage participation | OutageTransport.participation and OutagePolicy.binding/horizon | Existing OPEN suppliers; at the run's own point and selection the population and look-back committee η-sleepy clauses (outage catch-up `max cDur (η·ΔAC − 1)`) follow from `Outage` (`OutageTransport.participation_of_outage`). The destination coupling (sample coverage) is removed: unsatisfiable under growing faults |
| fixed outage recovery floor / endpoint fit | ACCorrectLocal policy data and OutageRecoveryBinding's eight equalities at SAME M/K/C | OPEN exact-policy matching; protection lives only in OutageReadPoint, with no actual-cut twin |
| outage pre/post service | OutageServiceSupply | OPEN exact implication; AC-owned service and node acceptance relay require instance transport |
| resilience target tip | ResilienceTipTransport | NEW OPEN representation only |
| RootOk at actual reads | HonestReadTransport.roots; genesis from the run (`ACRun.run_root`) | supplied for Goldilocks (`goldilocksRunMap_honestReadTransport`); OPEN for an arbitrary map; never inferred from unrelated dc names |
| honest union coherence | explicit clean-run → Coherent hypothesis | OPEN instance supplier, never added to HoldsAlways |
| held-store inclusion in honest union | HonestBlocksAt witnesses y=validator.symm v, cut=M.cut i, t=cutTime i, using before_time/honest_eq and nonnegative actual cutTime | DERIVED, not a new supplier |
| chain prefix from local ancestry | ReadRepresentation.ancestor_prefix, with actual held membership/root/coherence premises; same M.chain/header | supplied for Goldilocks (`goldilocksRunMap_readRepresentation`); OPEN for an arbitrary map; no final claim assumed |
| actual tip held / payload ancestry | OutputValidityEdge; LocalReadPoint, SleepyLayer1 coverage and HealthyReadPoint; final cache invariants | OPEN: OutputValidityEdge needs the honest reader's output tip at M.clock of its stored state to belong to the mapped FG tree. Neither ReadRepresentation nor HonestReadTransport supplies this membership. For Goldilocks, finalized membership follows from FG reachability and confirmed membership from AC ReqOutputs. |
| engine view and conviction binding | HonestReadTransport.chain_att_view, M.att_signer/att_conflict; key/validator equivalences | supplied for Goldilocks (`goldilocksRunMap_honestReadTransport`); OPEN for an arbitrary map; source population count unchanged |

### Premises production: no silently discharged field

For both DeadlinePremisesSupply and PreparationPremisesSupply the exact returned
record is Generic.Premises, not an arbitrary predicate. Its fields are individually
OPEN obligations of the instance realization:

| Premises field | Required source accounting |
| --- | --- |
| noColl | GrowingRunTransport.no_collision at same M |
| sync | Service at the consuming deadline, including strict signedRow processing; GSTRunAt alone is not this record |
| awake | finite healthy awake bound at the same deadline/horizon |
| faults | finite healthy cardinal bound at the same deadline/horizon |
| catchUp | actual CatchRun at 2Δ, not just a duration inequality |
| noRestart | NoRestartAfter at max GST 0 |
| timeoutDelay | 3≤δt and every slot's 6Δ+ΔFG timeout inequality |
| slotLen | every slot's 4Δ spacing inequality |
| snapshot | actual FirstCutAfter cutZ witness within consuming deadline |
| nonempty | actual honest population nonempty at consuming deadline |
