# Claim reduction interfaces: complete statement row

These are conditional statement interfaces, with proofs of all reductions and the capstone.
Their concrete supplier realizations remain separate obligations.

The binding-generic endpoint includes `persists`, `sleepySafe` and `sleepyLive` as
shape-claim fields. Removing their separate comparator wrappers changes neither
these reduction rows nor the suppliers required for an arbitrary map.

## Fixed outage policy

L9 now lives only in `OutageReadPoint.protection`. The actual-cut twin is deleted.
The local data fix threshold, catch-up, recovery, both independent look-aheads,
η, arming lag and budget. `OutageRecoveryBinding` matches catch-up by
`C.catchUp + 1 ≤ cDur`, and the other seven values by equality. `ClaimDeadlineFit`
uses the same catch-up inequality. Local readiness and the population and committee
counts at `max C.catchUp (C.outageEta - 1)` require monotone transport from the advertised
catch-up, not equality rewriting. `RunMap.delta_eq` fixes `P.Δ = E.ΔAC` in every covered environment.
The participation catch-up is derived as `max cDur (η·ΔAC − 1)`.
Both reads are strict (T < time i, t < time j), as the end-of-time reads of
`StoredReadTransport.end_read` are. Certificate: cert obligation open: OC-K. Goldilocks: PROVED
at the local data equations (`goldilocks_outageReadPoint`), every input derived from L9's own
antecedents on the run's trace.

`ACServiceBefore` uses recipient-deadline cutoffs and the AC-owned `served` predicate.
Fresh delivery implies `served`; Goldilocks interprets it as fresh processing or
stamped retained evidence (`AC.MessageServedBefore`). Only message service and node
acceptance relay are required. Growing AC relay follows the `acBlock_prev`/`accept_next`
derivation in `Growing/Compose/Sync`. Goldilocks fixes its interpretation in
`GoldilocksLocalData.served`; another instance supplies its own.
The unused `ServiceTransport` is deleted; generic `Service` is unchanged.

## Guarded-window forward adaptation

The original height interface omitted the concrete delivery-spacing prerequisite and
quantified over arbitrary qualifying windows. The correction instead makes
FinalHeightSupply pointwise evidence for one W and makes FinalWindowSupply jointly
select W at the original query/deadline with those heights. Its former anchor-3 honest
proposal, spacing `6 * P.Δ + E.ΔFG ≤ 4 * P.Δ * (W.gap : Time)`, HealedFrom and run outputs are
removed: the reduction discarded or only forwarded them to the deleted processing field and to
cache premises the Goldilocks cache never used.
HealthyLivenessReduction therefore removes its independent FinalHeightSupply premise.
It consumes the acceptance, ancestry and three own-reader height projections returned
for that SAME W; FinalReadTransport.cache retains its exact
inputs, and DeadlinePremisesSupply independently produces Premises at E.ΔFG
on the honest sets truncated after the exact deadline.
Its nonfinal branch reads inclusion at L7 (`HealthyReadPoint.proposal`), so it also takes
PreparationPremisesSupply and ResetHealBudgetSupply, the capstone's existing `preparation` and
`resetBudget` rows, for L7's Premises, selected reset and post-drain bound.
No arbitrary-window height law, timeoutDelay-to-spacing inference, gap enlargement or
latency enlargement is claimed. Joint guarded production is PROVED for Goldilocks
(`Simulation.goldilocks_finalWindowSupply`) and remains OPEN for an arbitrary map; this
correction fixes a missing source prerequisite, not a valid-run counterexample.

## Verdict and ownership

All regime reductions, final accountability, the output-validity HoldsAlways wrapper and the
local-supplier capstone `meetsObligations_of_local` are PROVED, conditional on their explicit
suppliers. The reset-window progress supplier `ResetProgressSupply` is deleted: the healed-safety
reduction takes its reset and opening from `ResetHealBudgetSupply`, and no proof consumed it.
Existing CHAIN-REP nesting and
final-monotonicity edges are reused, not duplicated. The remaining statement interfaces are
admission-free Prop definitions, not proofs. Their compilation establishes well-formedness only,
not truth, sufficient premises, realizability, or nonvacuity.

Supplier interfaces below remain hypotheses of the generic reductions. Goldilocks proves
every one at its canonical run map (`goldilocks_localClaimSuppliers`); they remain
obligations for an arbitrary map, and named source routes do not constitute generic adapter
proofs. Joint proposal and final-window production now take the
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

Proved over any AC: the output-validity wrapper (`outputValidAlways`), the final
accountability reduction (`finalAccountabilityReduction`), the persistence reduction
(`persistenceReduction`), the healed-safety reduction (`healedSafetyReduction`) and the
healthy-liveness reduction (`healthyLivenessReduction`, in `ClaimReductionEdges`), and the
nesting and final-monotonicity edges with their system-level assemblies (`nestedChainEdge`,
`finalMonotoneChainEdge`, `nestedChainsAlways`, `finalChainsAlways`, in
`ChainRepresentationEdges`). Each is proved from the suppliers its definition takes. The sleepy
safety and liveness reductions are proved too (`sleepy_safety_reduction`,
`sleepy_liveness_reduction`), and so is the capstone (`meetsObligations_of_local_proof`, in
`ClaimReductionEdges`), which forwards the fields of one `LocalClaimSuppliers` record per mapped
valid run to the reductions. Goldilocks supplies these records by
`goldilocks_localClaimSuppliers` in `Lemmas/Growing/Simulation/GoldilocksClaimSuppliers.lean`; they remain
obligations for an arbitrary map.
Healed safety takes its cross-reader
agreement from `HealthyReadPoint.healed` at the opening that `ResetHealBudgetSupply` selects
with its reset. The persistence proof transports the
advertised outage participation to the local catch-up with
`OutageTransport.participation_local`, which needs no threshold bound: each count itself
forces `θ < 1`, and a negative `θ` makes the transported count immediate.

L-CORR owns these generic signatures and their premise accounting. Each instance owns
its realization, including the lead instance downstream in dc D-INST/W10. The stored
read-context data has no default implementation. No interface is inferred from similar
dc predicate names. No source-realization or automatic arbitrary-AC generalization is claimed.

## Declaration inventory

Paths below are relative to `ConsensusLean/Instances/Goldilocks/`.

| Booked item | Declaration in `Lemmas/Generic/ClaimReductionEdges.lean` | Original telescope (stock `Fields`, deleted with the arbitrary-binding endpoint) |
| --- | --- | --- |
| outputValid wrapper | `OutputValidAlways` | Fields:43–44 |
| finalAccountable | `FinalAccountabilityReduction` | Fields:68–70 |
| healthyLive | `HealthyLivenessReduction` | Fields:193–199; confirmed:167–174; stock final branch (deleted, Concrete/Final:325) |
| sleepySafe | `SleepySafetyReduction`, proved by `sleepy_safety_reduction`, with `D : SleepyLayer1.Data A` | Fields:76–79 |
| sleepyLive | `SleepyLivenessReduction`, proved by `sleepy_liveness_reduction`, with `D : SleepyLayer1.Data A` | Fields:206–212 |
| healedSafe | `HealedSafetyReduction` | Fields:114–122 |
| persists | `PersistenceReduction` | Fields:150–153 |
| local-supplier assembly | `meetsObligations_of_local` in `CorrectnessEdges.lean`, with public-indexed `events : SleepyLayer1.Data` | stock Concrete/Endpoint:21–32; now instantiated by `meetsObligations_growing` |

The conclusion telescopes preserve the original capability tests, all progress forms,
ready→horizon versus ready→heal intervals, ready-reader conditionality, HoldsAlways
versus Holds, and the original hash-collision excuse. No NoColl or constant-fault
premise is added to an unconditional claim. The capstone consumes one `LocalClaimSuppliers`
record per mapped valid run, not endpoint claims or reduction propositions. Its proof composes
the reductions. Admissibility, service, progress-fit, progress-tolerance and
`HealthyBetaFit` and `CommitteeHalfFit` remain separate inputs. The stored-read context and outage policy remain
explicit data families. The capstone is proved (`meetsObligations_of_local_proof`).

The windowed `SleepyLayer1.EventSafety`, `Extension` and `ProposalCoverage` suppliers
range over the consuming `RunMap`'s trace, honest sets, committee, proposer and digest,
with window endpoint `b ≤ rho.horizon`. This restricts supplier quantification compared
with a law for arbitrary traces and selections; it does not strengthen `Run` or change
the headline claims. `ReadAgreement` and `ReadyReadSafety` use the same map and bound.
`LocalClaimSuppliers.outputValidity` separately supplies `OutputValidityEdge M` without
readiness, regime or collision premises.

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

The reductions and `LocalClaimSuppliers` consume the following rows. Each row is
PROVED for Goldilocks as recorded below and remains an obligation for an arbitrary map. The un-windowed sleepy fields of
`ACCorrectLocal`, `FiniteLocal` and `SleepyReadPoint` are removed: proposal and
inclusion now take the same run, binding, service, independent count windows and
anchored-frame premises as `Extension`.

| Input | Source and remaining obligation |
| --- | --- |
| `SleepyLayer1.EventSafety` | PROVED for Goldilocks by `Generic.SleepyLayer1.goldilocks_event_safety` in `Growing/Sleepy/Node/Layer1Proofs`, from the sleepy invariant (`goldilocks_invariant_adapter`); actual composed-run frames only. `Generic.SleepyLayer1.goldilocksRunMap_event_safety` in `Growing/Simulation/SleepyWindows` matches the canonical generic row, conditional on an existing local supplier and `GoldilocksLocalData`; it does not construct that supplier. |
| `SleepyLayer1.OutputProvenance` | PROVED for Goldilocks by `Generic.SleepyLayer1.goldilocks_output_provenance` in `Growing/Sleepy/Node/Layer1Proofs`. Actual-read held membership plus ancestry to an event or frame floor; no event-comparability premise. Held membership overlaps `LocalReadPoint.held` deliberately so the standalone generic `ReadAgreement` Prop target has a coherent genesis-root case without importing unrelated payload fields. |
| `SleepyLayer1.Extension` | PROVED for Goldilocks by `Generic.SleepyLayer1.goldilocks_extension` in `Growing/Sleepy/Node/Layer1Proofs`. Same-reader ancestry at ordered cuts and evaluation times; not inferred from compatibility. `Generic.SleepyLayer1.goldilocksRunMap_extension` in `Growing/Simulation/SleepyWindows` matches the canonical generic row under `GoldilocksLocalData`, without constructing the local supplier. |
| `SleepyLayer1.SourceProvenance` | PROVED for Goldilocks by `Generic.SleepyLayer1.goldilocks_source_provenance` in `Growing/Sleepy/Node/Layer1Proofs`. Report source is an ancestor of a same-reporter confirmation event at an earlier or equal cut. The source need not equal the event block. |
| `PopulationQuorumSupply` | Shared FG requires `2 * (H t)ᶜ.ncard < P.n`; arbitrary admissible thresholds do not supply it. `Simulation.goldilocks_population_quorum_supply` proves it for the canonical run map with explicit `1/2 ≤ K.params.θ`, using the population clause independently of committee counts. |
| `SleepyWindowSupply` | `Simulation.goldilocks_sleepy_window_supply` proves it for the canonical run map with explicit threshold and two independent look-ahead equalities. One mapped point supplies both regimes, preserving horizon-clamped honesty and awake bounds. Catch-up domination comes only from `ClaimDeadlineFit.catchUp`. Sleepy claims do not consume outage policy; neither regime interface depends on the other. |
| `SleepyLayer1.ProposalCoverage` | PROVED for Goldilocks by `Generic.SleepyLayer1.goldilocks_proposal_coverage` in `Growing/Sleepy/Node/Layer1Proofs`; `Generic.SleepyLayer1.goldilocksRunMap_proposal_coverage` in `Growing/Simulation/SleepyWindows` matches the canonical row under `GoldilocksLocalData`, without constructing the local supplier. Both windows and anchored frames are explicit, hold is at least Δ and margin at least 6Δ; the hold must survive the horizon. |

All eight generic adapter targets are PROVED in `Generic.SleepyLayer1`:

| Target | Proof | Module under `Lemmas/Generic` |
| --- | --- | --- |
| `CacheProvenance` | `cache_provenance` | `SleepyFG` |
| `RowProvenance` | `row_provenance` | `SleepyFG` |
| `ConditionalViability` | `conditional_viability` | `SleepyFG` |
| `FramesFromSources` | `frames_from_sources` | `SleepyGlue` |
| `ReadAgreement` | `read_agreement` | `SleepyGlue` |
| `ReadyReadSafety` | `ready_read_safety` | `SleepyGlue` |
| `CommitteeTransport` | `committee_transport` | `SleepyTransport` |
| `PopulationTransport` | `population_transport` | `SleepyTransport` |

These proofs retain their explicit supplier premises: source provenance, event
safety, output provenance, extension and the population quorum are not supplied
by constructing a generic adapter. Count transport never substitutes one
look-ahead for the other. The `SleepyCut` test guards the complete constant closures of
`SleepyFG`, `SleepyGlue`, `SleepyTransport` and `ClaimReductionEdges`, allowing only the existing
placement-only `AC.gbar` dependency.

**PROVED canonical instance fit: slot constancy.** `GoldilocksWindowPremises` requires
`cm (sp.ts s + sp.Δ) = cm (sp.ts s)` at every slot. Generic `EventSafety`,
`Extension` and coverage contracts do not imply this for arbitrary committees.
Its source must be a property of the selected-committee RunMap together with the
concrete run interface, reviewed with the instance discharge; it is not added as
an unconditional generic law. `Simulation.GoldilocksSlotConstancy` states that
exact canonical-map obligation; `Simulation.goldilocks_slot_constancy` proves it
for every integer slot, including the negative-time clamp to slot zero.
The committee-valid run interface carries positive matching committee sizes and
`NoCollRun`-conditional committee facts. The canonical `goldilocksRunMap_transport`
supplies this interface from `ExecutionValid`, with the committee-facts conjunct proved
by `runCommittee_facts`. Bare abstract collision freedom alone does not establish
committee facts.

### Engine and regime suppliers

Every row is in `Milestones/Statements/Generic/ClaimTransports.lean`; Goldilocks proofs are
identified below, while arbitrary-map suppliers remain open.
Concrete source paths below are under `Lemmas/` unless otherwise stated.

| Interface | Source / exact consumer | Unresolved scope |
| --- | --- | --- |
| `ClaimDeadlineFit` | stock sleepySafe catch-up arithmetic (deleted Fields); ReadPoint healthy proposal/healed; Accountable population threshold | Goldilocks: PROVED by `goldilocks_claimDeadlineFit`. Local catch-up + 1 ≤ engine cDur, local latency ≤ publication margin, max GST 0 + margin ≤ advertised nonfinal heal, α·n ≤ 2q−n, healthy population bound < 2q−n. Open for arbitrary contracts, not consequences of CorrectLocal. Nonnegative durations come from C.durations. |
| `AdmissibleProposal` | confirmed_payload_projection_at; ProposalLiveReady's proposer readiness | Actual B,k must be non-genesis, nonnegative, hold through horizon and engine-cDur ready. The old ReadyProposal only gives local catch-up and honesty through hold. |
| `ProposalWitnessRefinement` | stock sleepyLive and healthyLive_confirmed (deleted Fields) | Goldilocks: PROVED by `goldilocks_proposalWitnessRefinement`. Selects the same query/progress/deadline witness jointly with AdmissibleProposal on the collision-free branch. No InBy or ProposalLiveReady conclusion is assumed; the weaker budget twins are deleted. |
| `DeadlinePremisesSupply` | Generic/Obligations.Premises; concrete final query production; `premises_truncH` | Produces the exact Premises at query + final-latency·ΔAC on `truncH M.honest` at that deadline (restarts bounded only through it; no whole-run `NoRestartAfter`), only under actual final progress, healthy regime, heal≤query, deadline≤horizon and a ready deadline reader. Truncation discharges neither the E.ΔFG delay fit nor the snapshot. FinalWindowSupply alone does not produce this bundle. Supplied for Goldilocks by `Simulation.goldilocks_deadlinePremisesSupply` (Growing/Simulation/PreparationPremises) under the fits `β ≤ 1/3`, `fgDelay + 6 ≤ 4·δt` and `13 ≤ heal` (final): `goldilocks_premises_at` at `b = deadline` (service at `E.ΔFG` through the deadline, snapshot witnessed by the deadline, whole-run restarts) restricted by `premises_restrict_truncH`; OPEN for an arbitrary map. |
| `FinalWindowSupply` | Concrete/Final final window extraction | Goldilocks: PROVED by `Simulation.goldilocks_finalWindowSupply` at arbitrary vote binding, with catch-up `18ΔAC` and hold `ΔAC`. Selects the same W with anchor-0 non-genesis and advertised readiness and the window's acceptance, ancestry and heights (FinalHeightSupply). The universal FinalProposerTransport twin is deleted. OPEN for an arbitrary map. |
| `FinalReadTransport.cache` | actual-reader cache coverage | Retains Premises (on `truncH M.honest deadline`, as supplied), same W, acceptance, ancestry, all three height steps and population threshold at t; its former HealedFrom and CarrierProcessed premises are removed (the Goldilocks cache never used them). A reader at `deadline ≤ t` keeps honesty, run and threshold on `M.honest` (nobody is honest on the truncation after the deadline, since `truncH H b t = H t ∩ {t ≤ b}`); ancestry and conclusion stay over `M.honest` (ancestry over the truncated honest blocks is ancestry over `M.honest`'s, as `honestBlocksAt_truncH_subset` gives). The cut-only cache twin is deleted. Supplied for Goldilocks by `Simulation.goldilocks_finalReadTransport` at any local supplier: the supplied ancestry and height steps give the holder's coverage (`cacheCoverage_of_anchor_window_upTo_at`, no reset), and `reader_cache_covers_at` carries it to the reader, whose acceptance of the last anchor is read on the truncated premises (relay at its first call one delay after the anchor, or catch-up before GST) and whose cache growth is on `M.honest`'s run (`Compose.fg_grows`). CarrierProcessed alone does not give that acceptance: a processed block can be refused. OPEN for an arbitrary map. |
| `ActualReadAccountability` | Growing/Simulation/Endpoint/Accountable.finalAccountable_readPoint | Keeps both own-read honesty times, bounded read points, local run/no-collision, original 2q−n population cardinality and ChainAtts witnesses. Requirements and genesis validity come from the actual run; no separate default-start Requirements input remains. Goldilocks: PROVED by `goldilocks_actualReadAccountability` for every run supplier whose runs are Goldilocks runs from some start. |
| `PreparationPremisesSupply` | Healthy/PreparationReset and Generic/Obligations.Premises | Supplied for Goldilocks by `Simulation.goldilocks_preparation_premises_supply` (Growing/Simulation/PreparationPremises), `goldilocks_premises_at` at `b = horizon`, `ΔF = E.ΔFG`, under the fits `fgDelay + 6 ≤ 4·δt` and `13 ≤ heal` (nonfinal); OPEN for an arbitrary map. Exact nonfinal healthy-preparation progress interval and horizon. Final-only DeadlinePremisesSupply does not supply this. |
| `ResetHealBudgetSupply` | Healthy/PreparationInitialize.healthy_preparation_initialize_late_at:30 | Supplied for Goldilocks by `Simulation.goldilocks_resetHealBudgetSupply` at `K S A` and the local data equations (drain 2k + 5, margin 6Δ), at any vote binding; OPEN for an arbitrary map. Selects an actual reset a with max GST 0 ≤ slotTime(slotOf a + drain), and that slot time + margin + 1 ≤ advertised heal (the + 1 absorbs the stored clock lag, cutTime − 1 ≤ R.now). The same selection supplies an opening: an honest proposal of a slot s₁ ≥ slotOf a + drain with ḡ + 4Δ ≤ t_{s₁}, t_{s₁} + 6Δ ≤ horizon and t_{s₁} + margin + 2 ≤ heal, the opening HealthyReadPoint.healed requires (its compatibility reads are strictly after t_{s₁} + margin, and a stored read is at R.now ≥ heal − 1) (source: Healthy/Opening.healthy_bounded_repairing_opening_at within RepairDefs.reserve). Does not claim every reset is early. No unbudgeted healed slot. |
| `OutageServiceSupply` | Outage/Engine/Query.outage_pre_service_at; Simulation/ReceiverService.goldilocks_postStopService | Goldilocks: PROVED by `goldilocks_outageServiceSupply`. Supplies `ACServiceBefore` through b₀ and `PostStopService` from b₁ (message service and the unguarded acceptance relay that the recovery consumes; no delay order, block, signed-row or attestation field). AC-owned message service includes fresh and retained evidence. |
| `ResilienceTipTransport` | Simulation/RunMapRepresentation.goldilocksRunMap_resilienceTipTransport; Outage/Engine/Repair.outage_protected_at:65 | Schema/capability target tip is confirmed at actual t. This is representation, not protected-read ancestry. Goldilocks: PROVED by `goldilocksRunMap_resilienceTipTransport`. |
| `StoredReadContext` / `StoredReadTransport` | Healthy/CutTips.healthy_cut_tips_ancestor_at; Sleepy/Engine/ReadPoint.engine_read_point, readAfter_lastOwn, stateAt_lastOwn; Sleepy/Engine/Reads.ready_read_cut_at; Obligations/Sleepy.now_mono, stored_now_ge_cutTime_sub_one | The single read binding (DRAFT, awaiting the statement ruling). Engine cuts: the output is read at (R.cut, R.now), the cut after the last own event and the stored clock; source_tip/current_tip identify the tip, source_state the whole local state at R.cut and M.cut i; under engine readiness c+1, ready_point gives a ready read point with catch-up c, its boundary and cutTime i − 1 ≤ R.now; now_mono/cut_mono order one reader's reads. Claim times: end_read gives R.now = t at endCut t, strict t < time (M.cut (endCut t)), readiness and boundary there. Derived: `stored_output_eq`, `end_read_output_eq` (ClaimReductionEdges). Goldilocks: PROVED by `goldilocksRunMap_storedReadTransport`. No global clock equality. |
| `HealedReadAncestry` | same healthy_cut_tips_ancestor_at | Goldilocks: PROVED by `Simulation.goldilocks_healedReadAncestry` at arbitrary vote binding. Translates HealthyPreparationQueryAt's fields into the same M's valid/clean run, nonfinal capability, Healthy, actual ready→heal progress, nonnegative/bounded heal, ordered engine cuts, BOTH ready reads and later stored-now≤horizon. Conclusion stays LOCAL BLOCK ANCESTRY between R.tip values; StoredReadTransport separately identifies the current reads. |

## Field-by-field premise discharge map

The interfaces below remain hypotheses of the generic edges. Named Goldilocks suppliers are
proved evidence at the canonical run map, not assumptions of the Goldilocks endpoint.

| Consumer premise | Named interface / derivation | Status |
| --- | --- | --- |
| growing local run, no collision | GrowingRunTransport.run/no_collision | PROVED for Goldilocks by `goldilocksRunMap_transport`; OPEN for an arbitrary map. Collision excuse is split only in Holds rows |
| engine/local Δ identity | M.delta_eq | Goldilocks map data by `rfl` in Growing/Simulation/RunMap; OPEN realization for an arbitrary map |
| bounded own-read honesty, read boundary | EngineReadPoint.honest/boundary, RegimeTransport.ready + EngineReadPoint.ready | EngineReadPoint supplied for Goldilocks (`goldilocksRunMap_engineReadPoint`); OPEN for an arbitrary map; RegimeTransport.ready PROVED for Goldilocks (`goldilocks_regimeTransport`); actual engine cutTime retained |
| end-time readiness and output state/time | StoredReadTransport.end_read + `end_read_output_eq` | Under readiness at t: stored clock t at endCut t, strict read point at M.cut (endCut t); output is the chain of the confirmed read at t. PROVED for Goldilocks; OPEN for an arbitrary map |
| local versus engine catch-up, latency/heal | ClaimDeadlineFit.catchUp/latency_le_margin/healthy_start | Goldilocks: PROVED by `goldilocks_claimDeadlineFit`; open for an arbitrary map. catchUp states C.catchUp + 1 ≤ cDur, supplying the stored-clock bridge's numerical slack without the bridge itself |
| nonnegative durations | ACCorrectLocal.durations | Existing local data; no extra numerical supplier |
| proposal hold through horizon and proposer cDur | ProposalWitnessRefinement → AdmissibleProposal; FinalWindowSupply for anchor 0 | Goldilocks: PROVED by `goldilocks_proposalWitnessRefinement` for nonfinal proposals; FinalWindowSupply PROVED for Goldilocks by `Simulation.goldilocks_finalWindowSupply`, with anchor-0 engine readiness. Same jointly selected witnesses; OPEN for an arbitrary map |
| sleepy finite service and independent count windows | RegimeTransport.sleepy → `SleepyServicePrefix C` (0 ≤ b, `ACServiceBefore` through b, slot `FaultBoundAt` counts at the look-ahead clamped at b; no `Δ ≤ ΔFG` order); SleepyWindowSupply → CommitteeWindow and PopulationWindow | SleepyWindowSupply supplied for Goldilocks; RegimeTransport.sleepy PROVED for Goldilocks by `goldilocks_regimeTransport`; the concrete bridge `sleepyServiceBefore_of_prefix` gives the finite sleepy service at the S4 retained-evidence `served`; separate population/committee look-aheads; no finite⇒unbounded inference |
| healthy finite service/awake/cardinal bounds | RegimeTransport.healthy: generic `Service … g E.ΔFG horizon` (the `Premises.sync` form; no `Δ ≤ ΔFG` order), awake, population and committee bounds | Goldilocks: PROVED by `goldilocks_regimeTransport` at the local data and `K S A`; Goldilocks service source `resetService_of_psync_at` with `signed_row_service_psync_at` at E.ΔFG. `GSTRunAt` was replaced: its `delta_le` failed when ΔFG < ΔAC |
| accountable fraction and final population threshold | ClaimDeadlineFit.accountable/final_faults | Goldilocks: PROVED by `goldilocks_claimDeadlineFit`; open for an arbitrary map |
| all progress forms and matching query budget | ProposalWitnessRefinement, FinalWindowSupply | Goldilocks: PROVED by `goldilocks_proposalWitnessRefinement` for nonfinal proposals; FinalWindowSupply PROVED for Goldilocks by `Simulation.goldilocks_finalWindowSupply`. No single-pattern-only exclusion; OPEN for an arbitrary map |
| final four anchors / three height steps | FinalWindowSupply jointly selects SAME W with pointwise FinalHeightSupply evidence | Goldilocks: PROVED by `Simulation.goldilocks_finalWindowSupply`; OPEN for an arbitrary map. No independent arbitrary-window height supplier, no constant FrameWindow manufacture |
| actual-read final cache ancestry | FinalReadTransport.cache | no cut-clock cache twin; supplied for Goldilocks (`goldilocks_finalReadTransport`); OPEN for an arbitrary map |
| final deadline Premises | DeadlinePremisesSupply | on `truncH M.honest deadline`, not FinalWindowSupply; supplied for Goldilocks (`goldilocks_deadlinePremisesSupply`, three coefficient fits); OPEN for an arbitrary map |
| preparation horizon Premises | PreparationPremisesSupply | supplied for Goldilocks (`goldilocks_preparation_premises_supply`, two coefficient fits); OPEN for an arbitrary map; consumed before healing, not proved by healing |
| reset / drain-slot time | ResetHealBudgetSupply | Goldilocks reset budget: PROVED by `Simulation.goldilocks_resetHealBudgetSupply`, from the query's healthy preparation and its repair opening. The budget supplier selects the reset, and heal_after_reset only consumes it. |
| healed temporal ancestry | HealedReadAncestry + StoredReadTransport | Goldilocks: PROVED by `Simulation.goldilocks_healedReadAncestry` at arbitrary vote binding and the actual stored-read context. Uses the temporal record-extension proof, not compatibility⇒ancestry. |
| outage participation | OutageTransport.participation and OutagePolicy.binding/horizon | PROVED for Goldilocks by `goldilocks_outageTransport` at `goldilocksOutagePolicy` (the run's own indexed point), and `OutageTransport.participation_local` at the local catch-up; OPEN for an arbitrary map. At the run's own point and selection the population and look-back committee η-sleepy clauses (outage catch-up `max cDur (η·ΔAC − 1)`) follow from `Outage` (`OutageTransport.participation_of_outage`). The destination coupling (sample coverage) is removed: it is unsatisfiable under growing faults. |
| fixed outage recovery floor / endpoint fit | ACCorrectLocal policy data and OutageRecoveryBinding's seven equalities plus C.catchUp + 1 ≤ cDur at SAME M/K/C | Goldilocks: matching PROVED at the local data equations and the endpoint contract (`goldilocks_outageRecoveryBinding`); policy matching and monotone readiness/count transport OPEN for an arbitrary map. Protection lives only in OutageReadPoint, with no actual-cut twin. |
| outage pre/post service | OutageServiceSupply | Goldilocks: PROVED by `goldilocks_outageServiceSupply`; AC-owned service and node acceptance relay, open for an arbitrary map |
| resilience target tip | ResilienceTipTransport | Representation only; PROVED for the Goldilocks run map |
| RootOk at actual reads | HonestReadTransport.roots; genesis from the run (`ACRun.run_root`) | supplied for Goldilocks (`goldilocksRunMap_honestReadTransport`); OPEN for an arbitrary map; never inferred from unrelated dc names |
| honest union coherence | explicit clean-run → Coherent hypothesis | PROVED for Goldilocks by `goldilocksRunMap_coherent`; OPEN for an arbitrary map, never added to HoldsAlways |
| held-store inclusion in honest union | HonestBlocksAt witnesses y=validator.symm v, cut=M.cut i, t=cutTime i, using before_time/honest_eq and nonnegative actual cutTime | DERIVED, not a new supplier |
| chain prefix from local ancestry | ReadRepresentation.ancestor_prefix, with actual held membership/root/coherence premises; same M.chain/header | supplied for Goldilocks (`goldilocksRunMap_readRepresentation`); OPEN for an arbitrary map; no final claim assumed |
| actual tip held / payload ancestry | OutputValidityEdge; LocalReadPoint, SleepyLayer1 coverage and HealthyReadPoint; final cache invariants | PROVED for Goldilocks by `goldilocksRunMap_outputValidity` via `engine_outputValid_at`; OPEN for an arbitrary map. OutputValidityEdge needs the honest reader's output tip at M.clock of its stored state to belong to the mapped FG tree. Neither ReadRepresentation nor HonestReadTransport alone supplies this membership. For Goldilocks, finalized membership follows from FG reachability and confirmed membership from AC ReqOutputs. |
| engine view and conviction binding | HonestReadTransport.chain_att_view, M.att_signer/att_conflict; key/validator equivalences | supplied for Goldilocks (`goldilocksRunMap_honestReadTransport`); OPEN for an arbitrary map; source population count unchanged |

### Premises production: no silently discharged field

For both DeadlinePremisesSupply and PreparationPremisesSupply the exact returned
record is Generic.Premises, not an arbitrary predicate. Goldilocks supplies it through
`goldilocks_deadlinePremisesSupply` and `goldilocks_preparation_premises_supply`; its fields remain
individual obligations for an arbitrary map:

| Premises field | Required source accounting |
| --- | --- |
| noColl | GrowingRunTransport.no_collision at same M |
| sync | Service at the consuming deadline, including strict signedRow processing; GSTRunAt alone is not this record |
| awake | finite healthy awake bound at the same deadline/horizon |
| faults | finite healthy cardinal bound at the same deadline/horizon |
| catchUp | actual CatchRun at 2Δ, not just a duration inequality |
| noRestart | NoRestartAfter at max GST 0; on `truncH H b` the restart field reads only restarts through `b`, exactly `NoRestartUpTo` through `b` |
| timeoutDelay | 3≤δt and every slot's 6Δ+ΔFG timeout inequality |
| slotLen | every slot's 4Δ spacing inequality |
| snapshot | actual FirstCutAfter cutZ witness within consuming deadline |
| nonempty | actual honest population nonempty at consuming deadline |

A source that bounds honest restarts only up to the horizon `b` (`NoRestartUpTo`)
does not supply `noRestart` on `H`. It supplies the whole record on the honest sets
truncated after `b`: `premises_truncH` (Lemmas/Generic/HealingEdges.lean) builds
`Premises tr (truncH H b) …` from the other fields as stated here, and
`ACRun.run_truncH` gives the run there. `H_z` and a reset by `b` are unchanged by the
truncation (`HZ_truncH`, `isReset_truncH_iff` in Lemmas/Generic/HealingLeaves.lean).
`ACRun.run_truncH` is an instance obligation; Goldilocks supplies it in
`goldilocksRunInterface` (Lemmas/Growing/Simulation/GoldilocksBridge.lean), from
`KernelProof.goldilocksRun_truncH` and `CommitteeFacts.truncH`.
At the Goldilocks map with `b = rho.horizon` it does: every call cut is at or before the
horizon (`isCall_time_le_horizon`), so `NoRestartUpTo … horizon` is `NoRestartAfter`
(`goldilocks_preparation_premises_supply`).
DeadlinePremisesSupply returns, and FinalReadTransport.cache consumes, the truncated
record at the exact deadline, which can be before the horizon. PreparationPremisesSupply
returns `Premises` on `M.honest` at the horizon, with whole-run `noRestart`; at the
Goldilocks map that is the horizon case just described. The Goldilocks deadline record is
the same whole-run `Premises` at the deadline (`goldilocks_premises_at`), restricted to the
truncation by `premises_restrict_truncH`.

### Generic healing report-delivery delay

The milestone window pins maximum height `M`, top status `hmax = hj + 1`, and
the common `J` whenever top. Its four-key measure is
`frameKey = 2 * hmax + [hmax = hj + 1]`, not the former floor/clean-kind key.
The restatement excludes mixed contest/gap windows and varying-`J` top contests,
admits same-M common-J clean/contest toggles, and weakens leaf 8's two contest
round bounds (1 → 2 and 0 → 1). `resetSlots` retains its five-key range and
`healMargin` is unchanged. Replacement window and AC field suppliers are
separate proof obligations; this restatement lands only with P-U adoption.

The proposal-height field requires pre-state `hmax - 1 ≤` post-proposal height
and pre-state `hj <` that height. The report field retains tree membership and
uses `Anc F R` rather than `Anc fcRoot R`. The protocol frame and viable-head
rules are in `specs/goldilocks/tex/shared/fg.tex`, lines 71–77 and 136–152.

Instance obligation: `round_of_warm_at` and `rise_reset_rounds_at` require
`∀ s, P.slotTime (s + 1) + 2 * P.Δ + ΔF ≤ P.slotTime (s + P.δt)`.
They are proved over any `ACHealing` with this inequality as a premise
(`round_of_warm_at_of_healing` in Lemmas/Generic/HealingRounds.lean;
`rise_reset_rounds_at_of` and `rise_reset_rounds_within_of` in
Lemmas/Generic/HealingEdges.lean). The real-time reset `exists_reset_within`
(Lemmas/Generic/HealingEdges.lean) supplies it on the four-delay grid from
`6Δ + (D + GΔ) + ΔF ≤ 4Δ·δt`; its callers are the healthy preparation and final
reset premises. The leaves also require `slotLen`; the assemblies obtain it from
`Premises`.
On the four-Δ grid, substituting slotTime(s) = 4sΔ reduces the delay condition to
6Δ + ΔF ≤ 4Δ·δt. The generic instance obligation for an arbitrary schedule is not
discharged here.
`round_of_warm_at` additionally requires `(H b).Nonempty`, explicit in its
generic contract (Milestones/Statements/Generic/Healing.lean). Earlier proposer
honesty does not supply honesty at the later horizon. The rise contract already
has this premise.

### Goldilocks healing witness

Goldilocks: PROVED by `Generic.goldilocks_ac_healing` in
`Lemmas/Growing/Healing/Supply/Fields.lean`, assuming `3 ≤ sp.toParams.δt`.
It supplies `goldilocksACHealing` with warmup `2k`, follow `3` and drain `2k + 5`.
`heal_after_reset` reads no canonical-source premise (retired in Wave 7 Q1);
`goldilocks_heal_after_reset` supplies it from the reset, budget and premises. This supplies the
healing field only, not the assembled `ACCorrectLocal` witness or a generic
claim endpoint.

### Goldilocks high-row bridge target

No Goldilocks-side bridge from the generic high-row, no-contest or
historical-entry leaves is stated (the conditional `high_row_source_at_goldilocks`
is deleted as unused); the concrete reset kernel proves its own high-row source
(`Healing/Retention/Rows.high_row_source`).
