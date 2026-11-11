# Claim reduction interfaces: complete statement row

Base: combined ASSEMBLY candidate `c378aa9a3ec91a0aa17e0c42560607442b322758`,
on main `3a20c7e0258bf40262d13e1dd41942166ff05e1c`, with the reviewed guarded
production correction inherited from `9d668433` over interface base `ca0a119c`.
Branch: `work/surface-recovery-guard`. This is a forward statement correction,
not a landing, proof, freeze, or source-acceptance release.

## Fixed recovery policy forward correction

The DA accepted a fixed ACCorrectLocal.recovery and separate recovery_nonneg law.
L9 and OutageReadPoint now retain their original b₁ ≤ recoveryTime bound and add
b₁ + C.recovery ≤ recoveryTime. Their service, sample, readiness, actual-read and
ancestry clauses are otherwise unchanged. The original durations conjunction is unchanged.
The former telescope lacked a policy floor; this is not a valid-run counterexample
or a proof that the former suppliers were false. Samples are not an inverse delay law.

OutageRecoveryBinding.duration matches the SAME M/K/C by
`C.recovery = (K.params.recovery : Time) * E.ΔAC`. This is a **NEW UNRESOLVED
SUFFICIENCY TARGET**, not a supplied fact. PersistenceReduction explicitly consumes it.
At recoveryTime = recoveryAt, rewriting the equation and unfolding recoveryAt makes
the added floor guard reflexive; recovery_nonneg gives the retained b₁ bound.
Exact equality is a deliberate policy-matching RESTRICTION, not mathematically
necessary for persistence: a larger advertised recovery may safely dominate a smaller
local floor. Unequal durations are not automatically unsound. No per-read choice,
generic coefficient 9, or claim of arbitrary-duration protection is introduced.
GBR's concrete duration equation/adequacy and dc's corresponding policy fit remain OPEN.
The endpoint, Holds/collision alternative and independent service-reserve gap are unchanged.

Constructor/consumer accounting: ACCorrectLocal has two additional fields; its generated
constructor, recursors and projections must be included in the exact dump drift report.
Only its outageProtected field formula gains the guard; other field formulas retain
their text. ReadPoint.protection gains the same guard. Seven direct consumer leaves
(GBR, FiniteRegime, ReadPoint, ClaimTransports, CorrectnessEdges, ProgressBudgetEdges,
ClaimReductionEdges) elaborate against the changed record without unrelated formula edits.
No explicit public ACCorrectLocal construction or outage field invocation was found.
dc D-INST owns LeadLocalRunContracts and LeadOutagePrefixHandoff migration and the
leadACCorrectLocal OPEN data note; framework owns staged integration. Their rebuild
and the exact full-dump constructor/projection accounting remain separate required gates.

## Guarded-window forward adaptation

The original height interface omitted the concrete delivery-spacing prerequisite and
quantified over arbitrary qualifying windows. The correction instead makes
FinalHeightSupply pointwise evidence for one W and makes FinalWindowSupply jointly
select W at the original query/deadline with
`6 * P.Δ + E.ΔFG ≤ 4 * P.Δ * (W.gap : Time)`, HealedFrom, healing.Run and those heights.
HealthyLivenessReduction therefore removes its independent FinalHeightSupply premise.
It consumes the acceptance, ancestry and three own-reader height projections returned
for that SAME W; FinalCacheSupply and FinalReadTransport.cache retain their exact
inputs, and DeadlinePremisesSupply independently produces Premises at E.ΔFG.
No arbitrary-window height law, timeoutDelay-to-spacing inference, gap enlargement or
latency enlargement is claimed. Joint guarded production remains OPEN; this fixes a
missing source prerequisite, not a valid-run counterexample, and supplies no proof.

## Verdict and ownership

All eight booked items are STATED: six conditional reductions, the output-validity
HoldsAlways wrapper, and the GenericClaims bundler. Existing CHAIN-REP nesting and
final-monotonicity edges are reused, not duplicated. Every new edge is an admission-free
Prop definition, not a theorem. Compilation establishes well-formedness only: it does
not establish truth, sufficient premises, realizability, or nonvacuity.

All new supplier interfaces below are **OPEN / NEW UNRESOLVED SUFFICIENCY TARGETS**.
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
| sleepySafe | `SleepySafetyReduction` | Fields:76–79 |
| sleepyLive | `SleepyLivenessReduction` | Fields:206–212 |
| healedSafe | `HealedSafetyReduction` | Fields:114–122 |
| persists | `PersistenceReduction` | Fields:150–153 |
| GenericClaims bundler | `GenericClaimsBundling` | Concrete/Endpoint:21–32 |

The conclusion telescopes preserve the original capability tests, all progress forms,
ready→horizon versus ready→heal intervals, ready-reader conditionality, HoldsAlways
versus Holds, and the original hash-collision excuse. No NoColl or constant-fault
premise is added to an unconditional claim. The bundler mechanically consumes the nine
individual fields; it is **not** a reduction from local correctness. Admissibility,
service, progress-fit and progress-tolerance remain the four separate downstream
inputs of GenericMeetsObligations. They are not supplied by this row.

Each reduction fixes one EngineBinding B and uses exactly M = B.map E rho hv.
Local contracts C, outage policy D and stored-read context R are indexed by that M;
no fresh run, changed map, replacement proposal or unrestricted Prop callback is used.

## New interface rows and source limitations

Every row is in `Milestones/Statements/Generic/ClaimTransports.lean` and remains OPEN.
Concrete source paths below are under `Lemmas/` unless otherwise stated.

| Interface | Source / exact consumer | Unresolved scope |
| --- | --- | --- |
| `ClaimDeadlineFit` | Concrete/Fields sleepySafe catch-up arithmetic; ReadPoint healthy proposal/healed; Accountable population threshold | Local catch-up ≤ engine cDur, local latency ≤ publication margin, max GST 0 + margin ≤ advertised nonfinal heal, α·n ≤ 2q−n, healthy population bound < 2q−n. These are arbitrary-contract numerical targets, not consequences of CorrectLocal. Nonnegative durations already come from C.durations. |
| `AdmissibleProposal` | confirmed_payload_projection_at; ProposalLiveReady's proposer readiness | Actual B,k must be non-genesis, nonnegative, hold through horizon and engine-cDur ready. The old ReadyProposal only gives local catch-up and honesty through hold. |
| `ProposalWitnessRefinement` | Concrete/Fields sleepyLive and healthyLive_confirmed; existing ProposalBudgetSupply/SleepyProposalBudgetSupply | Selects a witness with the same query/progress/deadline conditions, plus AdmissibleProposal. It does not assert every old witness qualifies and does not assume InBy or ProposalLiveReady. Both original budget suppliers remain separate inputs. |
| `EndReadTransport` | Growing/Simulation/Endpoint/Outputs.prefix_reader_at; confirmed_payload_projection_at; outage actual-time reads | Explicit ready/boundary/output transport at t and endCut t. Neither cutTime(endCut t)=t nor trace.time(cut(endCut t))=t is asserted. General RunMap does not supply the output-time identity. |
| `DeadlinePremisesSupply` | Generic/Obligations.Premises; concrete final query production | Produces the exact Premises at query + final-latency·ΔAC, only under actual final progress, healthy regime, heal≤query, deadline≤horizon and a ready deadline reader. FinalWindowSupply alone does not produce this bundle. |
| `FinalProposerTransport` | Concrete/Final final payload projection | Same W.block 0/W.cut 0; non-genesis and engine-cDur ready at actual proposal time. Local W.ready is not this. |
| `FinalReadTransport.processed` | concrete carrier-processing supply / final payload projection | Real strict-earlier BlockCallAt via CarrierProcessed, with own processing honesty and deadline, at an actual ReadyReadPoint. Current FinalCarrierSupply instead requires ReadyCut at trace.time j. |
| `FinalReadTransport.cache` | FinalCacheSupply's local conclusion at actual reader time | Retains Premises, same W, acceptance, ancestry, all three height steps, actual carrier processing and population threshold at t. This is local block ancestry, not a chain or liveness claim. Its actual-read realization is OPEN. |
| `ActualReadAccountability` | Growing/Simulation/Endpoint/Accountable.finalAccountable_readPoint:53 | Keeps both own-read honesty times, bounded read points, local run/no-collision, original 2q−n population cardinality and ChainAtts witnesses. Generic.FinalAccountable reads trace.time and cannot substitute. Additional generic Requirements/genesis-root inputs remain explicit. |
| `ActualResetSupply` | Growing/Obligations/Healthy/PreparationReset.healthy_preparation_reset_at:42 | Actual IsReset and healing.Run under healthy preparation, all advertised progress forms and heal≤horizon. Not inferred from ResetProgressSupply's gap/window. |
| `HighCanonicalSupply` | Generic/Obligations.HighCanonical and ACHealing.heal_after_reset source prerequisites | Same run, horizon, reset and Premises; never derived by applying heal_after_reset itself. |
| `PreparationPremisesSupply` | Healthy/PreparationReset and Generic/Obligations.Premises | Exact nonfinal healthy-preparation progress interval and horizon. Final-only DeadlinePremisesSupply does not supply this. |
| `ResetHealBudgetSupply` | Healthy/PreparationInitialize.healthy_preparation_initialize_late_at:30 | Selects an actual reset a with max GST 0 ≤ slotTime(slotOf a + drain), and that slot time + margin ≤ advertised heal. Does not claim every reset is early. No unbudgeted healed slot. |
| `OutageServiceSupply` | Outage/Engine/Query.outage_pre_service_at:52, outage_psync_at | **Source-type discrepancy remains OPEN:** concrete theorem supplies SleepyServiceBefore, not SyncRunAt. The new exact target asks SyncRunAt through b₀; existing ServiceTransport.sync only supplies b₀−Δ. No strengthening of that existing declaration or erasure of the reserve. |
| `ResilienceTipTransport` | Concrete/Fields.persists; Outage/Engine/Repair.outage_protected_at:29 | Schema/capability target tip is confirmed at actual t. This is representation, not protected-read ancestry. |
| `StoredReadContext` / `StoredReadTransport` | Healthy/CutTips.healthy_cut_tips_ancestor_at:77 at E1 498dd8b5 | Concrete source is readAfter at cutMap(lastOwn …), stateAt.now. Data cut/now/tip has no implementation. source_tip/current_tip explicitly request its correspondence to confirmedRead; now_bound retains the later stored-clock horizon bound. No clock equality or direct arbitrary-AC realization is claimed. |
| `HealedReadAncestry` | same healthy_cut_tips_ancestor_at | Translates HealthyPreparationQueryAt's fields into the same M's valid/clean run, nonfinal capability, Healthy, actual ready→heal progress, nonnegative/bounded heal, ordered engine cuts, BOTH ready reads and later stored-now≤horizon. Conclusion stays LOCAL BLOCK ANCESTRY between R.tip values; StoredReadTransport separately identifies the current reads. |

## Field-by-field premise discharge map

“Supplied” below means a named OPEN hypothesis of the intended edge, not proved evidence.

| Consumer premise | Named interface / derivation | Status |
| --- | --- | --- |
| growing local run, no collision | GrowingRunTransport.local_run/no_collision | Existing OPEN supplier; collision excuse is split only in Holds rows |
| engine/local Δ identity | M.delta_eq | Map data, realization OPEN |
| bounded own-read honesty, read boundary | EngineReadPoint.honest/boundary, RegimeTransport.ready + EngineReadPoint.ready | Existing OPEN suppliers, actual engine cutTime retained |
| end-time readiness and output state/time | EndReadTransport.ready/boundary/output | NEW OPEN target, no next-cut honesty |
| local versus engine catch-up, latency/heal | ClaimDeadlineFit.catchUp/latency_le_margin/healthy_start | NEW OPEN numerical targets |
| nonnegative durations | ACCorrectLocal.durations | Existing local data; no extra numerical supplier |
| proposal hold through horizon and proposer cDur | ProposalWitnessRefinement → AdmissibleProposal; FinalProposerTransport for anchor 0 | NEW OPEN targets; same actual witnesses |
| sleepy finite service/cardinal bounds | RegimeTransport.sleepy → SleepyPrefixAt | Existing OPEN supplier; no finite⇒unbounded inference |
| healthy finite service/awake/cardinal bounds | RegimeTransport.healthy plus bounded nonnegative horizon → HealthyPrefix | Existing OPEN supplier + engine bound arithmetic |
| accountable fraction and final population threshold | ClaimDeadlineFit.accountable/final_faults | NEW OPEN numerical targets |
| all progress forms and matching query budget | existing ProposalBudgetSupply, SleepyProposalBudgetSupply, ResetProgressSupply, FinalWindowSupply, plus explicit refinements | All OPEN, no single-pattern-only exclusion |
| final four anchors / delivery spacing / three height steps | FinalWindowSupply jointly selects SAME W, guard at E.ΔFG and pointwise FinalHeightSupply evidence | Corrected OPEN production target; no independent arbitrary-window height supplier, no constant FrameWindow manufacture |
| actual final carrier processing | FinalReadTransport.processed, existing FinalCarrierSupply kept separately | NEW actual-read target; strict processing witness retained |
| actual-read final cache ancestry | FinalReadTransport.cache, existing FinalCacheSupply kept separately | NEW target; not inferred from cut-clock cache supplier |
| final deadline Premises | DeadlinePremisesSupply | NEW OPEN target, not FinalWindowSupply |
| preparation horizon Premises | PreparationPremisesSupply | NEW OPEN target; consumed before healing, not proved by healing |
| reset / canonicality / drain-slot time | ActualResetSupply, HighCanonicalSupply, ResetHealBudgetSupply | Three separate NEW OPEN targets; heal_after_reset only consumes them |
| healed temporal ancestry | HealedReadAncestry + StoredReadTransport | NEW OPEN local ancestry and separate mapping, not compatibility⇒ancestry |
| outage participation/sample coverage | OutageTransport.participation/coverage and OutagePolicy.binding/horizon | Existing OPEN suppliers |
| fixed outage recovery floor / endpoint fit | ACCorrectLocal.recovery/recovery_nonneg; OutageRecoveryBinding.duration at SAME M/K/C | NEW OPEN exact-policy matching target; no inference from sample coverage or readiness |
| outage pre/post service | OutageServiceSupply | NEW OPEN exact implication, concrete service mismatch recorded above |
| resilience target tip | ResilienceTipTransport | NEW OPEN representation only |
| RootOk at actual reads | HonestReadTransport.roots; genesis separately for accountability/Premises | Existing OPEN supplier; never inferred from unrelated dc names |
| honest union coherence | explicit clean-run → Coherent hypothesis | OPEN instance supplier, never added to HoldsAlways |
| held-store inclusion in honest union | HonestBlocksAt witnesses y=validator.symm v, cut=M.cut i, t=cutTime i, using before_time/honest_eq and nonnegative actual cutTime | DERIVED, not a new supplier |
| chain prefix from local ancestry | ReadRepresentation.ancestor_prefix, with actual held membership/root/coherence premises; same M.chain/header | Existing OPEN representation; no final claim assumed |
| actual tip held / payload ancestry | LocalReadPoint and appropriate SleepyReadPoint/HealthyReadPoint; final cache invariants | Existing OPEN suppliers; finite actual-time consumers only |
| engine view and conviction binding | HonestReadTransport.chain_att_view, M.att_signer/att_conflict; key/validator equivalences | Existing OPEN map/provenance realization; source population count unchanged |

### Premises production: no silently discharged field

For both DeadlinePremisesSupply and PreparationPremisesSupply the exact returned
record is Generic.Premises, not an arbitrary predicate. Its fields are individually
OPEN obligations of the instance realization:

| Premises field | Required source accounting |
| --- | --- |
| run | GrowingRunTransport.local_run at same M |
| noColl | GrowingRunTransport.no_collision at same M |
| genesisRoot | instance genesis-root/digest derivation |
| sync | Service at the consuming deadline, including strict signedRow processing; GSTRunAt alone is not this record |
| awake | finite healthy awake bound at the same deadline/horizon |
| faults | finite healthy cardinal bound at the same deadline/horizon |
| catchUp | actual CatchRun at 2Δ, not just a duration inequality |
| noRestart | NoRestartAfter at max GST 0 |
| timeoutDelay | 3≤δt and every slot's 6Δ+ΔFG timeout inequality |
| slotLen | every slot's 4Δ spacing inequality |
| snapshot | actual FirstCutAfter cutZ witness within consuming deadline |
| nonempty | actual honest population nonempty at consuming deadline |

## Verification and inherited scope

Both leaves elaborate with `lean -DwarningAsError=true`, using exact pinned dependency
sources over the existing warm cache. Generated ConsensusLean root includes both leaves.
`python3 -I scripts/check-boundaries.py` reports zero findings. The recovery correction
changes local record data, the two outage guards and PersistenceReduction's supplier
telescope, not its claim conclusion or any endpoint statement. Earlier targeted packets
for 9222b346 and 880ddab6 passed within their reported comparison scopes, but do not
validate this correction. Fresh four-root, changed-cone, strict CSM, full dump with
intended record/projection drift and closure results remain required against exact heads.
The inherited E1/FINITE/READPOINT/CHAIN-REP/PROGRESS gates are not gates of this new head.

Complete-row Astra review and DA read-back remain pending. Supplier proofs, nonvacuity,
source realization and all correctness proofs remain open. No main push is authorized.

## Generic forwarding statement interfaces

The forwarding slice is additive statement vocabulary. Every supplier is **UNSUPPLIED**;
every implication target is **UNPROVED / OPEN**. Elaboration establishes well-formedness,
not sufficient premises, realizability, nonvacuity or service. Existing protocol, finality
gadget, local correctness, reader and endpoint declarations are unchanged.

All declarations below live in `Milestones/Statements/Generic/Forwarding.lean`.

| Interface | Consumer boundary | Unresolved scope |
| --- | --- | --- |
| `ForwardingEmit.Phase`, `phaseStep`, `dutyPhases`, `runPhases`, `expandDuties`, `eventPhases`, `boundary` | Existing engine operations and actual ordered release candidates | Concrete phase expansion vocabulary only. Candidate capture precedes act; states thread through duties; outputs preserve order and multiplicity. Cross-vocabulary constructor, step, fold, scheduler and boundary commutation remain OPEN. |
| `ForwardingEmit.EventBinding`, `ForwardingEmit.SchedulerBinding` | Actual event endpoints, release outputs and exact phase list | UNSUPPLIED endpoint and scheduler obligations, not an existence assertion. Different phase inductives require explicit transport, not definitional equality. |
| `ForwardingCodec` | Same-hash forwarding, block and arbitrary-message decoding | UNSUPPLIED exact signed body, parent, canonical-child, stamp and conditional-decode laws. Digest-context equations compare decoder results on the same contained object, never whole digest lists. |
| `OrderedDelivery` | Actual recursive-part traversal | Exact canonical event, drop and empty-cut cases preserve node execution and occurrence order. It is not a carried-object set or a retry mechanism. |
| `ForwardingSourceLaws` | Generic growing local execution and honest-prefix finality projection | UNSUPPLIED local run and finality-prefix fields. Projection-store equality is derived; it is not an independent assumption. Full prefix projection is not obtained from static retention alone. |
| `ForwardingPrefixSourceLaws.prefix_source` | Actual source growing run on a retained prefix | UNSUPPLIED transport to the target prefix source package. No global local-run substitution, inverse prefix retention or larger honest-block universe is asserted. |
| `ForwardingEngineLaws` | Honest receipt/process segments, actual release provenance and candidate readiness | UNSUPPLIED exact cut and internal occurrence maps, canonical-child processing, source-time self-processing, candidate placement and all release guards. Used honest receipt and forwarding-release domains are explicit. No target service is a field. |
| `ForwardReceiptHeldEdge` | Parent-first holding under same-signer honest acceptance provenance | UNPROVED implication retaining finite honest receiver, finalized ancestry, ordered traversal and source stamp guards. |
| `ReleasedReceiptAcceptedEdge` | Actual released wrapper and later receipt | UNPROVED implication retaining source honesty, same object and digest, cut bounds, ancestry and strict output deadline. Root stamp need only precede release; descendant equality is not assumed. |
| `ForwardAcceptancePublicationEdge` | Honest acceptance to actual same-event publication | UNPROVED implication from real release-phase candidate, exact decode and readiness. The released object itself must decode; an unsigned carrier with a signed descendant is not this publication path. |
| `AcceptanceRelayAfterEdge` | Post-synchrony accepted-block relay | UNPROVED implication over the actual run, network log, own-time honesty, reader horizon, effective source time and finalized ancestry. |
| `ForwardingReceiverServiceAfter`, `ReceiverServiceAfterEdge` | Global receiver output | Identical message and relay field formulas to the existing receiver service record. Explicit fieldwise conversion is OPEN; separate records are not definitionally equal. The output record is never a supplier premise. |
| `FiniteServiceBefore`, `FiniteServiceBeforeEdge` | Finite message, projected acceptance and node acceptance output | UNPROVED implication preserving nonnegative sources, reader deadlines, ancestry and strict output witnesses. The positive finality annotation is distinct from the node delay. |
| `ReceiverServiceAfterThroughEdge`, `FiniteServiceBeforeThroughEdge` | Prefix-indexed service on the same actual engine run | UNPROVED bounded targets consume prefix no-collision and explicitly supplied prefix mechanisms. Source and reader calls, used events and witnesses are retained. No fictional truncated engine, global no-collision premise or additional network-cutoff bound is introduced. |

The bounded message self-processing law uses one effective-time parameter. Post-synchrony
service chooses the later of source time and synchronization time; finite service chooses
source time. Both retain an actual bounded same-time processing witness and a strict
deadline at the output cut. Receipt processing has fresh-segment and actual-prior-witness
branches; duplicate status alone supplies neither branch.

Concrete queue retention, selected-duty publication, canonical child occurrences,
prefix source and no-collision transport, observation suppliers, service proofs and stock
recovery all remain **OPEN**. Statement checks do not close these realization obligations.
