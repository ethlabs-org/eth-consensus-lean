# Contract to Lean map

## FG-SA sleep services (P-ShA round 5, 2026-10-10)

`CatchUp` supplies ready receiver service, exact fresh HEAD service, named target
service, and a constructor for proposal target service. Each retained object has
its own ready anchor, HistorySafeAt, handler window and receiver epoch.

`Count` and `GateReceiptScope` keep their local sleep interfaces. `SameLabel`
now derives SameLabelServiceScope from Base execution, restarts at wakes and
LabelSyncOn. The public `Export.fgsa_sameLabelClaim` compiles with its old type.

`ScoreServiceScope` supplies frozen HEAD service and named support block service
in both directions. New ScoreRun and ExactHead forms prove support incidence,
score equality, walk reflection, ghost transfer and exact joined HEAD output.

`HeadRelayServiceScope` supplies Relay receipts for each candidate and epochs.
The joined HEAD read supplies network provenance from its local restart bound.
HeldReceipt has an exact target-service form.

`RetainedServiceScope` supplies proposal service and score service for each candidate.
`RetainedExactHeadRunGeometryOn` guards every reader by joinedAt. New retained
path, reflection and geometry forms build that record. H6/H6S/H17/L4R/HG1/L2
read suppliers have `_joined` forms with the same reader guard.
Tests.RetainedConsumers checks these guarded forms.

`RegimesService` provides ten additive Clean/Recovery adapters. Existing names
and types stay in their original files. The original Regimes target is still
EXPECTED-FAIL: its ten legacy bodies request the removed global NoRestart field.
That field cannot be reconstructed for an honest run with a wake restart.
No public claim statement, baseline or exception changed.
See `docs/SLEEP-LEDGER.md`, P-ShA round 5, for scopes and named family suppliers.

## Receipt relay update (2026-09-28)

The dated relay note in `CONTRACT.md` supersedes references below to
accepted-object regime fields. The public regimes now require receipt
relay. The shared `GridCO/Proofs/ReceiptRelay` and `Paths` modules derive
vote settlement and block storage. `ScoreExtension` supplies the common
seat, score, and eligibility algebra; `ProposalTransport` constructs it
from actual runs. Exact proposal vote-set helpers are replaced.
`SAPC/Proofs/ReceiptRelay` derives exact complete-object relay and provides
specialized regime methods for its archive consumers. No model rule or
public contract conclusion changes.

## Derived roots update (2026-09-29)

Plan I9 (`docs/plans/2026-09-29-i9-derived-roots.md`; `FRAMEWORK-DESIGN.md`
§12 I9) makes block roots derived. The dated I9 note in `CONTRACT.md`
supersedes references below to `RootInjective` as a run assumption: the
regimes keep the field, and `rootInjective_all` proves it for every run.
The FG-SA rows below give the facts after Task 9. `ContentAgree` is a
theorem (`contentAgree`), and `Tests/RootCollision.lean` holds positive
tests. Before I9 (2026-09-29), `ContentAgree` was a store-pair premise,
and `Tests/RootCollision.lean` showed the DQ10/I9 root collision. The new
names:

```text
┌──────────────────────────────────────┬──────────────────────────────────────────────┐
│ File (without .lean)                 │ I9 names                                     │
├──────────────────────────────────────┼──────────────────────────────────────────────┤
│ AvailableChainModel/Objects/Codec    │ epair, efst, esnd, epair_inj, encList,       │
│                                      │ encOption, encBool (length-delimited codec)  │
│ AvailableChainModel/Objects/Blocks   │ nodeRoot; Block.node parent slot body;       │
│                                      │ Block.root (derived), Block.body;            │
│                                      │ Block.root_injective; parent_mem_iff_root,   │
│                                      │ parent_mem_and_iff_root (lookup)             │
│ AvailableChainKit/Roots              │ rootInjective_all                            │
│ AvailableChainGridCO/Proofs/Handling │ blockKnown_parent_slot_iff_root,             │
│                                      │ admitProposal_missingParent                  │
│ AvailableChainGridCO/Proofs/Roots    │ rootInjectiveBelow_all                       │
│ AvailableChainSAPC/Proofs/BaseViews  │ blockKnown_parent_slot_iff_root,             │
│                                      │ proposalEnters_missingParent,                │
│                                      │ admitProposal_missingParent                  │
│ AvailableChainSAPC/Proofs/           │ process_pc_missingPaths                      │
│ CertificateValidity                  │                                              │
│ AvailableChainLStar/Proofs/Hooks     │ blockKnown_parent_slot_iff_root,             │
│                                      │ admitProposal_missingParent                  │
│ AvailableChainRegistry/CounterRun    │ chain_depth, chain_injective (chain_root is  │
│                                      │ removed)                                     │
│ AvailableChainRegistry/Gaps/NoInput  │ clockBlock_depth, clockBlock_injective       │
│                                      │ (clockBlock_root is removed)                 │
│ AvailableChainSimplexFG/Objects      │ RowCodec, fgBodyTag, encFGBody,              │
│                                      │ encFGBody_inj, FGBlock.root (derived),       │
│                                      │ FGBlock.root_injective                       │
│ AvailableChainKitFG/Accountable      │ rootInjectiveOn_all                          │
│ AvailableChainKitFG/Correspondence   │ viewRootInj_all                              │
│ AvailableChainKitFG/FrameChannels    │ Pure contest, floor and retention geometry  │
│ AvailableChainFGSA/Model             │ packInner, packBody, appOf, rowsOk (in       │
│                                      │ wellFormed and blockAccepted); fgBlock (body │
│                                      │ from packInner); eraseFG (body encFGBody)    │
│ AvailableChainFGSA/Statements/       │ MetaInv.wireTree (with rowsOk)               │
│ Invariants                           │                                              │
│ AvailableChainFGSA/Proofs/Carrier    │ eraseFG_root (re-proved by induction),       │
│                                      │ eraseFG_injective, packBody_inj, rowsOk_iff, │
│                                      │ rows_eq_of_rowsOk                            │
│ AvailableChainFGSA/Proofs/Admission  │ parentFG_isSome_iff_root (lookup),           │
│                                      │ admitBlock_missingParent (no-op),            │
│                                      │ blockAccepted_rowsOk                         │
│ AvailableChainFGSA/Proofs/StoreInv   │ rootInj_all                                  │
│ AvailableChainFGSA/Proofs/CrossNode  │ contentAgree (MetaInv at both stores),       │
│                                      │ contentAgree_reachable                       │
│ AvailableChainFGSA/Tests/Support     │ admitWith, process_eq_admitWith              │
└──────────────────────────────────────┴──────────────────────────────────────────────┘
```

## Notation

`M` means `AvailableChainModel`; `S` means `AvailableChainStatements`.
Statement names are in `AvailableChain.Statements.Generic`; model names are
in `AvailableChain` or `AvailableChain.Generic`. Sources are relative to
`../decoupled-consensus/verified-consensus`.

## Grid CO: complete Draft 4.3 contract

`AvailableChain.GridCO.gridContract_from_engine` in
`AvailableChainGridCO/Proofs/Contract.lean` proves `GridContract p G E`
for `0 < G` and `E.Δ = p.Δ`. Every run premise comes from the common
contract regimes. See [Grid CO status](GRIDCO-STATUS.md) for constants,
premises, and the brief history of resolved issues.

The instance keeps three layers:

- `Model/Protocol.lean`: parameters, schedule, signed HEADs, proposal
  views, stores, GHOST, counted obligations, release, gates, and `gridCO`.
- `Statements/Contract.lean`: `gridInterface`, `roundedLevel`,
  `gridConstants`, and `GridContract`. It contains no claim proofs.
- `Proofs/`: engine lemmas and the complete contract proof.

The main proof paths below use files in `AvailableChainGridCO/Proofs/`.

- `Basic.lean` proves timing, constant validity, and `outputOrder`.
  `Windows.lean` defines gate and release inputs, `SynchronousLabel`,
  `CleanThroughLabel`, seat alignment, and `ProposalRelayReady`.
  `Regimes.lean` derives these label and relay premises from the regimes.
- `Execution.lean`, `History.lean`, `Stamps.lean`, `Handling.lean`,
  `ClockBounds.lean`, `Receipts.lean`, `Paths.lean`, `HeadTargets.lean`,
  and `ReceiptOrigins.lean` connect events, receipts, paths, and reads.
  `Execution.lean` keeps only the Grid CO forms of the schedule lemmas.
  The engine-generic lemmas (namespace `AvailableChain.Engine`) are in
  the library `AvailableChainKit` (see "Kit and engine v2 sketch").
  `Votes.lean` proves authentication and count bounds; `RecordSlots.lean`
  proves slot order and fresh-record replacement.
- `WindowMargin.lean` proves the relay premise "the reader does not exclude
  the object up to the cutoff" for each caller of the five relay lemmas
  (`synchronous_head_handled_early`, `synchronous_proposal_delivered`,
  `synchronous_receipt_before`, `synchronous_block_path_at_gate`,
  `handled_before_proposal_of_ready`). Its `head_not_excluded_before`
  replaces the old Registry lemma `inWindow_not_excluded`. `Hooks.lean` proves the E4 hook
  facts for `gridCO p` (`excludes_inert`, `excludes_stable`,
  `processed_stable`, `deps_stable`, `handles_carries`) and the exactness
  tests of `excludes` (`excludes_head_iff`, `excludes_proposal`,
  `excludes_not_processed`).
- `Goldfish.lean`, `Relay.lean`, and `Map.lean` prove local walk, gate,
  snapshot-count, and obligation invariants. `CrossView.lean` proves
  `sameLabel_from_engine`; `Snapshot.lean` proves `snapshot_from_engine`.
  `Release.lean` bounds conflicting rows that survive release.
- `Walk.lean`, `Support.lean`, `Transfer.lean`, `Frozen.lean`,
  `TransferViews.lean`, and `MergedViews.lean` prove ordinary HEAD
  transfer. `Preservation.lean` proves `preserve_from_engine`.
  `GenuineHistory.lean` then gives clean history; `CleanSafety.lean`
  proves `clean_safety_from_engine` and `monotone_from_engine`.
- `Roots.lean` derives root uniqueness from the contract. `Proposals.lean`
  proves honest emission and proposal views. `WalkTransport.lean`,
  `ProposalAdoption.lean`, `ProposalDelivery.lean`, `ProposalViews.lean`,
  `ProposalViewRelay.lean`, and `ProposalTransport.lean` prove delivery
  and adoption. `ProposerTransfer.lean` and `ProposalHeads.lean` connect
  ordinary proposal parents to honest HEADs. `CleanInclusion.lean` proves
  `included_from_engine` with delay `6Δ` for all three inclusion fields.
- `Coverage.lean` proves clean coverage and public row writes.
  `Protection.lean` proves preservation from armed rows.
  `Outage.lean` proves `stable_resilient_from_engine`, including the
  pending gate and renewal, with `A = 4Δ` and `Π = min(η,L)`.
- `RowOrigins.lean`, `RecoverySupport.lean`, and `RecoveryPersistence.lean`
  prove exact row sources and permanent support. `RecoveryStages.lean`
  proves row and source support after `K` stages. `RecoveryRepair.lean`
  proves record repair; `RecoverySuffix.lean` proves the safe suffix.
  `Recovery.lean` proves `recovered_from_engine` within `K(L+Δ)+G+10Δ`.
- `Contract.lean` constructs the bundle directly. The library root imports
  it and `Tests/Smoke.lean`; all proof modules are in the default build.

## SA: slow arming with one release level

`AvailableChain.SA.saContract_from_engine` in
`AvailableChainSA/Proofs/Contract.lean` proves the full Draft 4.3 bundle.
`fastP1_from_engine` in `Proofs/FastOutage.lean` proves the fast outage field of that bundle. See [SA status](SA-STATUS.md) for the rules, constants,
proof path, and validation.

The instance has three layers:

- `Model/Protocol.lean`: SA parameters and the shared engine with the
  slow-arming lease policy. Raw empty and vetoed gate results are saved.
- `Statements/Contract.lean`: `saInterface`, `saConstants`,
  `SAContract`, and the proof helper `HighParticipationBefore`.
- `Proofs/`: clean claims, both outage bounds, source support, recovery,
  and the complete bundle. `Tests/Smoke.lean` checks the lease rules;
  `Tests/Axioms.lean` audits the new public theorems.

The shared engine and proofs remain under `AvailableChainGridCO/`.
`LeasePolicy` defaults to Grid CO; SA selects `slowLeasePolicy`.
`RawHistory.lean` tracks saved local results. `LocalTransfer.lean`
handles the pending outage HEAD without assuming a covering lease.
`RecoveryRepair.lean` and `Recovery.lean` now expose admission-based
source support and common contract assembly. The grid instance retains
its original admission rule and `gridContract_from_engine` theorem.

## SA-PC: persistent TA certificates

`AvailableChain.SAPC.sapcContract_from_engine` in
`AvailableChainSAPC/Proofs/Contract.lean` proves the full Draft 4.3 bundle,
including SA-PC `fastP1_from_engine`. `sapcStrong_from_engine` in
`Proofs/StrongContract.lean` proves the additive strong companion.
Both require `G > 0` and `E.Δ = p.Δ`. No requested claim remains pending.
The base contract is unchanged. See [SA-PC status](SAPC-STATUS.md).

`Proofs/Hooks.lean` proves the E4 hook facts for `sapc p` (`excludes_inert`,
`excludes_stable`, `processed_stable`, `deps_stable`, `handles_carries`)
without an import of the framework. `excludes` stays `fun _ _ => false`
(`sapc_excludes`): SA-PC has no permanent refusal at the level of
`processed`, so this is the E4 classification. The file comment gives the
reasons. `sapcHooks` in `AvailableChainRegistry/Instances/SAPC.lean`
assembles them into `HooksSound (sapc p)`.

Recovery uses exact lease sources, SA's shared source-support induction,
and F4 transfer. `RecoveryBoundary` proves the two-lease support boundary;
`RecoveryRoots` and `RecoveryProposal` prove common exact proposal HEADs;
`RecoveryService`, `RecoveryGate`, and `RecoveryRepair` prove a common PC
and record repair within `2L+G+8Δ`. `RecoverySafety` proves the base safe
suffix. `RecoveryStrong` proves recovered strong safety and inclusion,
including late certificate reveals. The requested recovery cap follows
from the unchanged full-participation Recovery regime with `θrec = 2/3`.

The following implementation notes record the earlier proof rounds.
Their pending-work statements are historical; round 22 closes those gaps.

`State.base` reuses the Grid CO/SA engine. Complete signed HEADs and PC
metadata stay in the SA-PC archive and proposal store. Active choices add
F4 and mandatory finite roots. The gate gives each prefix its own PC
guard, with the lease loop outside the stable-record PC veto.

`Statements/Contract.lean` declares the base bundle, including fast P1,
and the strong companion with the requested constants. Current proofs
cover constants, nesting, local SA projections, signature provenance,
cap-test soundness and permanence, raw lease sources, and derivation of
the cap from Recovery. Timed receipt bounds, admitted path closure, exact
timely-save and freeze origins, save retention, and honest ack/preparation
sources are proved. `BaseArchive` connects cached keys to original signatures;
`TimelyDelivery` and `AckDelivery` connect delivered quorums to saves and
PC completion. `Assembly` proves archive-scan completeness. `CertificateRelay`
proves PC and cap-proof relay at the contract deadlines. `ActiveCounts`
bounds detected equivocators in base-cache and merged HEAD views without
an actual fault cap. `BaseViews` and `DeclaredSupport` prove archive sources,
label preservation, and support subsets for frozen and carried views.
`FrozenViews` connects ordinary saved views to their exact clock sources.
`Floor` proves the active declared-path witness and local F4 transfer;
`EffectiveScores` proves active q-score dominance over conflicting branches.
`Proposals` and `ProposalDelivery` prove actual emission, acceptance, and
path delivery before HEAD. `HeadTargets` and `HeadEmission` prove admitted
targets, slot bounds, complete honest HEAD emission, and target-path relay.
`ProposalViews` reuses the SA merge proofs to include the proposer's raw
and declared support keys in each HEAD view. `CertificateService` proves
PC completion before the 6Δ gate from exact preparations and extending
next HEAD choices under full participation at those duties and the cap.
`RecentArchive` supplies the base-key-or-equivocation alternative for
recent archived signatures. `TimelyTransfer` proves q-score transfer,
active next-HEAD coverage with compatible finite roots, and common
disablement after a compatible-root departure. `MergedReceipts` proves
reverse relay of the complete merged raw view. `QuorumGenuine` proves
same-label timely-N/genuine compatibility without a fault cap.
`EarlyReceipts` proves strict-cutoff presence from base stamps.
`GenuineTransfer` constructs the shared SA transfer interface for actual
SA-PC views, proves raw genuine compatibility at one label, and transfers
genuine prefixes to the actual next HEAD with explicit root premises.
Above-f support permits any selected PC; lower support uses selected-PC
compatibility. `TransferRegimes` derives relay premises from the fixed
synchronous and healthy-prefix conditions. Honest proposal choices and clean inclusion are proved in round 18.
Pending outage transfer and the complete bundle proofs remain open.
The clean root proofs are described below.
`Statements/CleanInvariant` now defines `cleanRunPath` from actual run
sources and `JointCleanInvariant` without a path argument. The old
conditional predicate is named `CleanPathFacts`. `RunCleanPath` and
`RunCleanTicks` prove the new initial, delivery, freeze, between-duty,
and capped proposal steps. `GenuineHistory` proves unconditional record,
saved-result, and finite-row source membership, plus finite-root
compatibility from ordered genuine history. Shared `HistoryInduction`
contains the extracted label induction used by both SA and SA-PC.
`Preservation` derives actual raw batch preservation from Sleepy and
honest HEAD coverage, reusing SA's confirmation theorem. Its
`clean_genuine_history_of_pc` leaves only active-PC compatibility as a
label-induction input. `CleanService` proves honest N/PC prefix witnesses
and exact raw proposal service from common exact HEADs. The clean safety
and 6Δ reductions consume the corrected invariant. The round-15 modules
below prove uncapped event preservation, safety, and monotonicity.
Round 18 completes common proposal choices and clean inclusion.

`Tests/CleanInvariantCounterexample` retains the complete capped Sleepy
run that refutes the round-9 arbitrary path-extension obligation. It also
checks that the new path excludes the losing sibling and contains the
actual next timely save. `Pending/RejectedCleanInduction` holds the old
statement, and `Pending/CleanInductionCounterexample` refutes it.
`Pending/CleanInduction` retains the historical exact proposal-choice
obligation and its round-18 proof. The event and PC-transfer obligations
are also discharged.
No pending module is imported by a default target. See the status document.

## Common model and contract

Draft 4.2 defines `BlockInRun` and `RootInjective` in
`AvailableChainStatements/Generic/Conditions.lean`. Sleepy, Outage, and
Recovery require this root premise; StableSleepy and Fast inherit it.
All witness runs satisfy it.

`CleanPCPath` proves capped PC membership in the canonical source path
and the strict selected-PC label bound. `RunCleanHeads` proves capped
HEAD/release preservation, including the final incomplete HEAD.
`RunCleanTransfer` derives timely continuation and a selected-PC prefix
of the pending genuine result without a following-gate horizon premise.
`MergedReceipts.local_back_receipts` and the factored genuine transfer
proof supply the local reverse receipt condition.
`RunCleanFacts` reconstructs source facts and restricts the capped
invariant to earlier prefixes. `RunCleanGates` proves source comparison,
ordered history, and the full capped early/gate step. `RunCleanCapped`
proves the capped run invariant and derives safety and monotonicity of
both base outputs under that cap. The round-15 induction removes the
cap for safety and monotonicity. Round 18 completes common proposal
choices; see `SAPC-STATUS.md`.

`Disabled` proves the full SA clock projection after disablement and
retains the joint invariant at the mode-changing receipt. `RunCleanHeads`
proves the uncapped disabled HEAD step. `RunCleanFacts` now reconstructs
and restricts source facts without the cap, using `q>a`. `RunCleanUncapped`
derives finite roots below timely saves from actual lease sources, proves
common disablement after departure, and proves first transfer for an
active gate PC. `RunCleanActiveTransfer` proves uncapped timely
continuation before an active input and selected-PC coverage of the pending raw result.
`RunCleanAuthority` retains continuation after disablement.
`RunCleanDisabledGates` proves the full disabled early/gate step;
`RunCleanActivePath` compares new and old sources at active ticks.
`RunClean` combines these steps into `clean_run_invariant` and
`clean_safety_from_engine`. Both base outputs have cross-reader safety
and local monotonicity under plain Sleepy, with no added fault cap.
Both P1 claims, strong claims, recovery, and both complete bundle
inhabitants remain pending. Round 18 completes proposal choices and inclusion.

Round 16 adds `ProposalOrigins`, `ProposalCounts`, `ProposalMerge`,
`ProposalTransport`, and `ProposalFloors`. These prove common proposal
participant counts, equivocation tests, declared-support scores, and
active F4 floors without a cap. The ordinary view transport reuses
`GridCO.ProposalViewTransport`. The shared GHOST transport proof now
also permits extra candidates whose scores are below the protected
path. Exact HEAD choices still need PC selection and finite-root
placement; common floors alone do not prove inclusion.

Round 17 adds `ProposalCertificates`, `ProposalAuthority`,
`ProposerTransfer`, `ProposalRoots`, and `ProposalHeads`. Frozen evidence
reaches the proposer, the carried live PC is valid at HEAD, and exact
selection retains the frozen encoding at equal rank. The selected rank
is common without a cap. Under plain Sleepy, active targets and F4
anchors are common. The shared SA receipt and GHOST proofs place finite
roots and active PC targets on the ordinary proposer walk and prove
that the honest proposal has that parent in either mode. A disabled
HEAD chooses the exact proposal, including when its proposer was active.
Round 18 completes active-tree eligible-path reflection and walk transport.

Round 18 adds `ProposalEligibility`, `Clean`, and `GateAdmission` and
extends `ProposalHeads`. The shared SA receipt interface gives a strict
non-equivocating majority in the proposer view. Common scores reflect
eligible old paths; authentication identifies the fresh proposal. The
shared adoption theorem now accepts extra ineligible paths, with its
original API retained. Exact active and disabled HEAD choices then give
both base inclusion claims under Sleepy and the StableSleepy and Fast
fields in `6Δ`, without a cap. The former pending proposal obligation has
a proof. Local gate lemmas establish first-prefix lease acquisition when
the raw descendant is PC-vetoed and preservation of an already protected
record prefix. Both run-level P1 claims still need the healthy-prefix and
pending-boundary proofs. Strong claims, recovery, and bundle assembly
also remain pending.

Round 19 adds `LeaseProtection`, `OutageProtection`, `GateRead`,
`HealthyBatch`, `SlowHistory`, `LocalTransfer`, and `PendingProtection`.
The shared `ProtectionInduction` supplies the same event induction and
public-read bridge for SA and SA-PC. Actual prefix leases persist until
their deadlines under arbitrary delivery and mode changes. Healthy early
batches give pending raw results and fast admission; immutable raw windows
give slow admission. Local pending HEAD transfer needs no relay or prior
lease. `pending_prefix_protection` combines these facts but still requires
healthy-prefix record and PC-authority premises. Neither contract P1 claim
is proved yet; strong claims, recovery, and the bundle inhabitants remain
pending. No contract or executable rule changed.

Round 20 completes both P1 claims in `Proofs/Outage.lean`:
`stable_resilient_from_engine` and SA-PC `fastP1_from_engine`. The shared
`RunPrefix` and `HealthyPrefix` proofs let `HealthyRun` reuse the uncapped
clean induction through a healthy cutoff equal to a gate. `HealthyHistory`
and `PendingAuthority` derive the pending finite and PC guards from actual
sources, with no cap. `RecordHistory` and `HealthyCoverage` connect stable
reads to healthy HEADs and records. The shared `History` field proof keeps
the original SA/Grid CO API. Slow-window and fast-count admission then
close the pending protection interface and both exact contract claims.

`StrongClean` proves `strong_safe_from_engine` and
`strong_included_from_engine` under the explicit cap. The proof orders PC
targets by preparation label and supplies exact `6Δ` PC service. Sound
arming, persistence with no budget, late-reveal protection, Recovery, and
the two bundle inhabitants remain pending. No contract or executable rule
changed. Earlier round summaries above describe their historical status.

```text
┌────────────────────────────┬────────────────────────────────────────────┬───────────────────────────────┐
│ Contract item              │ Lean name                                  │ File                          │
├────────────────────────────┼────────────────────────────────────────────┼───────────────────────────────┤
│ §2 time, environment       │ Time; Generic.Env                          │ M/Objects/Time; M/Generic/Env │
│ §2 protocol, wire objects  │ Generic.ProtocolSpec n; Signed; Auth;      │ M/Generic/Run;                │
│                            │ ProtocolSpec.Object                        │ M/Objects/Seats               │
│ §2 run and assignments     │ Generic.Run (seatOf, proposerOf);          │ M/Generic/Run                 │
│                            │ Run.holder                                 │                               │
│ §2 step, emission, sleep   │ World.step; Run.emittedAt; Run.emits       │ M/Generic/Run                 │
│ §2 signatures              │ UnforgeableSignatures                      │ S/Generic/Conditions          │
│ §2 delivery                │ PartialSynchrony; HealthyPrefixDelivery;   │ S/Generic/Conditions          │
│                            │ accepted-object relay                      │                               │
│ §2a K1, K6 seats per label │ Auth.seat; Run.seatOf : Label → Fin n ≃ V  │ M/Objects/Seats; M/.../Run    │
│ §2a K2 no identity         │ ProtocolSpec n has no V                    │ M/Generic/Run                 │
│ §2a K3 emission-neutral    │ World.step (tick = clock only)             │ M/Generic/Run                 │
│ §2a K4 unit seats          │ Env has no weights; counts in conditions   │ M/Generic/Env                 │
│ §2a K5 act once            │ duties_spec; duties_nodup; emittedAt       │ M/Generic/Run                 │
│ §3 interface               │ Interface; Output; readAt                  │ S/Generic/Interface           │
│ §4 participation, faults   │ awakeAt; awakeInClosed; faulty;            │ S/Generic/Conditions          │
│                            │ AwakeMajority; EtaSleepy;                  │                               │
│                            │ FullParticipation; BelowQuarter            │                               │
│ §4 proposer recurrence     │ HonestProposerRecurrence                   │ S/Generic/Conditions          │
│ §4 regimes                 │ SleepyRegime; StableSleepyRegime;          │ S/Generic/Regimes             │
│                            │ FastRegime; OutageRegime; FastOutageRegime │                               │
│                            │ RecoveryRegime                             │                               │
│ §5 properties              │ SafeFrom; MonotoneFrom; OutputOrder;       │ S/Generic/Properties          │
│                            │ HonestProposalAt; HonestAwakeProposer;     │                               │
│                            │ IncludedFrom; PersistsThrough              │                               │
│ §5 claims                  │ AvailableChain; RecoveredAt                │ S/Generic/Claims              │
│ §6 constants               │ Constants; Constants.Valid                 │ S/Generic/Constants           │
└────────────────────────────┴────────────────────────────────────────────┴───────────────────────────────┘
```

```text
┌──────────────────────────────────────────────────┬──────────────────────────────────────────────────────┐
│ Lean names                                       │ Source, and change                                   │
├──────────────────────────────────────────────────┼──────────────────────────────────────────────────────┤
│ Slot; BlockId; genesisRoot; Time                 │ Model/Objects/{Identifiers,Time}.lean; unchanged     │
│ Block and ancestry (preceq, prec, compatible)    │ Model/Objects/Blocks.lean; no proposer field, no V   │
│ Event; World; Run.stateBefore/…/final            │ Model/Generic/Run.lean; unchanged                    │
│ ProtocolSpec n                                   │ Generic/Run.lean ProtocolSpec V; new: no V, tick     │
│                                                  │ split into clock/act/propose/gossip, labels, slots   │
│ World.step                                       │ tick applies clock only (K3)                         │
│ Run                                              │ adds seatOf, proposerOf                              │
│ Run.emittedAt; emits                             │ recomputes emission from state, awake, assignments   │
│ Run.processes; handlesAt; acceptsAt              │ deliveries only; handles takes the delivered object  │
│ Env                                              │ Generic/Env.lean; electorate removed (unit seats)    │
│ Interface                                        │ Statements Interface; only outputs, block, opening   │
│ UnforgeableSignatures                            │ by holder of the authentication                      │
│ ExecutionValid                                   │ no sleep field: the engine gates emission            │
│ PartialSynchrony; HealthyPrefixDelivery          │ Statements Conditions.lean; unchanged                │
│ AwakeMajority; EtaSleepy; BelowQuarter           │ counts instead of weights                            │
│ HonestProposerRecurrence                         │ SingleProposerRecurrence; proposer awake             │
│ IncludedFrom                                     │ requires a proposal only from an awake honest        │
│                                                  │ proposer                                             │
│ Regimes, Claims, Properties (others)             │ Statements Generic; types adapted                    │
└──────────────────────────────────────────────────┴──────────────────────────────────────────────────────┘
```

`OutageRegime` uses `HealthyPrefixDelivery` only before `b₀`; it imposes no
delivery bound in `[b₀,b₁)`. Its two count premises apply from time zero,
including times before the protected read T. Draft 4.3 adds
`FastOutageRegime` and `stableResilientFast`, with the same persistence
conclusion and the fast arming lag. The witness also proves that fast
arming need not satisfy the general lag test.

## L* instance (definitions and statement; no claim proofs)

`LStar` below means `AvailableChain.LStar`. The pinned Goldfish source is
`../decoupled-consensus/verified-consensus/docs/PROTOCOL.md` §§2.1–2.3 and
`DecoupledConsensusModel/Protocol/`. The lock source is
`guarded-override.md` §§2, 3.1, 4.2, 10.1, with the checked list in
`lstar-recovery.md` §2.

```text
┌──────────────────────────────┬─────────────────────────────────────────────────────┐
│ Lean name                    │ Source rule                                         │
├──────────────────────────────┼─────────────────────────────────────────────────────┤
│ Params; proposalTime;        │ L* t_r, v_r, e_r, d_r, expiry; memory η           │
│ voteTime; earlyTime; gateTime│                                                     │
│ Msg; State; admitVote;       │ Goldfish HEAD, proposal view, vote/block handlers │
│ admitProposal; process       │                                                     │
│ resolvedBefore; proposerView;│ Goldfish resolution and previous-slot views        │
│ voterView; voterSupportView; │                                                     │
│ voterTree                    │                                                     │
│ goldfishScore; ghost;        │ Goldfish score, GHOST, eligibility, fork choice    │
│ goldfishEligible; forkChoice │                                                     │
│ earlyVotes; savedEarly;      │ L* early subtree snapshot, historical D and q    │
│ memoryDenominator; quorum    │                                                     │
│ confirmation; gate; clock   │ Genuine Goldfish gate; lock acquire/renew/expire  │
│ advance; stable; confirmed  │ L* separate S and G records and nested accessor   │
│ excludes                     │ E4 permanent refusals: an unprocessed HEAD whose    │
│                              │ seat equivocates; an unprocessed proposal wire      │
│                              │ whose block is stored (`admitProposal`)             │
│ Proofs/Hooks: excludes_inert;│ E4 hook facts for `lstar p n` (`HooksSound`         │
│ excludes_stable;             │ field shapes); exactness tests excludes_head_iff,   │
│ processed_stable;            │ excludes_proposal_iff, excludes_not_processed,      │
│ deps_stable; handles_carries │ excludes_second_wire                                │
│ Tests.smokeSecondWirePass    │ Second wire for a stored block is excluded          │
│ lstar; lstarInterface        │ Contract §2a ProtocolSpec and §3 interface        │
│ lstarConstants;              │ Contract §6, L* result constants and statement   │
│ LStarContract                │                                                     │
│ Tests.smokeRun; smokePass    │ Three honest HEADs, one silent faulty seat        │
└──────────────────────────────┴─────────────────────────────────────────────────────┘
```

The executable model is in `AvailableChainLStar/Model/Protocol.lean`; the
contract statement is in `AvailableChainLStar/Statements/Contract.lean`.
`Proofs/FastOutage.lean` derives fast P1 from a general P1 proof; the
general proof remains pending.
`Proofs/Hooks.lean` proves the E4 hook facts for `lstar p n` without an
import of the framework or Grid CO. `excludes` does not read the clock, so
`excludes_stable` does not use the schedule premise. `lstarHooks` in
`AvailableChainRegistry/Instances/LStar.lean` assembles them into
`HooksSound (lstar p n)`.
The `#eval` and `#guard` checks are in `AvailableChainLStar/Tests/Smoke.lean`.

## Witnesses (§2a K8, §7)

`AvailableChainWitnesses` is a Lake library and a default target. It does not
change the model or statement libraries.

```text
┌─────────────────┬───────────────────────────────────────────────────┬─────────────────────────────┐
│ Witness         │ Proved facts                                      │ File                        │
├─────────────────┼───────────────────────────────────────────────────┼─────────────────────────────┤
│ alwaysGenesis   │ Safety, monotonicity, and nesting for every run;  │ Witnesses/Sanity.lean       │
│                 │ a valid Sleepy run refutes inclusion for every D  │                             │
│ pooledLMD       │ Valid synchronous 2-honest/1-fault per label;     │ Witnesses/Accumulation.lean │
│                 │ spent B votes, late X votes, and a Y read reorg   │                             │
│ Regime premises │ Sleepy, StableSleepy (θ = 3/4), Fast, both Outage │ Witnesses/Regimes.lean      │
│                 │ regimes, Recovery; one fault and distinct views   │                             │
│                 │ one sleeping honest node where permitted          │                             │
└─────────────────┴───────────────────────────────────────────────────┴─────────────────────────────┘
```

The regime run relays an accepted object at time zero to all honest readers.
`acceptedRelayNonvacuous` records an active cross-reader deadline. A later
faulty object gives distinct honest views. The Recovery witness has an
actual honest proposal at slot 2. The
`RecoveryRegime` type does not require this: its recurrence can have no
windows if `proposerGap` exceeds the remaining horizon, and `opening` does
not require `propose` or `block` to return a value. A future contract decision
can strengthen that premise. No witness uses `native_decide`.

`Sanity.confirmedIncluded_claim_fails` states the failure for every integer
delay `D`. Its run has one honest, awake proposer and public ticks through
`max 1 (1 + D)`. The protocol always returns genesis and permanently excludes
all objects, which agrees with its state transition.

The accumulation witness models the vote pooling issue cited in
[RLMD-GHOST §1.2.1](https://arxiv.org/html/2302.11326v3). Labels 0, 1, and 2
act at times 0, 1, and 2. Their two honest seats vote for parent B, while
their faulty seat withholds a vote for hidden child X. At time 3, Y becomes
visible and both honest seats of label 3 vote for Y. The three X votes reach
both honest nodes at time 4. `WithheldFaultyVote` records a signing time equal
to each vote's act time, since faulty signing is outside `Run.emits`.
`noFaultySeatDeliveryEarly` proves that every
delivered faulty seat object arrives at or after its label's act time.
`honestParentVotes`, `honestVisibleVotes`, and `pooledCounts` prove the six
spent B votes, two Y votes, and three X votes. The tally counts every received
seat vote across labels and uses no validator identity. `attackSynchrony`
proves `PartialSynchrony` through the time-5 horizon, including relay of the
released X votes. `accumulationWitness` proves that an honest confirmed read
contains Y at time 3 and does not contain Y at time 4.

Fast has full honest participation from time zero. Recovery has an honest
sleeper before GST at time 1.

## Framework prototype (Phase 0)

`AvailableChainFramework` is a Lake library and a default target. It has
no protocol. It is a type-scanning catalog and certificate framework over
the contract (`AvailableChainStatements`). Its namespace is
`AvailableChain.Framework`. See [FRAMEWORK-DESIGN.md](FRAMEWORK-DESIGN.md)
§8 for the Phase 0 row, the accepted deviations and the lock change log.
Plan 1a (`docs/plans/2026-09-28-phase1a-gate-catalog.md`) added claim
domains, facets, shared profile constants, late triggers, the standard and
strong tiers, and the profiles `ac-4.3` and `strong-1`. Plan 1b
(`docs/plans/2026-09-29-phase1b-instances.md`) added the relation
`core_holdsAt_of_ac43`, the Grid CO, SA, SA-PC and L* instances in the
Registry, the row kind `profile-holds` and `docs/MATRIX.md`, and moved
the Kit out of this library. The tables below show the state after plan
1b. File paths below are relative to `AvailableChainFramework/`.

```text
┌───────────────────┬─────────────────────────────────────────────┬────────────────────────┐
│ Module            │ Contents                                    │ File                   │
├───────────────────┼─────────────────────────────────────────────┼────────────────────────┤
│ ClaimDomain       │ Validators (bundled V, DecidableEq,         │ ClaimDomain.lean       │
│                   │ Fintype); ClaimDomain (id, Inst, Ctx,       │                        │
│                   │ admissible, horizon): the instances that a  │                        │
│                   │ claim speaks about and their run contexts   │                        │
│ Hooks             │ Outcome (E4 classification); classify;      │ Hooks.lean             │
│                   │ HooksSound (5 fields: excludes_inert,       │                        │
│                   │ excludes_stable, processed_stable,          │                        │
│                   │ deps_stable, handles_carries)               │                        │
│ Instance          │ Instance (n, P, Δ, Δ_pos, iface, hooks);    │ Instance.lean          │
│                   │ V1Ctx (an environment and a v1 run);        │                        │
│                   │ ClaimDomain.v1                              │                        │
│ Claim             │ RefutationKind; ClaimSpec K (id, Const,     │ Claim.lean             │
│                   │ valid, le, le_refl, le_trans, Point,        │                        │
│                   │ regime, conclusion, trigger with a time H,  │                        │
│                   │ transport, refutable); holds; inhabited     │                        │
│                   │ (the trigger at a time of at least H)       │                        │
│ Cert              │ Cert; Refutation; RefutationFamily;         │ Cert.lean              │
│                   │ Cert.weaken; Cert.not_refuted;              │                        │
│                   │ Refutation.family_of (all over a claim      │                        │
│                   │ domain K)                                   │                        │
│ DomainMap         │ DomainMap K' K (an instance map and an      │ DomainMap.lean         │
│                   │ equivalence of contexts); ClaimSpec.pull;   │                        │
│                   │ holds_pull; inhabited_pull; Cert.pull;      │                        │
│                   │ ClaimDomain.ofV1; DomainMap.ofV1            │                        │
│ Facets/Strong     │ StrongInstance (extends Instance with the   │ Facets/Strong.lean     │
│                   │ strong output); StrongInstance.sface;       │                        │
│                   │ ClaimDomain.strong; DomainMap.strongV1      │                        │
│ Profile           │ Profile.Entry (a claim and the projection   │ Profile.lean           │
│                   │ of the shared constant); Profile K (id,     │                        │
│                   │ Shared, valid, entries); ProfileCert (one   │                        │
│                   │ shared constant, one certificate per entry  │                        │
│                   │ at its projection; Type 1);                 │                        │
│                   │ Profile.holdsAt; ProfileCert.holdsAt        │                        │
│ Pareto            │ stronger; pareto; pareto_sub; pareto_covers │ Pareto.lean            │
│                   │ (every constant is covered by a Pareto      │                        │
│                   │ constant)                                   │                        │
│ Catalog/Core      │ sleepy; safeOf; safeConfirmed; safeStable;  │ Catalog/Core.lean      │
│                   │ prefixOrder; includedConfirmed;             │                        │
│                   │ includedConfirmed_trigger_late; core (the   │                        │
│                   │ floor profile; Shared := Time, the D of     │                        │
│                   │ includedConfirmed); Candidate (Type 1);     │                        │
│                   │ not_candidate_of_family                     │                        │
│ Catalog/Meaning   │ meaning pins: <claim>_holds_iff and         │ Catalog/Meaning.lean   │
│                   │ <claim>_inhabited_iff for the four core     │                        │
│                   │ claims, in the Phase 0 form with L1         │                        │
│                   │ predicates only                             │                        │
│ Catalog/Mono      │ zeroConstants; the monotonicity lemmas that │ Catalog/Mono.lean      │
│                   │ the transport proofs use: etaSleepy_mono,   │                        │
│                   │ recurrence_mono, safeFrom_mono,             │                        │
│                   │ includedFrom_mono, and <regime>_mono for    │                        │
│                   │ StableSleepy, Outage, FastOutage, Recovery  │                        │
│                   │ and recoveredAt                             │                        │
│ Catalog/Standard  │ the standard tier over ClaimDomain.v1:      │ Catalog/Standard.lean  │
│                   │ EtaConst; OutageConst; RecoveryConst;       │                        │
│                   │ includedStable; includedStableFast;         │                        │
│                   │ persistOutage; persistOutageFast;           │                        │
│                   │ recovered; persistTrigger; for each claim   │                        │
│                   │ <claim>_le_trans, <claim>_transport and     │                        │
│                   │ <claim>_trigger_late;                       │                        │
│                   │ <claim>_no_witness_at_zero_budget for the   │                        │
│                   │ two persistence claims                      │                        │
│ Catalog/Strong    │ the strong tier over ClaimDomain.strong:    │ Catalog/Strong.lean    │
│                   │ StrongIncConst; StrongRecConst;             │                        │
│                   │ StrongRecIncConst; strongSafe;              │                        │
│                   │ strongIncluded; strongPersist;              │                        │
│                   │ strongRecoveredSafe;                        │                        │
│                   │ strongRecoveredIncluded;                    │                        │
│                   │ strongIncludedTrigger; for each claim       │                        │
│                   │ <claim>_le_trans and <claim>_transport;     │                        │
│                   │ <claim>_trigger_late for each claim with a  │                        │
│                   │ trigger other than True                     │                        │
│ Catalog/Profiles  │ the five regime adapters                    │ Catalog/Profiles.lean  │
│                   │ (stableSleepyRegime_iff, outageRegime_iff,  │                        │
│                   │ fastOutageRegime_iff, recoveryRegime_iff,   │                        │
│                   │ recoveredAt_iff); ac43 (ac-4.3:             │                        │
│                   │ Shared := Constants, nine claims); ac43_iff │                        │
│                   │ (↔ AvailableChain); ac43_valid_cross;       │                        │
│                   │ strong1 (strong-1:                          │                        │
│                   │ Shared := Constants × StrongConstants, five │                        │
│                   │ claims); strong1_iff (↔ StrongClaims)       │                        │
│ Catalog/Relations │ relations between profiles (plan 1b Task    │ Catalog/Relations.lean │
│                   │ 4): core_holdsAt_of_ac43 (ac-4.3 holds at C │                        │
│                   │ → core holds at D := C.D_c)                 │                        │
└───────────────────┴─────────────────────────────────────────────┴────────────────────────┘
```

Plan 1b Task 0 moved `Kit/Core` and `Engine/V2Sketch` out of this
library, to `AvailableChainKit` and `AvailableChainEngineV2` (see "Kit
and engine v2 sketch"). `AvailableChainFramework` does not import them.
Note (2026-09-29, Phase 2a gate): the Sketch is deleted. The Framework now
imports `AvailableChainEngineV2` for one module, `V2/Anchor.lean` (see
"Engine v2 and Kit v2 (Phase 2a)"). It does not import `AvailableChainKit`
or `AvailableChainKitV2`.

A claim domain (`ClaimDomain`) names the type of the instances that a
claim speaks about and the type of their run contexts. `ClaimSpec K`,
`Cert`, `Refutation` and `Profile K` are generic over the claim domain
`K`. The v1 claim domain `ClaimDomain.v1` has `Instance` and `V1Ctx`. A
facet is a structure that extends `Instance`, with its own claim domain
and a `DomainMap` to v1 (`Facets/Strong.lean`). A base claim and its
certificates pull back along the map (`ClaimSpec.pull`, `Cert.pull`).

The five regime adapters of the profiles are in `Catalog/Profiles.lean`,
not in `Catalog/Mono.lean`. `Catalog/Mono.lean` has only the monotonicity
lemmas that the `transport` proofs use.

`AvailableChainRegistry` is a Lake library and a default target. It holds
protocol instances over the framework, their certificates and refutations,
and compile-only tests. Its namespace is `AvailableChain.Registry`. File
paths below are relative to `AvailableChainRegistry/`.

```text
┌──────────────────┬─────────────────────────────────────────────┬───────────────────────┐
│ Module           │ Contents                                    │ File                  │
├──────────────────┼─────────────────────────────────────────────┼───────────────────────┤
│ Sanity           │ sanity (the Sanity instance); hooks;        │ Sanity.lean           │
│                  │ certSafeConfirmed; certSafeStable;          │                       │
│                  │ certPrefix; refutedIncluded                 │                       │
│                  │ (RefutationFamily); not_candidate           │                       │
│ Tests/Pareto     │ armedToy (a two-constant test claim: an     │ Tests/Pareto.lean     │
│                  │ arming lag and a budget); the Pareto        │                       │
│                  │ direction example                           │                       │
│ Tests/NewFacet   │ counterStrong (Counter with its stable      │ Tests/NewFacet.lean   │
│                  │ output as the strong output);               │                       │
│                  │ certSafeStableStrong (a pulled base         │                       │
│                  │ certificate); testStrongSafe (a test claim  │                       │
│                  │ with its own id); badStrong;                │                       │
│                  │ refutedBadStrong; refutedBadStrongSafe;     │                       │
│                  │ certStrongSafeCounter (a strong-tier        │                       │
│                  │ certificate)                                │                       │
│ Instances/       │ gridHooks (HooksSound (gridCO p)), from the │ Instances/            │
│ GridCOHooks      │ hook facts in AvailableChainGridCO/Proofs/  │ GridCOHooks.lean      │
│                  │ Hooks.lean; SA uses @gridHooks              │                       │
│                  │ slowLeasePolicy p.engine                    │                       │
│ Instances/GridCO │ gridInst (Grid CO, default lease policy);   │ Instances/GridCO.lean │
│                  │ grid_holds, grid_holds_core (G = 1) and     │                       │
│                  │ their _of_pos forms (0 < G): ac43 and core  │                       │
│                  │ holdsAt, not certificates                   │                       │
│ Instances/SA     │ saInst (hooks: @gridHooks slowLeasePolicy   │ Instances/SA.lean     │
│                  │ p.engine); sa_holds, sa_holds_core (G = 1)  │                       │
│                  │ and their _of_pos forms                     │                       │
│ Instances/SAPC   │ sapcHooks (HooksSound (sapc p)); sapcInst   │ Instances/SAPC.lean   │
│                  │ (a StrongInstance); sapc_holds_ac43,        │                       │
│                  │ sapc_holds_strong1, sapc_holds_core (G = 1) │                       │
│                  │ and their _of_pos forms; sapc_holds_shared  │                       │
│                  │ (ac43 and strong1 at one C)                 │                       │
│ Instances/LStar  │ lstarHooks (HooksSound (lstar p n));        │ Instances/LStar.lean  │
│                  │ lstarInst; no holdsAt theorem (L* has no    │                       │
│                  │ contract proof)                             │                       │
│ Counter          │ counter (a toy height protocol);            │ Counter.lean          │
│                  │ counterIface; counter_hooks; counterInst    │                       │
│ CounterRun       │ canonical (the synchronous run from         │ CounterRun.lean       │
│                  │ genesis); canonical_execution;              │                       │
│                  │ canonical_synchrony; canonical_relay;       │                       │
│                  │ canonical_sleepy; certSafeConfirmed;        │                       │
│                  │ certSafeStable; certPrefix                  │                       │
│ CounterIncluded  │ counter_included (exact-time inclusion at   │ CounterIncluded.lean  │
│                  │ D = 1); certIncluded (a proposal slot at a  │                       │
│                  │ time of at least H); candidate (Counter     │                       │
│                  │ passes the core floor at D = 1)             │                       │
│ Gaps/NoInput     │ KNOWN GAP I1: clockChain (reads no input);  │ Gaps/NoInput.lean     │
│                  │ clockInst; certSafeConfirmed;               │                       │
│                  │ certSafeStable; certPrefix; certIncluded;   │                       │
│                  │ clockCandidate (passes the core floor at    │                       │
│                  │ D = 0)                                      │                       │
└──────────────────┴─────────────────────────────────────────────┴───────────────────────┘
```

```text
┌────────────────────────────────────┬──────────────────────────────────────────┬─────────────────────┐
│ Script                             │ Check                                    │ Exit codes          │
├────────────────────────────────────┼──────────────────────────────────────────┼─────────────────────┤
│ scripts/CatalogLock.lean --check   │ compares the locked declarations with    │ 0 same, or ADDED    │
│ [--lock <path>]                    │ the lock by name; prints REMOVED,        │ lines only; 1 a     │
│                                    │ CHANGED and ADDED lines; also checks the │ REMOVED or CHANGED  │
│                                    │ axioms of each locked declaration and    │ line; 2 a usage     │
│                                    │ that no two claims have one id           │ error, a bad lock   │
│                                    │                                          │ line, a missing     │
│                                    │                                          │ declaration, a bad  │
│                                    │                                          │ axiom or two claims │
│                                    │                                          │ with one id         │
│ scripts/CatalogLock.lean --write   │ writes the lock; refuses a REMOVED or    │ 0 written; 1        │
│ [--allow-changes] [--lock <path>]  │ CHANGED line unless --allow-changes is   │ refused, nothing    │
│                                    │ given                                    │ written; 2 as for   │
│                                    │                                          │ --check             │
│ scripts/Registry.lean [--check |   │ writes docs/REGISTRY.md and              │ 0 written, or the   │
│ (--selftest | --selftest-write)    │ docs/MATRIX.md; with --check, compares   │ same; 1 different;  │
│ <file> [<module>]]                 │ both texts with the files, names each    │ 2 a usage error, an │
│                                    │ file that differs and writes nothing;    │ unreadable file, a  │
│                                    │ with --selftest, prints the rows and     │ bad family witness, │
│                                    │ MATRIX cells of one Lean file (not a     │ or a self-test file │
│                                    │ scanned library) and compares them with  │ that does not       │
│                                    │ its .expected file; --selftest-write     │ elaborate           │
│                                    │ writes that file                         │                     │
│ scripts/CheckFrameworkAxioms.lean  │ every constant of                        │ 0 clean; 1 a bad    │
│                                    │ AvailableChainFramework,                 │ axiom; 2 nothing    │
│                                    │ AvailableChainRegistry,                  │ found or a usage    │
│                                    │ AvailableChainKit and                    │ error               │
│                                    │ AvailableChainEngineV2 uses only         │                     │
│                                    │ propext, Classical.choice, Quot.sound    │                     │
│                                    │ (this rejects sorryAx and the axioms of  │                     │
│                                    │ native_decide); reads built data         │                     │
└────────────────────────────────────┴──────────────────────────────────────────┴─────────────────────┘
```

`scripts/Registry.lean` scans the libraries in `instanceLibraries` (now
only `AvailableChainRegistry`) for constants whose type is `Cert c I`,
`Refutation c I`, `RefutationFamily c I`, `ProfileCert p I`, `Candidate I`
or `Profile.holdsAt p I C`, and writes one row per constant to
`docs/REGISTRY.md`. The file header names the scanned libraries. A
`ProfileCert` or `Candidate` row has the kind `profile-cert`, and its
claim column shows the profile `id` (for example `core.v1`) and then the
row's constant as `at C = <term>` (for `profile-holds`, the argument `C`;
for `profile-cert`, the field `shared` of the value). A certificate of a
pulled claim shows the base claim with `(pulled)`. A type behind leading
binders (`∀ …, Cert c I`) is CONDITIONAL and is still written as a row,
with status `CONDITIONAL (not a certificate)`: it is a row of the table,
not a certificate. A row of kind `profile-holds` (a `holdsAt` theorem)
proves the claim propositions at one constant, without inhabitation; it
can be vacuous, and it is not a certificate. Such a row is a FAMILY, with
the status suffix ` (family)`, only if its binder telescope has exactly
one binder and that binder's type is syntactically in `familyBinders`
(`GridCO.Params`, `SA.Params`, `SAPC.Params`) and the instance argument
uses that binder (`gridInst p`); the script checks that each type's
witness exists, is not `unsafe`, has that type and uses only the allowed
axioms. A family row, and a row without binders, has status `LEAN` only if
`Lean.collectAxioms` finds no axiom outside `propext`, `Classical.choice`,
`Quot.sound`; any other axiom (including `sorryAx`) gives status
`UNSOUND(<axiom names>)`. An `unsafe` declaration has status
`UNSOUND(unsafe)`. A row of a module under `AvailableChainRegistry.Gaps`
has status `KNOWN-GAP` in place of `LEAN` (plan 1a Task 0, `gapsPrefix`).
A row's claim column keeps the claim's name and appends `NON-CATALOG` if
the `ClaimSpec` is not declared in a module under
`AvailableChainFramework.Catalog`. The instance column looks through a
parent projection to an instance type, so `(sapcInst p).toInstance` shows
`sapcInst`. It shows the head constant of an instance that depends on a
binder (`gridInst p` shows `gridInst`), and the full term of a closed
instance (`gridInst smokeParams`), which then gets its own MATRIX line.
The same run writes `docs/MATRIX.md`: one line per instance constant, one
column per catalog claim and per catalog profile; its header gives the
meaning of each cell (`holds*` for a family row; `gap` and `cond` are
records, not results), and a list under the table names each row without a
cell. The self-test files in `scripts/registry-selftest/` (not a Lake
library) check the family rule and the MATRIX cell rule; `--selftest`
compares their output with the committed `.expected` files, and their
`README.md` gives the commands and the expected statuses.
`docs/REGISTRY.md` and `docs/MATRIX.md` are generated; do not edit them by
hand.

`scripts/CatalogLock.lean` locks every declaration that Lean did not
generate in the modules `Hooks`, `Instance`, `Claim`, `Cert`, `Profile`,
`Pareto`, `ClaimDomain` and `DomainMap` of `AvailableChainFramework`, and
in every module under `.Catalog` and `.Facets`. It also locks every
declaration of the library whose type is a `ClaimSpec`, a `Profile`, a
`Profile.Entry` or a `ClaimDomain`. The hash of a line is a hash of the
set of declarations that the locked declaration reaches (its closure), in
a fixed order. Thus a new declaration does not change the line of an old
declaration that does not reach it. A theorem hashes its statement only,
so a new proof of the same statement keeps the hash (design deviation (e),
`FRAMEWORK-DESIGN.md` §8). For this reason, each new claim puts its
`transport` and `le_trans` proofs in named theorems. `Kit` is not locked.
The default lock file is `docs/catalog.lock`. Run `--check` after a build,
because the script reads the built `.olean` files.

`scripts/CheckFrameworkAxioms.lean` also reads built data. Run all three
scripts with `lake env lean --run scripts/<file>.lean` after `lake build
AvailableChainFramework AvailableChainRegistry AvailableChainKit
AvailableChainEngineV2`.

## Kit and engine v2 sketch (plan 1b)

Plan 1b Task 0 (`docs/plans/2026-09-29-phase1b-instances.md`) moved the
engine-generic lemmas and the Framework Kit into the library
`AvailableChainKit` (L5), and the engine v2 sketch into the library
`AvailableChainEngineV2` (L0). Both are Lake libraries and default
targets. No name and no namespace changed; only file paths and imports
changed. `AvailableChainKit` imports only `AvailableChainModel`,
`AvailableChainStatements`, Mathlib and its own modules.

```text
┌──────────────────────────────┬──────────────────────────────────────────┬──────────────────────────────────────────┐
│ Module                       │ Contents                                 │ Moved from                               │
├──────────────────────────────┼──────────────────────────────────────────┼──────────────────────────────────────────┤
│ AvailableChainKit.Core       │ namespace AvailableChain.Framework.Kit:  │ AvailableChainFramework/Kit/Core.lean    │
│                              │ block_preceq_trans;                      │                                          │
│                              │ includedPersist_of_safe (a derived       │                                          │
│                              │ lemma, not a claim)                      │                                          │
│ AvailableChainKit.Engine.    │ namespace AvailableChain.Engine: the     │ AvailableChainGridCO/Proofs/Execution    │
│ Execution                    │ schedule bridges (stateBefore_succ_event,│ (the engine part; the Grid CO forms stay │
│                              │ readAt_eq_stateBefore, …)                │ in Grid CO Proofs/Execution.lean)        │
│ AvailableChainKit.Engine.    │ ClockLaws; now bounds; invariants;       │ AvailableChainGridCO/Proofs/EngineClock  │
│ EngineClock                  │ stateBefore_stable_clock (plan 1b, new)  │                                          │
│ AvailableChainKit.Engine.    │ runPrefix and its read lemmas            │ AvailableChainGridCO/Proofs/RunPrefix    │
│ RunPrefix                    │                                          │                                          │
│ AvailableChainKit.Engine.    │ prefixEnv; healthyPrefix_* regime        │ AvailableChainGridCO/Proofs/HealthyPrefix│
│ HealthyPrefix                │ transfer                                 │                                          │
│ AvailableChainKit.Engine.    │ genesisEnv; healthyInterior_sleepy       │ AvailableChainGridCO/Proofs/             │
│ HealthyInterior              │                                          │ HealthyInterior                          │
│ AvailableChainKit.Engine.    │ state_interval_induction;                │ AvailableChainGridCO/Proofs/             │
│ ProtectionInduction          │ read_field_eq_clock                      │ ProtectionInduction                      │
│ AvailableChainKit.Engine.    │ clock_field_origin_since                 │ AvailableChainGridCO/Proofs/             │
│ SourceHistory                │                                          │ SourceHistory                            │
│ AvailableChainKit.Engine.    │ stateBefore_stable (a state property     │ AvailableChainRegistry/GridCOHooks.lean  │
│ Stable                       │ that clock and process keep holds for    │ (was AvailableChain.Registry.GridCO)     │
│                              │ the rest of the run)                     │                                          │
│ AvailableChainEngineV2.      │ namespace AvailableChain.Framework.      │ AvailableChainFramework/Engine/          │
│ Sketch                       │ V2Sketch: SpecV2; Isolated (E5);         │ V2Sketch.lean                            │
│                              │ Restorable (E6); tickV2; restartV2;      │                                          │
│                              │ toyV2 (a two-field toy spec)             │                                          │
└──────────────────────────────┴──────────────────────────────────────────┴──────────────────────────────────────────┘
```

`stateBefore_stable` is the only moved declaration with a new full name:
its namespace is now `AvailableChain.Engine`. `time_le_of_key_le` and
`filter_false_of_index_ge` in `Engine/Execution.lean` are no longer
private, because the Grid CO part of `Execution.lean`, now in another
file, uses them. Grid CO's private `block_preceq_trans` (`Map.lean`) and
the Kit's `block_preceq_trans` have different statements; both stay.

## Engine v2 and Kit v2 (Phase 2a)

Phase 2a (`docs/plans/2026-09-29-phase2a-engine-v2-core.md`) wrote engine
v2 in the library `AvailableChainEngineV2` (L0; namespace
`AvailableChain.V2`) and its lemmas in the new library
`AvailableChainKitV2` (L5; namespace `AvailableChain.V2.Engine`). Both are
default targets. The engine imports only Mathlib, the model modules
`Objects.Identifiers`, `Objects.Time`, `Objects.Blocks` and
`Generic.Env`, and its own modules. The Kit also imports the engine. Tests
are in the namespaces `AvailableChain.V2.Tests`,
`AvailableChain.V2.Tests.Toy` and `AvailableChain.V2.Engine.Tests`.
`docs/V2-API.md` is the frozen API manifest (280 entries);
`scripts/V2Manifest.lean --check` checks it. The design note is
[FRAMEWORK-DESIGN.md](FRAMEWORK-DESIGN.md) §2, "As implemented in Phase 2a";
the report is [PHASE2A-REPORT.md](PHASE2A-REPORT.md). One row per module:

```text
┌──────────────────────────────────────────────┬─────────────────────────────────────────────────────────────────────────────────┐
│ Module                                       │ Contents                                                                        │
├──────────────────────────────────────────────┼─────────────────────────────────────────────────────────────────────────────────┤
│ AvailableChainEngineV2.Engine.Objects        │ Auth (seat ℓ i | none); Signed (auth, payload); derived DecidableEq, Repr       │
│ AvailableChainEngineV2.Engine.Spec           │ ProtocolSpec (In : Type) (24 fields); ProtocolSpec.Object; objSelfVisible       │
│ AvailableChainEngineV2.Engine.Run            │ Event; World; Run; tick; World.step; stateBefore; emitsAt, emittedAt, emits     │
│ AvailableChainEngineV2.Conditions.Schedule   │ ScheduleWellFormed … ExecutionValid; NoRestart; restartFree; SelfDelivery       │
│ AvailableChainEngineV2.Conditions.Committees │ LabelFamilies (ap, fresh, linked); CStar; Linked; SingleSeat; Linked.toCStar    │
│ AvailableChainEngineV2.Conditions.Delivery   │ PartialSynchrony, HealthyPrefixDelivery (broadcast, relay; exclusion exemption) │
│ AvailableChainEngineV2.Conditions.Interface  │ Interface (propLabel_injective); proposerOf; outputAt; RootInjective            │
│ AvailableChainEngineV2.Laws.Isolation        │ LabelFamilies.APObject; Isolation (factors, hooks_base, separation); base_tick  │
│ AvailableChainEngineV2.Laws.Hooks            │ HooksSound (v1 fields on restartFree intervals; three recordOwn laws)           │
│ AvailableChainEngineV2.Laws.Outputs          │ OutputsFactor (confirmedB, stableB); confirmed_tick, stable_tick                │
│ AvailableChainEngineV2.Laws.SelfDelivery     │ EmitOk; selfDelivery_admissible; ExecutionValid.snoc_selfDelivery               │
│ AvailableChainEngineV2.Tests.*               │ Engine, Conditions, Laws, Interface: tests of Tasks 1, 2, 3 and 5               │
│ AvailableChainKitV2.ClockLaws                │ ClockLaws (v1 fields and recordOwn_now); now_tick                               │
│ AvailableChainKitV2.Execution                │ schedule bridges: readAt_eq_stateBefore, tick_index_lt_delivery, …              │
│ AvailableChainKitV2.EngineClock              │ clock and field lemmas with the D9 premises; _restore and _noRestart forms      │
│ AvailableChainKitV2.Stable                   │ stateBefore_stable (recordOwn premise, restartFree); tick_preserve              │
│ AvailableChainKitV2.Emission                 │ mem_tick_seat_iff; emits_bijSeat; linked_index_stable; ownRecord_fold           │
│ AvailableChainKitV2.RunCheck                 │ allTicks, allDeliveries, emittedBy and their _spec lemmas (finite checks)       │
│ AvailableChainKitV2.Tests.Counterexamples    │ check_a … check_c (the D9 and A03 premises are necessary); check_d (Unit)       │
│ AvailableChainKitV2.Tests.Toy                │ toy protocol; toyRun (ExecutionValid, self-delivery); pre (append form)         │
│ AvailableChainFramework.V2.Anchor            │ anchor: a let chain over the 224 engine entries; one locked line                │
└──────────────────────────────────────────────┴─────────────────────────────────────────────────────────────────────────────────┘
```

The gate deleted `AvailableChainEngineV2.Sketch` (64a48cd). The laws of
`Laws/Isolation` and `Laws/Outputs` replace its shapes.

## Generic library (A0 step 2)

`AvailableChainGeneric` is a default library for the shared Pure, V2 and AC
layers. Its namespaces are `AvailableChain.Gen.Pure`, `.V2` and `.AC`.
`Run.idxBefore` and `Run.nthIdx?` extend `AvailableChain.V2.Run` (D03).
Statements expose definitions, closed `...Statement : Prop` declarations and
`f_def` lemmas. Proofs do not expose proof bodies. Step 3 proves E-9; deferred
walk and gate proofs remain. The facade `AvailableChainGeneric.lean` imports
the Statements and Proofs modules. The table below lists their main roles.
Library globs build Tests; the facade excludes Tests. Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌──────────────────────────┬──────────────────────────────────────────────┐
│ Module                   │ Role                                         │
├──────────────────────────┼──────────────────────────────────────────────┤
│ Statements/Pure/Quorum   │ qF; FaultQ, FaultX and Batch bounds          │
│ Statements/Pure/FirstBad │ AGRule, FirstFailure, WindowRule, RetroAt    │
│ Statements/Pure/Schedule │ Patterns, recurrence and window definitions  │
│ Statements/Pure/Walk     │ Suffix premises and E-4 walk statements      │
│ Statements/Pure/Props    │ CompatOn/At, MonoOn, BelowOn, ServedOn       │
│ Statements/V2/Reads      │ Run indices, pubFloor, HonestSlot, Pending   │
│                          │ E-9 time/index statement PROVED              │
│ Statements/V2/Counts     │ faulty and awakeHonest                       │
│ Statements/V2/Obs        │ Time observations with optional proposals    │
│ Statements/V2/Interface  │ FinalityInterface extends the v2 interface   │
│ Statements/V2/Receipt    │ DeliveryWithin; E-9 statements PROVED        │
│ Statements/V2/Regimes    │ Regime cores, LabelSync, LabelFacts, SeedAt  │
│ Statements/V2/Signatures │ G12 emission and honest uniqueness           │
│ Statements/AC/Reads      │ ACReads, ACLaws, gate and reconcile reads    │
│ Proofs/Pure/FirstBad     │ Strong induction for the FirstBad rules      │
│ Proofs/Pure/Schedule     │ Pattern, window and recurrence facts         │
│ Proofs/Pure/BlockOrder   │ Block order, compatibility and path facts    │
│ Proofs/V2/Fields         │ ownRecord_fold_restart                       │
│ Proofs/V2/Reads          │ E-9 time/index bridge                        │
│ Proofs/V2/Induction      │ Invariant and interval lifts; kept_from_seed │
│ Proofs/V2/Receipt        │ E-9 proofs; two DeliveryWithin producers     │
│ Proofs/V2/Regimes        │ Six LabelSync and LabelFacts facts           │
│ Proofs/V2/Signatures     │ G12 proofs; no receipt-window premise        │
│ Proofs/AC/Output         │ output_step_of_restartFree                   │
│ Tests/Axioms             │ Kernel axiom audit of every public theorem   │
│ Tests/FoldRestart        │ Two special cases of the restart fold        │
│ Tests/Schedule           │ Window-bound and recurrence examples         │
└──────────────────────────┴──────────────────────────────────────────────┘
```

`docs/GEN-API.md` records the Statements types and values. Run
`lake env lean --run scripts/V2Manifest.lean --scope gen --check` after a build.
Before G-F0a, a Statements edit updates this manifest in the same commit;
from G-F0a it is append-only (D15). `docs/LEAN-ARCHITECTURE.md` gives the layer
rules. The CatalogLock and v2 manifest remain separate checks.

`bash scripts/check-build.sh` runs checks (a)–(i) after a full build:

```text
┌───────┬─────────────────────────┬──────────────────────────────────────────┐
│ Check │ Script (scripts/)       │ Rule                                     │
├───────┼─────────────────────────┼──────────────────────────────────────────┤
│ (a)   │ check-module-headers.py │ module headers and public imports        │
│ (b)   │ check-expose.py         │ Proofs expose only allowed definitions   │
│ (c)   │ rebuild-cone-test.sh    │ A proof-only edit rebuilds one module    │
│ (d)   │ CheckProofEqns.lean     │ Proofs export no new equation lemmas     │
│ (e)   │ check-layers.py         │ Module imports follow the layer rules    │
│ (f)   │ shake-report.sh         │ Unused imports; report only, no --fix    │
│ (g)   │ chain-depth.py          │ Longest import chain; report only        │
│ (h)   │ check-transparency.py   │ Transparency option position and reasons │
│ (i)   │ check-gly-rules.sh      │ GLY rules and per-rule baselines         │
└───────┴─────────────────────────┴──────────────────────────────────────────┘
```

## Simplex FG module (DC-fj)

The FG module `SimplexFG.fj` is DC's FG without SG and grades, with the FJ
root rule in place of NJ. Its plan is `docs/plans/2026-09-28-fg-module.md`;
its registry is `docs/FG-COMPOSITION.md`. Both libraries are default
targets. The module does not import the framework, the engine, or an AP.
`AvailableChainKitFG/Pins.lean` records the coverage of each registry id
clause by clause (Lean names and extra hypotheses, or the paper step, the
registry id, or the AP fact that carries the clause).

```text
┌─────────────────────────┬──────────────────────────────────────────┬─────────────────────────────┐
│ Library                 │ Contents                                 │ Namespace                   │
├─────────────────────────┼──────────────────────────────────────────┼─────────────────────────────┤
│ AvailableChainSimplexFG │ LM, definitions and decide examples      │ AvailableChain.SimplexFG    │
│                         │ only: rows and blocks, the chain state   │                             │
│                         │ with no NJ height, E1/E2 evidence, the   │                             │
│                         │ FG client, the DC-fj store (one          │                             │
│                         │ cumulative admitted tree, on_block,      │                             │
│                         │ update_finality, activeView), the FJ     │                             │
│                         │ controls, filteredFrom, fjFrame          │                             │
│ AvailableChainKitFG     │ L5, definitions and proofs: certificates, │ AvailableChain.KitFG        │
│                         │ pinned FG lemmas (fg.* and fj.* ids),    │                             │
│                         │ the store invariant and store controls,  │                             │
│                         │ and the pin table (Pins.lean)            │                             │
└─────────────────────────┴──────────────────────────────────────────┴─────────────────────────────┘
```

Step 2 adds the following modules and E-15 facts. Paths are relative to
`AvailableChainKitFG/`; the facade imports all four modules.

```text
┌──────────────────────────┬─────────────────────────────────────────────────────────────────┐
│ Module                   │ Role                                                            │
├──────────────────────────┼─────────────────────────────────────────────────────────────────┤
│ StoreInvDef.lean         │ StoreInv moved from Correspondence with its name and fields     │
│ ViewLock.lean            │ ViewLock and f_def; blocks strictly above the height extend Fb  │
│ HonestRows.lean          │ HonestRows: emission, no slashing, and the row height cap       │
│ Certificates.lean (E-15) │ Row commutativity/idempotence; folds and transitions by row set │
└──────────────────────────┴─────────────────────────────────────────────────────────────────┘
```

`StoreInvDef`, `ViewLock` and `HonestRows` are definition modules with
`@[expose] public section`; `scripts/baselines/kitfg-def-modules.txt` lists them.

C1 adds the view producer below. The root imports both production modules.
`ViewLockChainsDef` is also in the definition-module list. The Tests glob
builds the regression and axiom audit with `AvailableChainKitFG`.

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Module (KitFG/)            │ Role                                                         │
├────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ ViewLockChainsDef.lean     │ Closed chain and honest-chain Statements; complete _def      │
│ ViewLockChains.lean        │ ViewLock from chain agreement or a strict fault weight bound │
│ Tests/ViewLockChains.lean  │ Both producers; sibling at the strict threshold; one fault   │
│ Tests/Axioms.lean          │ Kernel dependencies of both equations and producer proofs   │
└────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

Both producers use the accepted carrier's `h_F` and the strict comparison
`θ < hOf E cfg W`. The honest form needs only `noSlash` on the two chains.
DC: `ChainState/FinalityComparison.lean:50–56`; same strict comparison and
finalized ancestry. Root collision freedom is a theorem here because roots
identify content (`Accountable.lean:15–18`; GLY:57–58, intentional).

C4 adds the exact lower-F removal set. The root imports the Def module and
`TwoChanges`; the Tests glob builds the regression and axiom audit.

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Module (KitFG/)            │ Role                                                         │
├────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ LowerFDomainDef.lean       │ Closed LowerFDomainIdentityStatement and complete _def       │
│ TwoChanges.lean            │ lowerF_domain_identity; reuses Fmove_filtered                │
│ Tests/LowerFDomain.lean    │ Strict-ancestor removal; F′ retained; top-J domain equality  │
│ Tests/Axioms.lean          │ Kernel dependencies of the equation and the removal proof    │
└────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

`LowerFDomainDef` is in the definition-module list. The proof uses
`preceq_refl` and `preceq_antisymm` to make the removal criterion exact.
DC: none; INTENTIONAL addition: FJ phase-dependent domain; record
`blueprint/21-healing.md:691–694, 2579–2581`.

C2 adds G20 chain bit persistence and forward row occurrence. The root imports
both modules. `RowBitsDef` is in the definition-module list. The Tests glob
builds the regression tests and the axiom audit.

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Module (KitFG/)            │ Role                                                         │
├────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ RowBitsDef.lean            │ Three bit kinds, keys, matching, closed Statements and _def  │
│ RowBits.lean               │ Forward fold coverage; chain persistence; row-to-bit proof  │
│ Tests/RowBits.lean         │ All kinds; timeout progress; finality consumption and resets │
│ Tests/Axioms.lean          │ Kernel dependencies of the equations and bit proofs         │
└────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

Equal endpoint keys exclude resets because height and justification height
cannot decrease. A justification write strictly raises `h_j`; finality
consumption keeps `finalize`. No reverse claim identifies a row from a bit.
`bit_fold_covered` supplies the target-fold coverage used by the Counts lane.
DC: `ChainState/Chain.lean:125,136,149`, same carrier step adapters.
The chain contracts have no unified DC counterpart; they are derived carrier
lemmas (G20), with witnesses at `MatchingProgress.lean:147` and
`FinalityCertificates.lean:133`. Receipt remains in G13.

C3 adds G22 high record preservation and the view no-contest bound. The root
imports both modules. `RecordHighDef` is in the definition-module list. The
Tests glob builds the regression tests and the axiom audit.

```text
┌────────────────────────────┬──────────────────────────────────────────────────────────────┐
│ Module (KitFG/)            │ Role                                                         │
├────────────────────────────┼──────────────────────────────────────────────────────────────┤
│ RecordHighDef.lean         │ Inclusive HighRecord; closed Statements and complete _def    │
│ RecordHigh.lean            │ One record write; contest bound from honest quorum members   │
│ Tests/RecordHigh.lean      │ Inclusive cut, locks, low timeout, fallback and contest      │
│ Tests/Axioms.lean          │ Kernel dependencies of the record equations and proofs       │
└────────────────────────────┴──────────────────────────────────────────────────────────────┘
```

H.13 uses `h0 = μ+1` and gives `H ≤ μ+1`, equivalent to no contest with
`j > μ`. FF2 uses `h0 = M+1` and gives exactly FF2-C's `H ≤ M+1`.
DC: `ValidatorClient/W4FKChainFinalityRows.lean:115–129` consumes the guard.
INTENTIONAL: H1 and record induction supply it (`blueprint/22-finality.md:770–773`).
The contest bound has no DC counterpart. INTENTIONAL addition: FJ replaces
the NJ case (`blueprint/21-healing.md:2579–2581`).

```text
┌─────────────────────────────┬──────────────────────────────────────────────┬─────────────────────┐
│ Script                      │ Check                                        │ Exit codes          │
├─────────────────────────────┼──────────────────────────────────────────────┼─────────────────────┤
│ scripts/check-fg.sh         │ unsets the test-only overrides; builds the   │ 0 all pass; else    │
│                             │ two libraries once (--wfail), then runs the  │ the failed step's   │
│                             │ root-import check and the four checks below, │ code (1 for a       │
│                             │ then the negative controls of check-fg-      │ control that is not │
│                             │ pins.sh (steps 0, 4 and 5; temporary         │ detected)           │
│                             │ emitter, registry and allowlist copies, and  │                     │
│                             │ the real registry) and of the FG import-     │                     │
│                             │ closure check; stops at the first failure    │                     │
│ scripts/check-fg-syntax.sh  │ no native evaluation outside comments in the │ 0 clean; 1 found; 2 │
│                             │ two FG libraries: native_decide, +native,    │ missing directory,  │
│                             │ native := true, ofReduceBool, ofReduceNat    │ root file or files  │
│ scripts/CheckFGAxioms.lean  │ every constant of the two libraries uses     │ 0 clean; 1 bad      │
│                             │ only propext, Classical.choice, Quot.sound   │ axiom or forbidden  │
│                             │ (this rejects sorryAx and the _native axiom  │ library in the      │
│                             │ of native_decide); the root of every module  │ closure; 2 nothing  │
│                             │ in the import closure of the two FG roots is │ found, usage error  │
│                             │ on a literal list (no AvailableChainFGSA, no │ or missing name     │
│                             │ library above the FG libraries); --root M    │                     │
│                             │ (controls); --expect N … checks that the     │                     │
│                             │ names exist; reads built data                │                     │
│ scripts/FGPinIds.lean       │ prints the manifest of the elaborated pin    │ 0 clean; 2 a pinned │
│                             │ table; --check-names checks that each pinned │ name is not an FG   │
│                             │ Lean name is an FG constant; --ext prints    │ constant, or a      │
│                             │ the leanIn names; every mode rejects a       │ leanIn library is   │
│                             │ leanIn library that is not on its allowlist; │ not on the          │
│                             │ reads built data                             │ allowlist           │
│ scripts/check-fg-pins.sh    │ builds the two libraries, runs               │ 0 clean; 1 registry │
│                             │ FGPinIds.lean; strict manifest grammar and   │ or allowlist        │
│                             │ trailers (src, pin, ap, external,            │ mismatch; 2 build   │
│                             │ notFormalized, dep, hist, mention); each     │ failed, bad or      │
│                             │ source resolves to its registered version    │ missing manifest,   │
│                             │ with the pinned hash and matches its §0.1    │ emitter failure,    │
│                             │ row; each id has an entry and one Index row; │ malformed or        │
│                             │ no id that a current pin names (its own id,  │ duplicate allowlist │
│                             │ a dep: .ap or .external, or a registry id in │ entry               │
│                             │ its free text outside a (history: …) marker) │                     │
│                             │ has WITHDRAWN or SUPERSEDED as a token in    │                     │
│                             │ its status; the hist pins are exactly the    │                     │
│                             │ script's dated allowlist, each WITHDRAWN or  │                     │
│                             │ SUPERSEDED; prints the number of leanIn      │                     │
│                             │ names. The full pin gate is check-fg.sh PLUS │                     │
│                             │ check-fgsa.sh (the leanIn names)             │                     │
└─────────────────────────────┴──────────────────────────────────────────────┴─────────────────────┘
```

Run `bash scripts/check-fg.sh` for all checks. The Lean scripts read the built
`.olean` files, which Lean does not compare with the sources: run them alone
only after `lake build AvailableChainSimplexFG AvailableChainKitFG`, with
`lake env lean --run scripts/<file>.lean`.

## FG-SA composite model (store)

The library `AvailableChainFGSA` (namespace `AvailableChain.FGSA`) is the
composite FG-SA store: the SA base (`GridCO.State` under `slowLeasePolicy`), the
FG store of `SimplexFG`, the stored proposal wires, the row pool and the fast
writes. Its plan is `docs/plans/2026-09-29-fgsa-model-store.md`; its report is
`docs/FGSA-STORE-REPORT.md`; the gate reports are
`docs/audit/fgsa-task*-opus-review.md`, `docs/audit/fgsa-model-check-report.md`
and `docs/audit/fgsa-final-audit-*.md`. It is a default target. It does not
import the framework, the registry, SA-PC or the witnesses, and it names no
engine (`bash scripts/check-fgsa.sh` checks this). The results are local store
facts; the cross-node results take `ContentAgree`, which holds for any two
stores with `MetaInv` (`contentAgree`, I9 Task 9); the run lifts are composition
task T7. Before I9 (2026-09-29), `ContentAgree` was a store-pair premise, and
the cross-node results held only for store pairs under it. The first row and the
rows under `scripts/` are paths from the repository root.

```text
┌────────────────────────────────┬────────────────────────────────────────────────┬────────────────────┐
│ File (AvailableChainFGSA/)     │ Role                                           │ K / blueprint ids  │
├────────────────────────────────┼────────────────────────────────────────────────┼────────────────────┤
│ AvailableChainFGSA.lean        │ root; imports every file below                 │                    │
│ Model/Objects.lean             │ Params, labels, row bodies, wires, Msg, Input, │                    │
│                                │ decoders, eraseFG, base conversions, rounds;   │                    │
│                                │ packInner, packBody, appOf, rowsOk (D9)        │                    │
│ Model/Store.lean               │ State, initial, outputs (finalized, confirmed, │ bp.activeView.v1,  │
│                                │ stable), actView, onView, normalizeS,          │ bp.reconcile.v1    │
│                                │ reconcile, lease and fastWrite reads,          │ (defs)             │
│                                │ blockExcluded                                  │                    │
│ Model/Handlers.lean            │ admitHead, admitRow, parentFG, fgBlock,        │                    │
│                                │ blockAccepted, admitBlock, process, wellFormed │                    │
│ Model/Clock.lean               │ fastSet, gateStep, clockPre, clock             │                    │
│ Model/Frame.lean               │ controls, fullTree, liveRoot, HEAD votes and   │                    │
│                                │ support, getHead, proposalRows, propose,       │                    │
│                                │ fgHead, fgSource, fgInputs, attest             │                    │
│ Statements/Invariants.lean     │ Reachable, NestOK, SACompat, FastOrigin,       │ K4, K5 premise     │
│                                │ CStoreInv, Inv0, MetaInv, ContentAgree (the    │                    │
│                                │ store-pair content property, DQ3(b); a theorem │                    │
│                                │ after I9: contentAgree)                        │                    │
│                                │ LeaseBelowOutputStore and its f_def (E-11)      │ E-11 PROVED        │
│ Statements/Store.lean          │ OutputNestingStored, StoreInvariant,           │ K2, K4             │
│                                │ FMonotone, MetadataInvariant                   │                    │
│                                │ StoreBundle, StoreBundleInvariant, f_def       │ E-11, D14; PROVED  │
│ Proofs/BlockAncestry.lean      │ public Block ancestry lemmas                   │                    │
│ Proofs/SetEq.lean              │ Pool permutation and set-only proposal reads   │ T7.9 A             │
│ Proofs/Carrier.lean            │ local carrier: eraseFG slot, root, parent,     │ K5 local           │
│                                │ ancestry and compatibility                     │                    │
│ Proofs/Fields.lean             │ write sets of every step                       │                    │
│ Proofs/Head/Pool.lean          │ Clean support counts; F-anchored confirmation │ P3 F1b.1          │
│ Proofs/Head/Walk.lean          │ Conditional FG-SA suffix walk instances       │ P3 F1b.4a         │
│ Proofs/Head/Score.lean         │ Retained-suffix store score equality          │ P3 F1b.4a         │
│ Proofs/Head/Transfer.lean      │ HEAD coverage from transfer bounds           │ P3 F2.3           │
│ Proofs/ActView.lean            │ actView laws (items 1–6); SA bridge of the     │ bp.activeView.v1   │
│                                │ tick (clock_eq_saClock_offGate,                │                    │
│                                │ clock_eq_saClockFrom_gate: the walk from F)    │                    │
│ Proofs/Nesting.lean            │ outputNesting_stored, finalized_preceq_stable  │ K2                 │
│ Proofs/Reconcile.lean          │ exact effects, idempotence, reconcile_frame,   │ K3, K1             │
│                                │ storeControls_reconcile;                       │                    │
│                                │ reconcile_harmless_origin (reconcile_harmless  │                    │
│                                │ is a helper)                                   │                    │
│ Proofs/Admission.lean          │ refusal and accept-branch agreement; block-    │ J3, K8 input       │
│                                │ step SA bridge (actView_admitBlock_*);         │                    │
│                                │ admitBlock_sufficient; parentFG_isSome_iff_    │                    │
│                                │ root, admitBlock_missingParent (I9)            │                    │
│ Proofs/StoreInv.lean           │ storeInvariant, J_mem, fMonotone,              │ K4 core, K1        │
│                                │ viewRootInj_TF, SACompat, FastOrigin,          │                    │
│                                │ admitBlock_reconcile_harmless, selector facts, │                    │
│                                │ rootInj_all (I9)                               │                    │
│ Proofs/Metadata.lean           │ metadataInvariant, process_cumulative,         │ K4 metadata        │
│                                │ clock_cumulative, stored_wire_of_block         │                    │
│ Proofs/LeaseOutput.lean        │ E-11 stored-target invariant                   │ E-11               │
│ Proofs/StoreBundle.lean        │ E-11 bundle induction; storeBundleInvariant    │ E-11, D14          │
│ Proofs/CrossNode.lean          │ fg_eq_of_eraseFG_eq_across, preceq_iff_across, │ K5 cross-node      │
│                                │ compatible_iff_across, rootInjectiveOn_across  │                    │
│                                │ under CStoreInv, MetaInv and ContentAgree;     │                    │
│                                │ contentAgree_self (CStoreInv, MetaInv);        │                    │
│                                │ contentAgree (MetaInv at both stores),         │                    │
│                                │ contentAgree_reachable (I9)                    │                    │
│ Proofs/Head.lean               │ T7.W walk wrappers (Grid CO walk lemmas at     │ T7.W (W1), (W2)    │
│                                │ slowLeasePolicy): (W1)                         │                    │
│                                │ headInTree_stored, getHead_stored,             │                    │
│                                │ headVote_stored; (W2)                          │                    │
│                                │ liveRoot_preceq_headInTree, F_preceq_liveRoot, │                    │
│                                │ F_preceq_headInTree; from B ⪯ F:               │                    │
│                                │ preceq_getHead_of_preceq_F,                    │                    │
│                                │ preceq_fgHead_of_preceq_F,                     │                    │
│                                │ preceq_headVote_of_preceq_F (s > 0 only);      │                    │
│                                │ headVote_zero (slot 0 gives genesis)           │                    │
│ Tests/Support.lean             │ admitWith, process_eq_admitWith: proved        │                    │
│                                │ rewrite of a delivery for kernel checks        │                    │
│ Tests/Smoke.lean               │ decide examples of the model                   │                    │
│ Tests/RootCollision.lean       │ I9 positive tests: the former colliding blocks │                    │
│                                │ have distinct roots; ContentAgree holds; a     │                    │
│                                │ repeated block is refused as a duplicate;      │                    │
│                                │ wrong row lists are refused (before I9: DQ10   │                    │
│                                │ root collision, ContentAgree failed)           │                    │
│ Tests/Axioms.lean              │ #print axioms of every public theorem of Tasks │                    │
│                                │ 2 and 7–12, of I9 Task 9, and of T7.W          │                    │
│ scripts/check-fgsa.sh          │ build (--wfail); root imports and the direct-  │                    │
│                                │ import allowlist with directory rules, on      │                    │
│                                │ parsed headers; native scan; Q1/Q5 grep; the   │                    │
│                                │ three Lean checks (all required); negative     │                    │
│                                │ controls for each import, closure, coverage,   │                    │
│                                │ lease and ext-name rule                        │                    │
│ scripts/CheckFGSAAxioms.lean   │ axioms of every compiled FGSA constant; every  │                    │
│                                │ source file is in the build; no Framework,     │                    │
│                                │ Registry, SAPC or Witnesses module in the      │                    │
│                                │ import closure; --expect N …                   │                    │
│ scripts/CheckFGSALease.lean    │ no FGSA declaration is policy-generic; every   │                    │
│                                │ GridCO [LeasePolicy] argument in FGSA and in   │                    │
│                                │ the reached AvailableChain.* definitions is    │                    │
│                                │ slowLeasePolicy (or, in a generic imported     │                    │
│                                │ definition, its own parameter)                 │                    │
│ scripts/CheckFGSAExt.lean      │ each leanIn name of the FG pin table (records  │                    │
│                                │ of FGPinIds.lean --ext) exists, is declared in │                    │
│                                │ an AvailableChainFGSA module and uses only the │                    │
│                                │ three standard axioms (the checks of a .lean   │                    │
│                                │ name); check-fgsa.sh also requires at least    │                    │
│                                │ one record when Pins.lean has a leanIn clause; │                    │
│                                │ --root M (controls); the pin gate for a pin    │                    │
│                                │ with leanIn evidence is check-fg.sh plus       │                    │
│                                │ check-fgsa.sh                                  │                    │
└────────────────────────────────┴────────────────────────────────────────────────┴────────────────────┘
```

Run `bash scripts/check-fgsa.sh` for all checks. The Lean scripts read the
built `.olean` files: run them alone only after `lake build AvailableChainFGSA`.

E-11 `StoreBundle` has cstore, meta, nest and lease fields. Its reachability
proof and the `LeaseBelowOutputStore` live lease bound are PROVED.

The T7.W row-fold declarations are now in `AvailableChainKitFG/Certificates.lean`
(namespace `AvailableChain.KitFG`, I14): `process_row_eq`, `process_row_comm`,
`process_row_idem`, `transition_perm`, `transition_eq_of_mem_iff`, and
`transition_eq_of_toFinset`. The shared `AvailableChain.FGSA.liveRoot_stored`
proof is in `AvailableChainFGSA/Proofs/StoreInv.lean`.

## FG-SA run library (T7.2–T7.4)

`AvailableChainFGSARun` is a default library with namespace
`AvailableChain.FGSA.Run`. Its facade imports Model, Statements and Proofs;
the library glob builds Tests. It adapts the FG-SA store to engine v2.

```text
┌─────────────────────────────────┬───────────────────────────────────────┐
│ Module (AvailableChainFGSARun/) │ Role                                  │
├─────────────────────────────────┼───────────────────────────────────────┤
│ Model/Protocol.lean             │ fgsa protocol, node and wire adapters │
│ Model/Families.lean             │ Label families and isolation          │
│ Statements/Excludes.lean        │ Exclusion and epoch predicates        │
│ Statements/Interface.lean       │ Output interface and store factors    │
│ Statements/Acceptance.lean      │ Timely, invariant and trigger         │
│ Statements/AC.lean              │ Event-indexed FG-SA AC reads          │
│ Statements/ReceiptCoverage.lean │ K8 receipt/coverage Prop and inputs   │
│ Proofs/Protocol.lean            │ Adapter, field and decoder facts      │
│ Proofs/Excludes.lean            │ Exclusion stability and epoch proofs  │
│ Proofs/Interface.lean           │ Proposal label injectivity            │
│ Statements/Client.lean          │ Row safety and indexed client inputs  │
│ Proofs/Emission.lean            │ Emission, decoding and restart fold   │
│ Statements/Emission.lean        │ Wire check and input decoding Props   │
│ Proofs/EmissionWellFormed.lean  │ Row validity and well-formed emission │
│ Proofs/ClientTrace.lean         │ Linked client trace and no slashing   │
│ Proofs/ClockLaws.lean           │ Base clock laws and restore premises  │
│ Proofs/Reachable.lean           │ Run store bundle and proposal origins │
│ Proofs/Hooks.lean               │ HooksSound and child well-formedness  │
│ Proofs/Readiness.lean           │ Non-block and parent readiness proofs │
│ Proofs/Acceptance.lean          │ Thresholds and receipt law proofs     │
│ Statements/Receipts.lean        │ Decoded proposal block                │
│ Proofs/Receipts.lean            │ Receipt splits, stamps and origins    │
│ Proofs/ReceiptCoverage.lean     │ K8 coverage at receipt deadlines      │
│ Proofs/Content.lean             │ Content agreement at indexed stores   │
│ Tests/Protocol.lean             │ Protocol and acceptance controls      │
│ Proofs/Schedule.lean            │ Tick order, release and block slots   │
│ Proofs/AC.lean                  │ AC laws and slot-only gate corollary  │
│ Tests/Protocol.lean             │ Protocol examples                     │
│ Tests/Axioms.lean               │ Public theorem axiom audit            │
└─────────────────────────────────┴───────────────────────────────────────┘
```

`bash scripts/check-fgsa-run.sh` checks the build, root imports, import layers,
used constants, axioms, lease instances and negative controls.


## FG-SA claims skeleton (F0.0b)

The three roots contain only imports. Each library has its own Tests
target. The roots do not import Tests. `scripts/check-fgsa-claims.sh` checks
P3 layers, module order, compiled dependencies, leases, equation exports,
unused imports, and negative controls. No baseline entries were added.

```text
┌─────────────────────────────────────────────────┬─────────────────────────────────────┐
│ Module                                          │ Purpose                             │
├─────────────────────────────────────────────────┼─────────────────────────────────────┤
│ AvailableChainFGSAClaims.lean                   │ Claims library root                 │
│ AvailableChainFGSAClaims/FGSAClaims.lean          │ G-F0a safety and G-F0b W outputs    │
│ AvailableChainFGSAClaims/Statements/Bounds.lean │ FG-SA bound terms                   │
│ AvailableChainFGSAClaims/Tests/Recurrence.lean  │ Astra B1 positive controls          │
│ AvailableChainFGSAProofs/Proofs/Shared/Recurren │ FG-SA implications and bound proofs │
│ ce.lean                                         │                                     │
│ AvailableChainFGSAClaims/Statements/Counts.lean │ FG-SA interval counts and proposals │
│ AvailableChainFGSAClaims/Statements/Regimes.lea │ FG-SA regimes and named sets        │
│ n                                               │                                     │
│ AvailableChainFGSAClaims/Statements/Windows.lea │ FG-SA window specifications         │
│ n                                               │                                     │
│ AvailableChainFGSAClaims/Statements/Packages/Sa │ Foundation and Clean packages       │
│ fety.lean                                       │                                     │
│ AvailableChainFGSAClaims/Statements/Packages/Ou │ Outage point premises               │
│ tage.lean                                       │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/Regimes. │ Counts, delivery and seed proofs    │
│ lean                                            │                                     │
│ AvailableChainFGSAClaims/Tests/Regimes.lean     │ Horizon-zero regime smoke values    │
│ AvailableChainFGSAClaims/Statements/Reads.lean  │ V2 cut and FG-SA store/gate reads   │
│ AvailableChainFGSAClaims/Tests/Reads.lean       │ Three-read regression on v2         │
│ AvailableChainFGSAClaims/Statements/Counts.lean │ Provisional honest proposal read    │
│ AvailableChainFGSAClaims/Statements/Channels.le │ FG-SA channel and signed-row reads  │
│ an                                              │                                     │
│ AvailableChainFGSAClaims/Statements/ChannelProp │ FG-SA safety channel predicates     │
│ s.lean                                          │                                     │
│ AvailableChainFGSAClaims/Statements/ComposeStmt │ FG-SA post-gate composition windows │
│ .lean                                           │                                     │
│ AvailableChainFGSAClaims/Tests/Channels.lean    │ Channel kernel regression controls  │
│ AvailableChainFGSAProofs/Proofs/Shared/Gate     │ G32 gate service and opening source │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ Gate-to-action and R15 adapters     │
│ OpeningSource.lean                              │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/Channels │ Channel equations and row ordering  │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/StoreRun │ Cumulative run store metadata       │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/ScoreRun │ G25 scores; G11 suffix and regimes  │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ Active HEAD receipts                │
│ GateReceipt.lean                                │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ ExactService HEAD clause            │
│ ExactHead.lean                                  │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ Exact gate service from HEAD reads  │
│ ExactService.lean                               │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/Closure   │ Inclusive history and source reads  │
│ AvailableChainFGSAProofs/Proofs/Clean/GateOutput │ Conditional gate result below S    │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/Action   │ Action step and frozen corollaries │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/Transfer  │ Pre-freeze path and transfer frame  │
│ Frame.lean                                      │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/Transfer  │ Public transfer with named C5      │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/Frame    │ Given-state Clean frame core        │
│ .lean                                           │                                     │
│ AvailableChainFGSAClaims/Claims/Foundations.lean │ Client safety; frozen K8 citation   │
│ AvailableChainFGSAClaims/Claims/Shared.lean     │ Same-label and pure head claims     │
│ AvailableChainFGSAClaims/Claims/Clean.lean      │ Clean history, cut and safety Props │
│ AvailableChainFGSAProofs/Proofs/Shared/Claims.l │ Four claim implication/projections  │
│ ean                                             │                                     │
│ AvailableChainFGSAClaims/Tests/Axioms.lean      │ Claims public-theorem axiom audit   │
│ AvailableChainFGSAProofs/Proofs/Foundations/Cou │ Recovery counts and exact target    │
│ nts.lean                                        │ quorum consumption (22 I7)          │
│ AvailableChainFGSAProofs.lean                   │ Proofs library root                 │
│ AvailableChainFGSAProofs/Proofs/Foundations/Cro │ Strict held-block crossing, FaultX  │
│ ssing.lean                                      │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Car │ Run carrier and held row origins    │
│ rier.lean                                       │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Exp │ Foundation claim wrappers (L42)     │
│ ort.lean                                        │                                     │
│ AvailableChainFGSAProofs/Proofs/Assembly/Founda │ Foundation claim export boundary    │
│ tions.lean                                      │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Sto │ Run store, frame, views and seeds   │
│ re.lean                                         │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Cer │ Run chain geometry and certificates │
│ tificates.lean                                  │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Lea │ All-row lease target bound          │
│ ses.lean                                        │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Rec │ Exact reconcile edits and K1        │
│ oncile.lean                                     │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Cli │ Client safety; one row per round    │
│ ent.lean                                        │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/Reads.lean │ Cut, gate values and index proofs   │
│ AvailableChainFGSAProofs/Proofs/Shared/HeadCover │ Batch head coverage; keep parameter │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ Ordinary walk and band/eligibility  │
│ RetainedWalkStore.lean                          │ adapters                            │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ Store head floor and anchor geometry │
│ HeadGeometry.lean                               │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ View witness keep; pivot exactness  │
│ KeepExact.lean                                  │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/Count   │ Active receipt and batch count bounds │
│ AvailableChainFGSAProofs/Proofs/Shared/Relay   │ C5 forward; C6 head-vote backward     │
│ AvailableChainFGSAProofs/Proofs/Shared/Release │ Active release laws and fault bound │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/SameLabel │ Same-label raw gate compatibility   │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/Export   │ Frozen Shared claim wrappers        │
│ .lean                                           │ SYN L50 Shared export boundary      │
│ AvailableChainFGSAProofs/Proofs/Assembly/Shared │ Shared exports for the package root │
│ AvailableChainFGSAProofs/Proofs/Assembly/Root.lean │ SYN L58 safety aggregate; head premise │
│ AvailableChainFGSAProofs/Proofs/Assembly/Clean  │ Clean cut and safety claim assembly │
│ .lean                                           │ SYN L50 assembly boundary           │
│ AvailableChainFGSAProofs/Proofs/Foundations/    │ Source discipline and source frame  │
│ Sources.lean                                    │ K6; frozen F1.1 and F1.3 inputs     │
│ AvailableChainFGSAProofs/Proofs/Foundations/    │ Timing interface producers          │
│ Timing.lean                                     │ TSrc, LabelBound, TimingContract    │
│ AvailableChainFGSAProofs/Proofs/Foundations/Cap │ G17 run cap; positive finality lag  │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Acc │ Accountable count; explicit lock    │
│ ountable.lean                                   │                                     │
│ AvailableChainFGSAProofs/Proofs/Foundations/Fin │ Finalized safety from Base and count │
│ alizedSafety.lean                               │                                     │
│ AvailableChainFGSAClaims/Statements/            │ Qualified search: Gen export        │
│ Recurrence.lean                                 │                                     │
│ AvailableChainFGSAClaims/Statements/Packages/   │ W finality premise packages         │
│ Finality.lean                                   │                                     │
│ AvailableChainFGSAClaims/Statements/Packages/   │ Healing and joined-kernel packages  │
│ Healing.lean                                    │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/         │ μ bounds and unique full H0 time    │
│ Compose.lean                                    │                                     │
│ AvailableChainFGSAClaims/Statements/Witness.lean │ Common healing witness and tstar    │
│ AvailableChainFGSAClaims/Statements/Healed.lean │ HEALED and explicit row-delay input │
│ AvailableChainFGSAClaims/Statements/WeakContinu │ Bounded weak-continuation statement │
│ ation.lean                                      │                                     │
│ AvailableChainFGSAClaims/Claims/WeakContinuatio │ Universal safety-only claim         │
│ n.lean                                          │                                     │
│ AvailableChainFGSAClaims/Tests/WeakContinuation │ Self-continuation and cut controls  │
│ .lean                                           │                                     │
│ AvailableChainFGSAProofs/Proofs/Shared/Healed.lean │ Same-time and later-start proofs    │
│ AvailableChainFGSAProofs/Tests/Channels.lean    │ Old source obstruction and G1 tests │
│ AvailableChainFGSAProofs/Tests/KeepExact.lean   │ Pivot ancestry regression tests     │
│ AvailableChainFGSAProofs/Statements/            │ Clean invariant and step statements │
│ CleanInvariant.lean                             │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Clean AG review contract            │
│ Interface.lean                                  │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Clean chain algebra and restriction │
│ Chain.lean                                      │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Clean non-gate fields and history   │
│ State.lean                                      │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Conditional gate state fields       │
│ StateGate.lean                                  │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Gate Ordered, Same, nonempty; guard │
│ StepGate.lean                                   │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Zero-cut history and truncation     │
│ Zero.lean                                       │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Bounded Clean and whole-run safety  │
│ Safety.lean                                     │                                     │
│ AvailableChainFGSAProofs/Proofs/Clean/          │ Frozen Clean results and cut lanes  │
│ Export.lean                                     │                                     │
│ AvailableChainFGSAProofs/Tests/Zero.lean        │ Nonempty time-zero schedule checks  │
│ AvailableChainFGSAProofs/Tests/Axioms.lean      │ Proofs public-theorem axiom audit   │
│ AvailableChainFGSAInhabit.lean                  │ Inhabit library root                │
│ AvailableChainFGSAInhabit/Tests/Axioms.lean     │ Inhabit public-theorem axiom audit  │
└─────────────────────────────────────────────────┴─────────────────────────────────────┘
```

The Tests targets are `AvailableChainFGSAClaimsTests`,
`AvailableChainFGSAProofsTests`, and `AvailableChainFGSAInhabitTests`.
The claim facade is `AvailableChainFGSAClaims/FGSAClaims.lean`.
It holds the complete exported safety-claim aggregate.

F1 fix X1–X8: Foundations/Accountable.lean now separates pure and whole-run
weight evidence from validator attribution. Foundations/Export.lean owns the
lease/source claim assembly and output nesting.
Foundations/Carrier.lean supplies the shared delivery and honest-row origins.
Shared/Gate.lean supplies the R15 exact selector step; temporal composition is separate.

F1 X9: Foundations/Timing.lean owns the three timing interface producers.
Export imports Timing; only claim assembly remains in Export.

F1 delta: fgsa_finalLock_ev is lane-only and is absent from docs/FGSA-API.md.
X8 changed its second disjunct from a faulty-holder count to
HasSlashableWeightBetween p.E (chainRows K) (chainRows W).
fgsa_finalLock_faulty_count preserves the attribution conclusion.
fgsa_finalizedSafety now uses FGSASlashableBound; the held-store route remains
as fgsa_storeSlashableBound_of_faults, with a BaseSet adapter.
All-run carriage follows from ExecutionValid, as in DC AdmissibleCore.

```text
┌─────────────────────┬──────────────────────────────────────────────────────────────────────────────────┐
│ Foundations file    │ New producers                                                                    │
├─────────────────────┼──────────────────────────────────────────────────────────────────────────────────┤
│ Carrier.lean        │ stored_block_wire_delivery; stored_chain_row_origin_delivery                     │
│ Accountable.lean    │ delivered_runBlock_carriage; emitted_runBlock_carriage                           │
│ Accountable.lean    │ fgsa_runBlock_carriage; fgsa_slashableBound_of_base                              │
│ Accountable.lean    │ fgsa_storeSlashableBound_of_base; fgsa_eventPrefixAgreement_of_bound             │
│ Crossing.lean       │ fgsa_finalLock_of_bound                                                          │
│ Accountable.lean    │ carried_rows_carriage; proposalRows_source; store_wire_origin                    │
│ Accountable.lean    │ FGSASlashableBound_def                                                           │
└─────────────────────┴──────────────────────────────────────────────────────────────────────────────────┘
### A3 unit-seat count modules
## A4 Gen support and honest-origin count

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌───────────────────────────────┬───────────────────────────────────────┐
│ Module                        │ Role                                  │
├───────────────────────────────┼───────────────────────────────────────┤
│ Statements/Pure/QuorumInter   │ Unit-seat honest quorum intersection  │
│ Statements/Pure/SupportCounts │ Honest-origin and two-majority counts │
│ Proofs/Pure/SupportCounts     │ Finite-seat majority count proofs     │
└───────────────────────────────┴───────────────────────────────────────┘
┌─────────────────────────────┬─────────────────────────────────────────────┐
│ Module                      │ Role                                        │
├─────────────────────────────┼─────────────────────────────────────────────┤
│ Statements/AC/Support       │ Score ancestry, conflict and seat contracts │
│ Proofs/AC/Support           │ Score antitone and conflicting score bounds │
│ Statements/Pure/HonestCount │ HonestOriginOfCountStatement                │
│ Proofs/Pure/HonestCount     │ honest_origin_of_count                      │
│ Tests/Support               │ Concrete finite-set honest-origin count     │
└─────────────────────────────┴─────────────────────────────────────────────┘
```

## A3 unit-seat count modules

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌───────────────────────────────┬───────────────────────────────────────┐
│ Module                        │ Role                                  │
├───────────────────────────────┼───────────────────────────────────────┤
│ Statements/Pure/QuorumInter   │ Unit-seat honest quorum intersection  │
│ Statements/Pure/SupportCounts │ Two-majority intersection count       │
│ Proofs/Pure/SupportCounts     │ Finite-seat majority count proofs     │
└───────────────────────────────┴───────────────────────────────────────┘
```

## A4 Gen support and honest-origin count

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌─────────────────────────────┬─────────────────────────────────────────────┐
│ Module                      │ Role                                        │
├─────────────────────────────┼─────────────────────────────────────────────┤
│ Statements/AC/Support       │ Score ancestry, conflict and seat contracts │
│ Proofs/AC/Support           │ Score antitone and conflicting score bounds │
│ Statements/Pure/HonestCount │ HonestOriginOfCountStatement                │
│ Proofs/Pure/HonestCount     │ honest_origin_of_count                      │
│ Tests/Support               │ Concrete finite-set honest-origin count     │
└─────────────────────────────┴─────────────────────────────────────────────┘
```

## B2 Gen lease windows (G26)

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌───────────────────────────┬───────────────────────────────────────────────────────┐
│ Module                    │ Role                                                  │
├───────────────────────────┼───────────────────────────────────────────────────────┤
│ Statements/AC/LeaseWindow │ Slow-window conflict and threshold expiry contracts   │
│ Proofs/AC/Lease           │ Slow-window contradiction and threshold expiry proofs │
│ Tests/LeaseWindow         │ Gen live-row adapter and boundary checks              │
└───────────────────────────┴───────────────────────────────────────────────────────┘
```

## G02 dominance count core (W9, 2026-10-01)

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌───────────────────────────┬──────────────────────────────────────────────┐
│ Module                    │ Contract or proof                            │
├───────────────────────────┼──────────────────────────────────────────────┤
│ Statements/Pure/Dominance │ MajUniqueChildStatement and its equation     │
│ Proofs/Pure/Quorum        │ maj_unique_child_statement; maj_unique_child │
│ Tests/Dominance           │ Two sibling blocks; one eligible child       │
└───────────────────────────┴──────────────────────────────────────────────┘
```

## E-12 DC regime bridges (2026-10-01)

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌─────────────────────────┬────────────────────────────────────────────────┐
│ Module                  │ Contract or proof                              │
├─────────────────────────┼────────────────────────────────────────────────┤
│ Statements/V2/DCRegimes │ DC recurrence and outage interval field types  │
│ Proofs/V2/DCRegimes     │ RecoveryCore and CutCore bridges to DC fields  │
│ Tests/DCRegimes         │ Gap-period instance and outage boundary checks │
└─────────────────────────┴────────────────────────────────────────────────┘
```

## G37 Gen DC property bridges (2026-10-01)

Paths omit `AvailableChainGeneric/` and `.lean`.

```text
┌───────────────────────┬────────────────────────────────────────────────────┐
│ Module                │ Contract or proof                                  │
├───────────────────────┼────────────────────────────────────────────────────┤
│ Statements/V2/DCProps │ Six DC output-property mirrors and equations       │
│ Proofs/V2/DCProps     │ Four equivalences with the Gen.Pure properties     │
│ Tests/DCProps         │ Closed endpoints, empty intervals, and source time │
└───────────────────────┴────────────────────────────────────────────────────┘
```

## Gen wave D2 (2026-10-01)

`Gen/` means `AvailableChainGeneric/`. `FGSA/` means
`AvailableChainFGSAProofs/Proofs/`. Paths omit `.lean`.

```text
┌─────────────────────────────────────────┬──────────────────────────────────────────────┐
│ Module                                  │ Contract or proof                            │
├─────────────────────────────────────────┼──────────────────────────────────────────────┤
│ Gen/Statements/Pure/OpeningAfterGate    │ Inclusive gate-grid delay                    │
│ Gen/Proofs/Pure/OpeningAfterGate        │ Inclusive gate-grid delay                    │
│ Gen/Statements/Pure/StageStops          │ Three tagged stops or terminal stage         │
│ Gen/Proofs/Pure/StageStops              │ Three tagged stops or terminal stage         │
│ Gen/Statements/Pure/AdditiveStages      │ Full sum and ordered additive bound          │
│ Gen/Proofs/Pure/AdditiveStages          │ Full sum and ordered additive bound          │
│ Gen/Statements/Pure/PeriodicStages      │ Elapsed fold at an Int residue               │
│ Gen/Proofs/Pure/PeriodicStages          │ Elapsed fold at an Int residue               │
│ Gen/Statements/Pure/HeadAfterSettlement │ Settlement ceiling and upper-cut bound       │
│ Gen/Proofs/Pure/HeadAfterSettlement     │ Settlement ceiling and upper-cut bound       │
│ FGSA/Shared/OpeningAfterGate            │ Action and gate bound bridge                 │
│ FGSA/Shared/HeadAfterSettlement         │ Vote and proposal ceiling bridges            │
│ FGSA/Healing/AdditiveStageBounds        │ Existing reset-budget sum bridge             │
│ FGSA/Healing/PeriodicStageBounds        │ Canonical action-time residue bridge         │
│ Gen/Tests/WaveD2                        │ Zero, equality, skip, tag and negative cases │
└─────────────────────────────────────────┴──────────────────────────────────────────────┘
```


### P-Fi sleep consumers (2026-10-10)

The current restart design is in `ARCHITECTURE.md`, E6, and `SLEEP-LEDGER.md`.
`Finality/RecoveryScope.lean` derives honest join bounds, local event-index
restart intervals, and confirmed readers. It also states the exact action
receipt supplier. `Finality/RestoreReads.lean` preserves acceptance and held
rows through durable restore. `Finality/TickRead.lean` connects joined tick
reads to time cuts. `RowsBatch` and `TailBatch` keep all honest HEAD seats.
`TailMixed` uses an exact retained-head receipt supplier. `Export` threads
these suppliers explicitly. The universal CoreServices vote supplier and
the safe receipt suppliers remain open; see the P-Fi Round 2 ledger entry.
