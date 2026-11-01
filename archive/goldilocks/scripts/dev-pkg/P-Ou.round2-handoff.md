# P-Ou round 2 — closure handoff

Base: babc0460 (sleep-int 03aecc74 plus S-Ap P15-CUT ddfe84be).
P-Ou is PREPARED, not CLOSED. This file records required inputs and ports.

P-Cl2's exact growth suppliers are installed at Outage/Export:166, after
`end CleanClaims`. The old section includes do not bind this theorem.
The public claim has no new premise. Claims/Outage already had the approved
independent trigger/deadline reader scopes; only its comment changed.
GrowthConsumer contains the actual unfolded production body, not a private
copy. Its build passes. The mixed Export build fails in its other imports.
Do not count that lower build as closure of the mixed Export.

Growth inputs:
- P-Cl1/P-Cl2: produce CleanTruncAt at the horizon from the sleep cut and
  compile production Clean/Export. Its public-output compatibility projection
  is the hOutputs argument of clean_growth_compatible_of_outputs.
- P-Ou: produce one confirmed inclusion witness at g(s) for each supplied
  honest proposal B. The witness is exactly
  `exists y, confirmedReader y g(s) and B <= S_at(timeIdx g(s),y)`.
  Together with hOutputs, the compiled compatibility proof covers every
  earlier confirmed trigger reader, even if that reader sleeps later.
- P-Ou: port inclusion_retained_reads/exact HEAD and InclusionGate* to
  confirmed readers, enabled gates, joined transfer and local epochs. Then
  prove scoped clean_inclusion_body for all later confirmed reads. Neither
  growth supplier is yet derived completely from CleanSet.
- P-ShA interfaces exist: use RegimesService *_on and exact retained
  geometry/ScoreServiceScope. P-Ou must derive those local inputs; past
  processing does not imply retained HistorySafeAt after restart.

P-Ar inputs:
- clean_epoch_saved_row from the running P-Cl1 round 2 is still absent here.
- Close corrected arming_prefix_batch_receipt, protected-receiver origins
  and arming seeds. The required prefix service includes earlyTime q <= b0.
- The origin supplies a gate at/before b0. outage_prefix_cut_of_origin then
  gives 6*delta <= b0; outage_prefix_label_cut gives the per-label bound.
  Genesis uses block_genesis_preceq and needs no pending prefix receipt.
- The round-1 unrestricted transfer defect is repaired in landed
  arming_head_ge_on and arming_healthy_batch: both use the joined guard.
- ArmingDuty:122/130 still fails at the joined act branches; :181 still
  supplies the old root idealization to a receipt theorem.
- ArmingGate:156/221 still uses old gate equations; :268 lacks the enabled
  marker; :316 lacks the exact receiver awake fact.
- Supply lower GREEN arming_write_row, arming_writeKeys_stable and
  arming_gateResult_tick (with its enabled guard) for PersistenceStep.
  P-Ou does not edit or duplicate P-Ar producers.

P-Ou receipt callers:
- ContinuationPaths:17/44 uses ReceiptCoverageAnchorPremises and
  fgsa_active_path_of_coverage_anchor. Both production consumers build.
- Remaining ContinuationReceipt calls need exact local coverage. The
  regression/early-gate calls anchor at v(s), deadline e(s); the frozen
  transfer call anchors at e(s), deadline f(s). ReadyTrigger, HistorySafeAt,
  handlers and restartFree must refer to that same anchor. Bind pathCoverage
  to dl(anchor o t). Do not supply dl(anchor)=dl(send) or global NoRestart.
- The public restored service still needs fresh HEAD/target dependencies,
  retained-history safety, compatible finality and survival at each of the
  early, freeze and proposal cuts. No public receipt premise was added.

Good votes and writes:
- outage_good_batch_of_e derives the exact good-seat majority and the late
  complement bound by A union W from Base2 and E, at every receiver store.
- outageV_gate_of_receipts uses that opponent cardinality as its internal
  count parameter. Membership, strict stamps and compatible targets are
  still service/joint-invariant inputs.
- outage_gate_writeKeys_compatible proves compatibility of newly written
  gate rows when the passed result is compatible. It allows old conflicting
  rows. The all-honest late-write invariant is still open.
- Full good-vote compatibility, late-write exclusion, both joint inductions
  and the handover at v(r+k+1) remain P-Ou work after arming/service inputs.
- T31/T35/T37 still need actual earlier witnesses or proofs that avoid the
  ticks. T61 now requests confirmedReaderAtIdx at the post-gate cut and gets
  awake only for that reader; its full test module waits on InclusionGate*.

Other owners:
- P-As: port Shared/Claims and Assembly/Outage to the two growth suppliers
  and the approved scoped conclusions. Shared/Claims fails on this base.
- S-Ap: D013 and P15-CUT are installed; no new defect was found in the
  corrected prefix predicate. The Run facade and Run.Tests.Axioms stay
  EXPECTED-FAIL in this map. Claims/Statements was not edited.
- P-Da: register GrowthConsumer, ContinuationPaths and GoodVotes in the
  architecture map and canonical audit inventory. No shared exception,
  baseline, checker or scope row was changed.
- Canonical audit moves: the two receipt names move from ContinuationReceipt
  to ContinuationPaths; outageV_gate_of_receipts moves from ContinuationGate
  to GoodVotes. SleepAxioms and P-Ou.coverage-fragment.txt audit all 59 names.

## Round 3 — current closure handoff

Branch sleep-pou2, base bf0c024d. The public package is OPEN.
GREEN means that a module builds. It does not mean that its regime inputs
are proved. No public claim statement has changed.

All paths below start in AvailableChainFGSAProofs unless another prefix is
shown. P-Ou has not edited Arming files, Clean files, Shared files or Assembly.

The retained and gate ports now build:

- Proofs/Outage/ExactProposalRetained:325, inclusion_retained_reads:
  retained premises are required only at actual joined vote readers.
  The proof uses local early HEAD/body service and local restart intervals.
- ExactProposalRetained:743/806/856: compatibility, joined proposal receipt
  and joined exact HEAD. The receipt/HEAD clauses match the approved scope.
- Proofs/Outage/ExactProposalReceipts:31/54: actual joined vote and enabled
  gate witnesses. T31 and T37 use a counted gate actor; T35 uses a counted
  vote reader. The horizon endpoint is included.
- Proofs/Outage/InclusionGateBounds:18: consume InclusionHistoryBounds.
  The duplicate Clean state induction is removed.
- Proofs/Outage/InclusionGateService:66: the exact gate uses GateReceiptScope.
  The count is joined participation, not awake participation.
- Proofs/Outage/InclusionGateBody:18/87: scoped post-gate and later-read
  consumers. Both owned inclusion test modules build with --wfail.

P-Ou's service inputs remain closure work:

- ExactProposalReceipts:229, InclusionReceiverInputs. Derive the early
  FreshHeadService and TargetReceiptService at e(q), for the actual proposer
  at t(q+1) or joined reader at v(q+1), with the read time at most rho.horizon.
  Derive the exact HeadRelayServiceScope at the actual reader vote tick.
  The relay input must include rho.events[ih]? = some (.tick y (v(q+1))).
  Derive RetainedServiceScope.proposal and .scores for
  each actual emitted proposal and joined reader.
- InclusionGateBody:115, hScopes: derive GateReceiptScope at each actual
  enabled or post-gate confirmed reader. This includes enabledness, the
  receiver join guard, idxBefore(e(s))->gate epoch and each authentic target
  service. A counted sender does not supply receiver readiness.
- InclusionGateBody:121, hOrigins: derive an enabled gate origin for every
  later confirmed read. Its exact required statement is:

~~~lean
∀ t x, SA.gateTime p.toParams pt.s ≤ t → t ≤ rho.horizon →
  confirmedReader p c E rho x t →
  ∃ q i B, pt.s ≤ q ∧ SA.gateTime p.toParams q ≤ t ∧
    enabledGateAt p c E rho i x q ∧ gateResultAt p c E rho i = some (some B) ∧
    Block.Preceq B (S_at p c E rho (timeIdx rho t) x)
~~~

This last origin is P-Ou work. It is not an input to add to a public claim.

Proposal anchor services build at RestoredReceipt:18/71. They use v(s)->e(s)
and e(s)->f(s). Base2, PartialSynchronyBy, the actual source acceptance and
the enabled/joined reader supply readiness, durable proposal HistorySafeAt,
handlers and survival. Each constructor has a displayed GST-at-anchor bound
and exact target/F compatibility at its deadline. Derive those timing and
finality bounds from the joint regime invariant. For prefix cuts, use the
healthy-prefix deadline when its GST bound is not available. Do not infer
HistorySafeAt for a retained object from processing in an earlier epoch.

P-Ou must still derive full prefix/restored batch service, good target
prefixes and finality floors. GoodVotes:136 produces actual good-seat
membership and strict stamps from the exact local service. GoodVotes:279
connects that output to the real gate count. GoodVotes:342 quantifies the
new-key exclusion over all honest writers, W included. Its hResults input
is still the all-honest compatible late-result invariant to prove.

PersistenceSleep:81, outage_joint_restart, preserves both global histories
and protection on the selected receiver scope at a real restart event.
Both full inductions and the handover at v(r+k+1) remain OPEN.

P-Cl1/P-Cl2 inputs:

- Claims/Clean:18 in AvailableChainFGSAClaims: CleanHistoryAt at the cut.
  Its order clause has confirmed readers, its nonempty clause has enabled
  gates, and its transfer clause has the receiver's joined vote guard.
  Saved and fast rows have the exact receiver epoch; saved retention also
  has activeCompatible. Suppliers:16 now accepts these intended fields.
- ExactProposalReceipts:250 requires this projection of that history:

~~~lean
∀ i x, i ≤ timeIdx rho rho.horizon → x ∈ rho.honest →
  let st := storeAt p c E rho i x
  let bound := BelowLabel p c E rho i (labelBoundAt p c rho i)
  bound (F_at p c E rho i x) ∧ bound (J_at p c E rho i x) ∧
    bound (S_at p c E rho i x) ∧
    (∀ row ∈ st.base.obligations, bound row.1) ∧
    (∀ q C, GridCO.savedGenuine st.base q = some (some C) → bound C)
~~~

- Proofs/Clean/Export:133: cleanTruncAt must return
  CleanTruncAt p c E rho b0 from the sleep cut, quorum, foundation and source
  frame. Its scoped public-output compatibility projection supplies P20.
- P-Cl1's current saved-row producer is on P-Ar's d60ff01d base:
  Proofs/Clean/EpochSaved:15, clean_epoch_saved_row. It is absent in this
  work tree. The source is readable in the parallel wt-w1b work tree.
  Its exact receiver/origin premises and conclusion are:

~~~lean
(h : CleanCutSet p c E rho b0 ΔF)
(hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
(hf : FGFoundation p c E rho) (hsrc : SrcFrameAboveStmt p c E rho)
(hx : x ∈ rho.honest) (hcut : SA.gateTime p.toParams q ≤ b0)
(hAw : AwakeClosed E x (slotStartZ p (q : Int)) b0)
(hEpoch : RestartFreeTime rho x (slotStartZ p (q : Int)) b0)
(hOrigin : B = .genesis ∨ ∃ r D, r < q ∧
  (r, D) ∈ cleanResults p c E rho (timeIdx rho b0) ∧ Block.Preceq B D)
:
Block.Preceq B (F_at p c E rho (timeIdx rho b0) x) ∨
  ∃ C, GridCO.savedGenuine (storeAt p c E rho (timeIdx rho b0) x).base q =
    some (some C) ∧ Block.Preceq B C
~~~

Do not use an arbitrary same-label origin. The statement needs r < q.

P-Ar inputs:

- ArmingReceipt:172, arming_prefix_batch_receipt_on: discharge its exact
  ArmingBatchReceiptService for each selected G receiver and prefix label,
  with earlyTime q ≤ b0. P-Ou's origin adapter remains P15-CUT compatible.
  Non-genesis protection needs an actual origin gate at or before b0;
  genesis uses its universal prefix-order fact.
- ArmingGate:26/89: supply the lower GREEN arming_write_row and
  arming_writeKeys_stable. Their existing pure statements are unchanged.
- ArmingGate:214: supply the guarded arming_gateResult_tick with
  enabledGateAt at its source tick and the same exact pre-gate raw result.
- ArmingGate:402: the pending seed must use the selected G scope and the
  sleep/epoch inputs. Required seed shape:
  forall y in G, OutageProtection p B j
    (storeAt p c E rho (afterTicksIdx rho (SA.gateTime p.toParams j)) y).
  Source and duty seeds remain global histories of actual emissions.
  The current legacy NoRestart/all-honest producer is not a sleep seed.

P-As inputs:

- Shared/Claims:30, clean_history_supplier: return the exact CleanHistoryAt
  from CleanCutPrem and the assembled CleanCutClaim.
- Shared/Claims:39, cleanSafety_outputs: return ScopedCompat and ScopedMono
  with confirmedReader on public times 0 ≤ t ≤ horizon. Do not return the
  old all-honest/unbounded output statement.
- Assembly/Outage:21/46/75: use hInputs, hScopes, the field-level history
  projection and the scoped output monotonicity in the current Export calls.
  The later inclusion caller must use the proved P-Ou hOrigins producer.
- Assembly/Outage:103: use the exact two growth suppliers at Export:211.
  InclusionGateBody:160 supplies the actual inclusive gate witness.
  InclusionGateBody:284 composes the first growth supplier from that witness
  and scoped output compatibility. The second supplier still needs the
  P-Ou later-read origin. No public growth premise is added.

The actual Outage/Export build fails in ArmingDuty:122/130/181,
ArmingGate:156/221/268/316 and Shared/Claims. The edited mixed wrappers are
PREPARED; they are not counted as a compiled exporter or public closure.

Final map: 36 TARGETS, 494 GREEN, 12 EXPECTED-FAIL (10 P-Ou, two S-Ap).
The canonical audit fragment now includes 108 SleepAxioms commands and 15
named inclusion-test commands. P-Da can use the existing audit key for
serial inventory integration. No shared checker, scope or baseline changed.

Validation of proof source 502f1893:
DCK P-Ou PASS (39 strict sources, 3,086 results, 24 controls).
Complete GREEN exports: 285 proof modules, 253 accepted, zero unaccepted.
Local complete coverage: 123 commands. Layers: 72 inherited, zero new.
Both owned inclusion tests build with --wfail. Only the three standard
axioms occur. Public-meaning STOPs: none.

## Round 4 — FIX-FIRST

The early field now requires a ≤ rho.horizon. The two retained calls supply
the proposal bound t(s) ≤ v(s) ≤ rho.horizon and the vote bound v(s) ≤ rho.horizon.
The relay field requires the actual vote tick at ih; the retained call supplies hih.
Export consumes this corrected internal record. Public statements are unchanged.

## Round 4 — current P-Ar inputs

The Round 3 P-Ar and P-Cl1 requests above are now supplied in this tree:
ArmingKernel.arming_prefix_batch_receipt is the corrected public P15-CUT theorem.
RestoredReceipt.outage_restored_receipt_on uses it directly; restored services
do not produce the prefix. The protected-read adapter uses the actual P-Ar origin.
PersistenceSleep.outage_arming_local_on uses the scoped ArmingSleepCert.
PersistenceSleep.outage_arming_domain_on supplies hRows from the global source
history and sourceDiscipline_emittedName through outage_named_of_source_history.
It retains the current-F branch and the coveredNodes receiver scope.

InclusionOrigins.inclusion_last_gate_reader proves the latest enabled gate
from an actual caught-up read, including a restarted reader. The later-origin
adapter needs the Clean gate-output bound at that gate and scoped monotonicity
on public reads in [0,horizon]. Those are Clean/assembly projections.
The global source seed through the pending tick is still P-Ou closure work.
Fast certificate construction at equality remains with P-Ar.

The current full handoff is scripts/dev-pkg/P-Ou.round4-handoff.md.
It supersedes the remaining-input lists above. Restored services and the
later-reader origin producer are now proved. Full joint closure remains OPEN.
