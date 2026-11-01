# P-Ou Round 4 handoff

Base: 0c836aac. Branch: sleep-pou4. P-Ou is PREPARED, not CLOSED.
This file supersedes the remaining-input list in the Round 2 handoff.
Public claims and protocol declarations are unchanged. There is no public STOP.

## Checked consumers

- ExactProposalReceipts:230, early requires a ≤ rho.horizon.
  ExactProposalRetained:562/649 supply the proposal/vote bounds.
- ExactProposalReceipts:239, relay requires the actual reader vote tick.
  ExactProposalRetained:708 supplies hih.
- RestoredReceipt:307, outage_restored_receipt_on uses P-Ar's public
  arming_prefix_batch_receipt. Restored services have no prefix field.
- RestoredReceipt:316, outage_prefix_receipt_of_protected_read uses P-Ar's
  actual positive-label Clean origin to derive 6Δ ≤ b₀ and the selected label cut.
- PersistenceSleep:127, outage_arming_local_on consumes ArmingSleepCert and
  arming_sleep_gate_core. Protection has the coveredNodes scope and current-F branch.
- PersistenceSleep:145, outage_arming_domain_on supplies P-Ar's hRows through
  outage_named_of_source_history. It returns current F, fullTree, or frame-root coverage.
- PersistenceSleep:181, outage_arming_sources_before_on derives the strict
  pre-pending global source history directly from the scoped certificate.
- PersistenceSleep:193, outage_arming_sources_on isolates only the actual
  pending action sources as the remaining all-ticks seed input.

The receipt-backed proposer-count core accepts honest counted seats and coverage
of all joined honest seats. The _on wrapper uses the joined set. The legacy
awake wrapper also covers joined seats through joinedAt.1. Both need actual
emitted and resolved receipts for every counted seat. ArmingCover now compiles
without a P-Ar file edit. Sleep consumers use the joined wrapper.

## Restored services

RestoredBatch:309, outage_restored_services derives all three service fields from
Base₂, full-run PartialSynchronyBy and GST ≤ b₁. No receiver-service, finality
compatibility, prefix-receipt or joint-invariant premise is added to this producer.
The incompatible-target alternative remains in each batch. Compatible targets
use their original acceptance; proposal HistorySafeAt comes from durable storage.
Fresh HEADs use the actual emission and the joined receiver's current epoch.

The target/proposal anchors and deadlines are:

- early read: v(q) → e(q);
- frozen read: e(q) → f(q);
- proposal read: f(q) → t(q+1).

Fresh HEAD transport remains v(q) → e(q), with survival through each later read.
The proposal-read service uses the public freeze anchor and its next public tick.
It does not infer retained HEAD history from earlier processing.

RestoredBatch:377, outage_continuation_receipt_of_prefix derives the restored
clauses from OutageContinuationSleepPrem. Its only separate receipt input is:

```lean
hPrefix : OutagePrefixReceipt p c E rho fast T b₀
```

Owner P-Ar must supply the continuation-prefix adapter at this exact boundary:

```lean
∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
  (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
  (fast : Bool) (T b₀ b₁ ΔF : Time),
  OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
  OutagePrefixReceipt p c E rho fast T b₀
```

ArmingKernel:785 proves the prefix from OutageSleep₂. Its type is unchanged.
The continuation premise has lengthV, rather than the OutageSleep₂ eta budget.
Do not assert that it is directly an argument to that public theorem.
P-Ou does not derive prefix service from its restored receipt.

## Later-reader origins and assembly

InclusionOrigins:43 proves the latest enabled gate from a caught-up read.
It uses the actual last restart marker, wake-restart law and awake reader.
InclusionOrigins:110 and Suppliers:131 derive the later result origin.
Export:168/175 now takes the following Clean projections, rather than hOrigins:

```lean
∀ q i x, x ∈ rho.honest → SA.gateTime p.toParams q ≤ rho.horizon →
  enabledGateAt p c E rho i x q →
  ∃ C, gateResultAt p c E rho i = some (some C) ∧
    Block.Preceq C (S_at p c E rho (timeIdx rho (SA.gateTime p.toParams q)) x)
```

```lean
ScopedMono (confirmedReader p c E rho)
  (fun t x => S_at p c E rho (timeIdx rho t) x)
  (fun t => 0 ≤ t ∧ t ≤ rho.horizon)
```

Owner P-As supplies these assembly projections at Assembly/Outage:75.
Tests/InclusionOrigins:14 checks them with the actual P-Cl1 producers:
Clean/GateOutput:27 clean_gateOutput_body, Clean/Closure:127 clean_invariant,
Clean/Closure:380 sExtends, and Clean/Safety:91 clean_outputsAt.
P-Cl1 is CLOSED; no new Clean theorem or public premise is required.
The first projection uses the actual gate result and its inclusive output bound.
The second is bounded public monotonicity, with confirmedReader guards.

The exact Clean section of mixed Export is checked from a verbatim extraction
in .lake/sleep-pou-r4/CleanConsumer.lean. All four wrapper axioms are standard.
The full Export remains EXPECTED-FAIL. This extracted check is not a full module build.
Shared/Claims:30/39 and its remaining adapters are P-As-owned; their Clean sleep
sets, confirmed-reader scopes and recoveryStart types still need assembly ports.

## Joint induction boundaries

GoodVotes:364, outage_good_release_bound bounds actual release opponents by A union W.
Only senders in outageH(s) outside W need compatible targets. Stored and replayed
honest HEADs have actual joined emissions. No NoRestart premise is used.
Tests/OutageServices:23 combines this result with E's strict count.

P-Ou still owns the following inputs and full induction work:

- ExactProposalReceipts:229, InclusionReceiverInputs: the full Clean producer
  for early target compatibility, relay service and retained score geometry.
- GoodVotes:136, hTargets: good emitted targets extend B and the receiver F.
- GoodVotes:342, hResults: every honest enabled result with label > r is compatible
  with B, including writers in W. This supplies exclusion of conflicting new keys.
- PersistenceSleep:193, hPending: every actual honest pending action source is
  compatible with B. The strict pre-pending seed is now proved.
- Induction:120 and ContinuationInduction:37: both full joint inductions must use
  covered receiver protection and the good-set/A-union-W release invariant.
  Their old all-honest seeds and explicit NoRestart proof lane do not close sleep claims.
- ContinuationJoint:671/871 and Close:84: scoped read/duty conclusions and final
  handover remain OPEN. These old consumers still project the removed noRestart field.

ContinuationTiming:133 proves OutageEnd(r) = v(r+k+1) = gateTime(r)+L.
PersistenceSleep:211 removes rows with deadlines at or before that handover.
The full induction must still prove the bound on old conflicting-row deadlines.
The expiry equality test keeps a later row and removes a row exactly at its deadline.
These endpoint facts do not establish the full handover invariant.

P-Ar's fast equality construction remains OPEN at ArmingSleep:699. Its exact hLast is:

```lean
∃ C, (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat, C) ∈
  cleanResults p c E rho (timeIdx rho b₀)
```

The named-row producer already exists, owner P-Fd:
Foundations/Sources:180 sourceDiscipline_emittedName. It has the exact hnamed type
of PersistenceSleep:145. Assembly passes it with the actual ScheduleWellFormed.
P-Ar's Clean state/history/saved inputs also exist: Clean/State:963,
Clean/Closure:127/219 and Clean/EpochSaved:15. P-As passes those through assembly;
the Outage lane must not import the Clean proofs.

## Package status

43 TARGETS, 502 GREEN, 11 EXPECTED-FAIL: nine P-Ou and two S-Ap.
GREEN records compilation, not public closure. The map includes the three newly
consumed P-Ar modules as dependency targets; P-Ou did not edit their sources.
Local audit fragment: 161 commands. Production commands stay in SleepAxioms;
test commands stay in their own standalone test roots. Canonical integration
must import production modules, never these test modules, under the existing key.

## Final validation

Proof source: c8885bf3. DCK P-Ou PASS with 41 strict sources, 3,124 results
and all 24 controls. Complete GREEN exports: 314 proof modules, 253 exports,
zero unaccepted and zero Gen exports. Local complete coverage and its control
PASS for 161 commands: 140 production, 17 InclusionExact, one InclusionOrigins
and three OutageServices. Only propext, Classical.choice and Quot.sound occur.
Layers: 72 inherited findings, zero new. Whitespace, ownership, new prose/code
line length and placeholder checks PASS. Machine inventory rows keep their
required three-token format. No checker, baseline, allowance or toolchain changed.
Evidence: .lake/sleep-pou-r4/dck-final.log, exports-final.log, coverage-final.log,
layers-final.log, clean-consumer-check2.log and consumer-final.log.
