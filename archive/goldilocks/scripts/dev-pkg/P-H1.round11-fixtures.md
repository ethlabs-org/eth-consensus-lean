# P-H1 Round 11 regression evidence

Production remains CLOSED. The four complete adversarial ExecutionValid
certificates remain OPEN/P-H1. This round uses the permitted partial-fixture
route: actual local handler folds and exact type-checked remaining goals.
No local state is assigned an FG height, finalized block, lease, or HEAD result.
The folds start at initialAt and use process, clock and acRestart.

The source specifications are healing-contract-34d9aa77.md section F,
tperm-decision-9a814001.md sections 1-3, and early-lease-design.md section 5,
under research/async-resilient-committees/tip-stability/codex/jobs.
The full prefix and regime obligations remain in P-H1.round7-fixtures.md.

## Checked local parts

Healing/RegressionFixture contains the common data. Each test imports this
non-test module. No test imports another test or a module from another project.
The digest uses app+1 for the finite local bodies; it is not a global injectivity
assumption. All listed bodies have different app values. Full receipt-domain
collision freedom remains part of each full-run certificate obligation.

```text
┌─────────────┬────────────────────────────────────────────────────────────────┐
│ Replay      │ Kernel-checked local facts                                     │
├─────────────┼────────────────────────────────────────────────────────────────┤
│ k=3         │ Gate 3 writes D with expiry 29. Restart 21 keeps that row.       │
│             │ Release at 25 is skipped. The computed label-6 HEAD is D.       │
│             │ A separate enabled source fast-writes B at gate 5. B ⋠ D.      │
│ k=4         │ D expiry is 33. At the joined reads 28/29/30, the proposal      │
│             │ parent, HEAD and S fail the three old B transfer obligations.  │
│ n=7 slow    │ Parent-first certificates give H=3, h_j=2, J and F=genesis.     │
│             │ Gate 250 saves B without a lease. The joined HEAD at 1009      │
│             │ is incompatible with B. Gate 251 slow-writes B, expiry 1017.   │
│ split batch │ Target and mature timeout certificates give H=3 and contest.  │
│             │ WB stamps are 2013/2014. Joined label-252 HEADs split 2/3.      │
│             │ Release count is 3<4; the actual slow B row survives at 2026. │
│             │ At 2032 B is the live root; a prior label-253 HEAD rejects B.  │
│             │ The proposer parent extends B. At 2034 expiry removes the row │
│             │ and the label-254 HEAD rejects B.                             │
└─────────────┴────────────────────────────────────────────────────────────────┘
```

The k=3 and k=4 tests are HealingStaleLeaseReplay. The slow test is
HealingSlowLeaseReplay. The split test is HealingSplitBatchReplay. All checks
use decide +kernel, and each proved result has a strict axiom command.
The constructed row quorums pass local parent admission. This does not prove
that the honest signers actually emitted them in a network run.

## Exact remaining goals

HealingReplayObligations declares k3Replay, k4Replay, slowReplay and splitReplay.
Each goal fixes the honest set and the source specification's sleeping environment.
The clock-only always-awake environments are not full-run inputs. Each full-run
goal also chooses a digest for the complete finite receipt domain. prefixDigest
keeps its values on the checked local certificate bodies. The local app+1 digest
cannot be used for a full execution with different honest app=0 proposals.
Each goal requires RecoverySleep₂ for a real V2.D.Run, the specified fixed phase,
and the actual PhaseBody/Transfers failure or honest proposal/ExactService failure.
RecoverySleep₂ includes ExecutionValid, Linked, CStar, RestartsAtWakes, receipt
root collision freedom, PartialSynchronyBy, fault bounds and joined recurrence.
The first three horizons include a nonempty recurrence window after Jst.
splitReplay 2058 is the old failure. splitExtensions requires two executions to
2070/2080 with identical event prefixes through the inclusive 2058 tick cut.
These declarations are types, not proofs of their existential witnesses.

To close them, construct the complete global event lists. Supply every honest
row and proposal signature origin, parent-first dependency, public awake tick,
sleep/wake restart, finite ready-anchor delivery and quiet suffix. Then connect
the concrete head/proposal/output reads to the checked local folds. In the k=4
run, retain the distinct failure of all three clauses, not only the first.
In the split run, add the actual signed Q_B proposal at 254 and its admitted
current-slot body before proving failure of ExactService.

transfers_fail_of_head is a checked bridge: an honest computed HEAD at a
permitted later label with B not below it refutes Transfers. It supplies no
execution, signature origin or service callback.

## Positive run

NonVacuity/HealingRun keeps its real horizon-310 execution, RecoverySleep₂,
non-genesis body after Jst and nvPerm. Its four new positive_* checks use the
named Foundation producers. Both phase-local cover adapters apply to every
qualified phase/read of that fixed run with P5 services produced from recovery.
No local phase-service record is an extra assumption of those positive checks.

## P-H2 handoff

Commit 18e34a92 is the first, adapter-only commit. RepairLeaseRecovery keeps both
exact types from f50d49e1:scripts/dev-pkg/P-H2.round6-handoff.md. It uses a private
phase-local write split: old deadlines expire; new writes use healing_tPerm_at
with the supplied matching SupportPermanenceServices. The whole-run recovery
TPerm producer is not used by either cover proof. The existing import is kept
for compatibility with the closed producer audits. P-H2 owns its caller imports.

No public Claims, model, P-H2 or P-Ou module is changed. No acceptance baseline,
checker implementation, public API snapshot, dependency or toolchain is changed.
