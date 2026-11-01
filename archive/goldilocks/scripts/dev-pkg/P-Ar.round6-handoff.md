# P-Ar Round 6 handoff — 2026-10-10

Base dcdb4a06, branch sleep-par6. Import repair commit: 244016e1.
P-Ar CLOSED. DCK PASS: 22 targets, 490 GREEN, 38 strict roots, 3,225 results,
and 24 controls. Local audit: 261 results; production fragment: 207 results.
Complete GREEN exports: 294 modules, 253 exports, zero unaccepted.
Local coverage: 261 commands; 170 modules, 252 exports, zero unaccepted.
Layers: 72 inherited, zero new. Headers: no P-Ar failure; two P-Ou failures.

All principal Round 5 constructor, history, and gate export names/types are
unchanged. Use scripts/dev-pkg/P-Ar.round5-handoff.md for their full types.
The two P-Ar score helpers have distinct arming_ names because the merged
ExactProposalReceipts module defines the original names. Their types are
unchanged. ArmingCover and the P-Ar audit/coverage fragments use the new names.

Concrete witnesses are in Tests/OutageArming.lean, namespace
AvailableChain.FGSA.Run.Tests.OutageArming.Finite.
positive_fast and positive_slow have no proof hypotheses. Each proves
ExecutionValid, a non-genesis stable read, membership of receiver 0 in the
protected set, the certificate, and an executed lease conclusion.
The fast witness has earlyTime(3) = b0 = 14 and no label-2 Clean result.
It uses ArmingSleepGateCert, whose comparison result can have label 1.
ArmingSleepCert requires max_mem at label 2 and cannot inhabit that branch.
The slow witness inhabits ArmingSleepCert with a label-2 result and the
current-epoch saved row. Both pending_input proofs use ArmingGateInput.
Both gate consumers invoke the production core export at the actual tick
(time 18, event index 24); the state after that tick has index 25.
They prove a lease deadline dl with 18 < dl and 18 + L(p) <= dl.
Finality is genesis there, so the lease branch is necessary.

Parameters: Delta = 1, n = 1, k = 2, R = 2, eta = 0. Each run has 25 events
and horizon 18. Genesis HEAD receipt at 1 and proposal receipt at 4 allow
the stable block-1 read at 10. The fast run receives HEAD 2 at 10, after
its strict early read; the slow run receives it at 9. Both receive HEAD 3
at 13, before the pending gate's early read at 14.
These are direct finite certificate and gate-export witnesses. They do not
claim OutageSleep2 or a healthy-prefix premise for the sparse event lists.
The one-seat fast trace's late HEAD 2 would violate healthy-prefix delivery.
The high-level regime/Clean constructors retain their verified conditional
consumer tests from Round 5. No new public meaning or premise was added.

Horizon 8 with Delta = 2 (EarlyCut.run) is too short: label-0 gate time is 12,
and the earliest positive-label gate is 20. For the minimal integer Delta=1
and k=2, a positive origin is first possible at gate 1 = 10. The fast and
slow lag allowances are both 4, so T=10 requires b0>=14; the next pending
gate is 18. The shared fast/slow witness attains these minimum parameters.
All existing negative cut tests remain in place.

P-Ou still owns hRows: the exact named-row/source-history input at the
pending action cut. No hRows factory or all-honest pending_input was added.
This branch's global header check still reports P-Ou GoodVotes and
RestoredBatch; no P-Ar file has a header failure.

Audit: all 25 new theorem declarations have direct strict print commands.
The production fragment contains 207 commands and production imports only.
The package map keeps 22 targets and all owned targets GREEN.
Evidence: .lake/sleep-par-r6/.
