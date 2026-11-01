# P-H1 Round 7 regression fixture obligations

Round 8 status and the N4 expiry regression are in P-H1.round8-fixtures.md.
The four full ExecutionValid replays below remain required.

Status: clock regressions PROVED; full sleep-run replays OPEN/P-H1.
HealingJoinedStart.lean checks all four numerical source exclusions and the
new repair thresholds. It does not prove a protocol execution for those runs.
NonVacuity/HealingRun.lean separately proves a positive RecoverySleep₂ run
and a nonempty source body at label 2 after recoveryStart, with no service input.
Its prior unconditional TPerm test depended on a removed producer; that assertion
is replaced by the real sleep-regime/source witness. Full P5 closure stays open.

Each complete replay must construct all of these concrete objects:

- Params with the listed numerical fields; AppCodec Unit; V = Fin n;
  a finite honest set, HEAD/FG CStar bijections and linked proposer seats.
- Distinct scoped named roots, parent-first bodies and all certificates used
  by the GHOST witnesses. Prove NamedReceiptRootCollisionFree for delivered,
  held and emitted bodies plus ancestors; never assume global root injectivity.
- The complete event list. Omit asleep ticks and deliveries. Each wake has
  its phase-zero restart. Prove ScheduleWellFormed, SleepWellFormed,
  DeliveryWellFormed, UnforgeableSignatures and RestartsAtWakes.
- PartialSynchronyBy for every bounded anchor, including the processed-root
  alternative and actual ready handler events; no old P2 supplier is accepted.
- RecoverySleep₂ with the stated finite horizon, faulty count and joinedGap.
  Prove the actual postClock/gateResult/fastWrite and selected HEAD/proposal
  reads; source fields cannot be assigned as arbitrary FG states.
- Show each failing source vote is before recoveryStart, while later qualified
  phase starts and reads satisfy the new readiness and preserved floor guards.

The exact output obligations for each source-level specification are:

```text
┌─────────────┬─────────────────────────────────────────────────────────────────────┐
│ Replay      │ Required kernel facts                                               │
├─────────────┼─────────────────────────────────────────────────────────────────────┤
│ k=3         │ Δ=ΔF=1, n=4, k=3, R=2, GST=21, G=8; Jst=30.                       │
│             │ Actual D lease at gate(3), expiry 29; fast B at gate(5)=26.           │
│             │ Incompatible HEAD at 25; PhaseBody(5,B); ¬Transfers(5,B,26).         │
│ k=4         │ Same numerical context except k=4; D expiry 33.                      │
│             │ Joined D-path proposal at 28, HEAD at 29 and S at 30.                 │
│             │ PhaseBody(5,B); failure of all three old Transfers clauses.           │
│ n=7 slow    │ Δ=ΔF=1, n=7, k=2, R=2, GST=1001, G=8; Jst=1010.                   │
│             │ Saved B at 250; slow B write at 251; incompatible HEAD at 1009.      │
│             │ PhaseBody(251,B); ¬Transfers(251,B,1010). New first label is 253.    │
│ split batch │ Δ=ΔF=2, n=7, k=2, R=5, GST=2002, G=16; Jst=2020.                 │
│             │ §5 certificate prefix with F=genesis, H=3, active root F, contest.   │
│             │ W_B receipts at 2013/2014 across the strict 2014 freeze.              │
│             │ Slow B at 2020; first joined batch split 2/3; release count 3<4.      │
│             │ B lease live at proposal(254)=2032, expiry at 2034.                   │
│             │ Q_B at 254 lacks ExactService; old early TRepair branch fails.       │
│             │ New b=253, one threshold=255, two threshold=256.                     │
│             │ Quiet suffix to 2070/2080; gate(256)=2060, gate(258)=2076.             │
└─────────────┴─────────────────────────────────────────────────────────────────────┘
```

The first three horizons must include their displayed reads and a finite quiet
suffix that satisfies joinedGap. The split replay uses horizon 2058 for the old
counterexample; separate extensions to 2070 and 2080 check the new existential
triggers. Keep the same actual pre-GST certificate prefix and signing records.
The complete suffix Extension/RecoverySleep₂ proof is an exact OPEN/P-H1 goal.

No complete replay is reported as proved from arithmetic or from a missing
producer input. Their source specifications are healing-contract §F,
tperm-decision §§1-2, and early-lease-design §5, under JOINED-START.
