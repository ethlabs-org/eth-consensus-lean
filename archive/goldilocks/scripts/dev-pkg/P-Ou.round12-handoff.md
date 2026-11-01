# P-Ou Round 12 handoff

Base: 1b245e9e. Branch: sleep-pou12.
Proof commits: 88a2634c, 696b63f6, a0d5801e, 41483e69.
P-Ou is PREPARED. The complete Round 12 task is incomplete.
Public claims, protocol declarations and Healing files are unchanged.
Both complete public exporters remain EXPECTED-FAIL. No public STOP.

## Completed proof groups

- O11-EARLY-READ: `AvailableChainFGSAProofs/Proofs/Outage/ScopedEarly.lean:118`,
  `outage_early_public_read`.
- O11-EARLY-HEAD: `AvailableChainFGSAProofs/Proofs/Outage/ScopedEarly.lean:182`,
  `outage_early_scoped_head`.
- O11-EARLY-F: `AvailableChainFGSAProofs/Proofs/Outage/ScopedEarly.lean:100`,
  `outage_early_finalized_read`.
- O11-DUTY: `AvailableChainFGSAProofs/Proofs/Outage/ScopedEarly.lean:223`,
  `outage_early_scoped_duties`.
- O11-W-READ, from its seed: `AvailableChainFGSAProofs/Proofs/Outage/ScopedCatchUp.lean:220`,
  `outage_caught_up_public_read_from_seed`.
- O11-OUTAGE, protected B: `AvailableChainFGSAProofs/Proofs/Outage/ScopedClose.lean:171`,
  `outage_protected_scoped`.

These declaration links contain the complete Lean types and proofs. They supersede
Round 11's OPEN producer goals except O11-W-SEED. The W read needs fewer inputs
than the old type: receipt, awake suffix, restart-free interval and low-F test are
not needed after its stable seed. The actual gate and inclusive endpoint remain.
The exact old O11-W-READ contract is proved in .lake/sleep-pou-r12/Contracts.lean.
The early read and outage result take two named Clean facts below. No future seed
or seed-horizon bound is added to an early public read.

The before-freeze event induction accepts the current inclusive read or post-duty
index. Its endpoint can be before the future restored seed and can equal lease
expiry. The in-flight HEAD branch handles the pending gate boundary. The duty
proof uses only emitted HEADs and proposal parents at scoped readers before b1.

The complete HEAD/F consumers are `AvailableChainFGSAProofs/Proofs/Outage/ScopedCatchUp.lean:366`.
They use ScopedBridge:170 after r and the early HEAD proof at labels at most r.
The restored suffix and early finalized proof supply all public F reads.
There is no new future HEAD, result, receipt or source callback in this consumer.

The read assembly is `AvailableChainFGSAProofs/Proofs/Outage/ScopedCatchUp.lean:287`.
It joins the early read, covered suffix, finalized W branch and W seed/read
branch. Its hWSeed parameter is exactly O11-W-SEED. This theorem is a consumer,
not a producer of that parameter. It does not close the public exporter.

## Common caller context

The common context has no marker, regression or first-event input. hHist and
hOutput are named P-Cl1 suppliers. They are required only by EARLY-READ and the
outage-only protected result. They are not new public claim premises.

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG Gen.Pure
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
  {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
variable [Fintype V]
    {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF)
    (hf : FGFoundation p c E rho) (origin : RQCOrigin p c E rho) (htsrc : TSrc p c E rho)
    (hnamed : ∀ k x r (a : RowWire p.n) e,
      HonestRowAt p c E rho k x r a → namedEntry a.payload.height_pair = some e →
      ∃ C G, actionSourceFG p c E rho x r = some (some C) ∧
        e = ((heightView p C).h, (heightView p C).T_h.root) ∧
        FGBlock.Preceq (heightView p C).T_h C ∧
        gateResult p c E rho x (r * p.R) = some (some G) ∧
        Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
    (hsrc : SrcFrameAboveStmt p c E rho)
    (hState : ∀ i, i ≤ timeIdx rho b₀ → CleanState p c E rho i)
    (hprov : ArmingJoinedProvenance (c := c) E rho)
    {B : Block} (hne : B ≠ .genesis) {l : Slot} {D : Block}
    {Dh β : FGBlock (Fin p.n)}
    (hc : ArmingSleepGateCert p c E rho fast T b₀ B l D Dh) (hβ : eraseFG β = B)

variable
    (hHist : CleanHist p c E rho (timeIdx rho b₀))
    (hOutput : ∀ j y s, j < timeIdx rho b₀ → enabledGateAt p c E rho j y s →
      ∃ C, gateResultAt p c E rho j = some (some C) ∧
        Block.Preceq C (S_at p c E rho (j + 1) y))
```

## Named suppliers and produced arguments

- hState: Clean/State:963, cleanState_of_hist, with Clean/Closure:127,
  clean_invariant at i <= timeIdx(b0), and Clean/Action's clean_actionStep.
- hHist: Clean/Closure:127, clean_invariant at timeIdx(b0).
- hOutput: Clean/GateOutput:27, clean_gateOutput_body at timeIdx(b0). Project
  its result and S inclusion; omit the passed-gate field. The enabled gate gives
  the actor's honesty through ScheduleWellFormed.honest_only.
- These three Clean producers use the actual HealthyPrefixSleep2, hf, hsrc,
  and FaultQ. Obtain FaultQ from the existing pre.faultQ_of_pos and positive b0.
  Positive b0 follows from the lag or the selected certificate's gate_le_cut.
  No extra quorum or all-honest gate input is needed.
- hprov is now produced by outage_joined_provenance in ScopedClose. It uses
  the actual joined HEAD read and its local prior proposal tick, with P-Cl1's
  existing retained-provenance proof also available as a named supplier.
- htransfer for the empty-G certificate: Clean/Closure:219,
  cleanHistoryAt_body, third clause, at the actual joined in-flight HEAD.
- hc: ArmingConstruction:398/:461, fast_arming_scoped_on /
  slow_arming_scoped_on. The slow producer's covered receiver is selected from G.
  If G is empty, outage_empty_covered_certificate supplies the certificate from
  the actual last Clean comparison. Its pending receiver clause is empty.
- beta/hBeta: outage_protected_initial_lift in ScopedClose. It selects a lift
  from the certificate's actual positive-label Clean origin. No arbitrary root
  or global all-honest stable lift is requested.
- hf, hsrc, htsrc and hnamed keep their P-Fd producers from Round 11.
  origin remains Foundations/Sources:316, sourceDiscipline_qcOrigin, with the
  existing SourceDisciplinePrem/FaultQ. Durable and epoch cumul forms stay split.

Direct imports of Clean proof modules from an Outage proof are forbidden by the
current layer rules. The proof consumers therefore take the named supplier facts
above. No checker, baseline, allowance or protocol declaration was changed.

## Remaining exact P-Ou obligations

### O11-W-SEED — OPEN, P-Ou; unchanged exact goal

```lean
∀ x t s j, outageConfirmedReader p c E rho fast b₀ b₁ x t →
  x ∉ coveredNodes p E rho fast b₀ → t ≤ rho.horizon →
  restoredLabel p b₁ + p.k ≤ s → j < timeIdx rho t →
  enabledGateAt p c E rho j x s →
  BatchReceiptAt p c E rho x s (SA.earlyTime p.toParams s) →
  AwakeClosed E x (SA.gateTime p.toParams s) t →
  RestartFreeTime rho x (SA.gateTime p.toParams s) t →
  V2.D.restartFree rho x (V2.D.Run.actionCut rho (SA.voteTime p.toParams s))
    (V2.D.Run.idxBefore rho (SA.earlyTime p.toParams s)) →
  ¬ Block.Preceq B (F_at p c E rho j x) →
  Block.Compatible B (S_at p c E rho (j + 1) x)
```


Caller: outage_continuation_public_reads, at the actual post-E W gate selected
by outage_caught_up_gate_scope. The current public F split produces the low-F test
at j by monotonicity. The gate producer supplies the batch, awake suffix and
receipt epoch. The raw result is compatible by the global actual HEAD producer.
The missing conclusion is S compatibility at j+1. Neither raw compatibility nor
a stable seed assumed for all honest nodes supplies that conclusion.
This remains an unproved P-Ou goal. No counterexample to the public claim is asserted.

### O12-PUBLIC-CONT — OPEN, P-Ou

Caller: OutageContinuation.Export, under the exact continuation sleep premise
in the common context. Select a non-genesis B from each actual initial confirmed
read and obtain hc, beta, hState, hHist, hOutput and hprov through the named
producers above. Genesis uses prefix order. Then discharge O11-W-SEED and consume
the scoped read and HEAD/F theorems. The final unchanged public type is:

```lean
OutageContinuationConcl p c E rho fast T b₀ b₁
```

Its full definition is Statements/OutageContinuation:40. The exact initial-read
quantifiers and every public output clause remain there. The complete scoped
per-B read and HEAD/F types are at the two ScopedCatchUp declaration links above.
The public body must use hf.cumul.1 and hf.cumul.2 with actual local epochs.
No NoRestart or all-honest stable seed may be supplied from the sleep premise.

### O12-PUBLIC-OUTAGE — OPEN, P-Ou

Caller: Close and Outage.Export, under their own premise:

```lean
variable (hO : OutagePrem p c fast E rho ⟨T, b₀, b₁⟩ ΔF)
```

Use the common actual model, hf, htsrc, hnamed, hsrc, hState, hprov, hHist,
hOutput, selected B, hne, hc and hBeta. No continuation h, synchrony, E window,
post-E count or marker is needed. The protected-B producer now proves the exact
four-part O11-OUTAGE result; its full type is ScopedClose's outage_protected_scoped.
The exact alias form also compiles and is proved in Contracts.lean.

Select the certificate for each initial protected B. Use the empty-G certificate
when the slow arming receiver set is empty. Apply the produced four-part result
and handle genesis. The final unchanged public type is:

```lean
OutageCompatAt p c E rho fast ⟨T, b₀, b₁⟩
```

Its complete definition is Claims/Outage:144; P1Concl is Claims/Outage:114.
The complete existing public supplier boundary is Outage/Export:334/:406.
Port its body to the scoped result and the named Clean/arming producers. The old
all-honest supplier declarations and noRestart/duties_and_outputs calls are failed
port sites, not active sleep inputs or new supplier requests.

## Failed consumer map

```text
┌───────────────────────────┬─────────────────────────────────────────────────────────┐
│ Consumer                  │ Required work                                           │
├───────────────────────────┼─────────────────────────────────────────────────────────┤
│ ContinuationReceipt       │ Port to ScopedPaths:100/185/379. No new receipt         │
│                           │ producer.                                               │
│ ContinuationInduction     │ Port to ScopedBridge:59/292 and ScopedEarly current     │
│                           │ finite cuts.                                            │
│ ContinuationJoint         │ Use ScopedCatchUp public consumers; discharge exact     │
│                           │ O11-W-SEED.                                             │
│ Close                     │ Use ScopedClose protected result; actual initial arming │
│                           │ and Clean facts.                                        │
│ Outage.Export             │ O12-PUBLIC-OUTAGE. Protected producer is proved;        │
│                           │ complete body is open.                                  │
│ OutageContinuation.Export │ O12-PUBLIC-CONT and O11-W-SEED. Complete public body is │
│                           │ open.                                                   │
└───────────────────────────┴─────────────────────────────────────────────────────────┘
```

These six entries remain EXPECTED-FAIL. The complete consumer build was run:
Close still projects Base2.noRestart and calls duties_and_outputs;
ContinuationInduction still calls the removed outage_arming_local. Neither complete
exporter is GREEN. GrowthSuppliers' public import remains intact.
A separate ContinuationReceipt build also fails at stale helper signatures and
missing awake guards for old unconditional tick selection. No new receipt
producer is needed; use the existing actual-read scoped path and epoch proofs.

## SCOPE-NARROW table

YES means true under the stated regime, actual event, epoch or branch. The OPEN
W seed row identifies a goal without certifying an unproved producer. Ordinary
sleep, restart at GST, suppressed gates and exclusion remain in the theorem
premises. No service is inferred from joinedness alone. Cross-node service is
still restricted to the caller's actual post-GST source/read cuts.

```text
┌─────────────────────┬─────────────────────┬───────────────────────┬───────────────────────┐
│ Input               │ Status / owner      │ Producer / guard      │ Sleep assessment      │
├─────────────────────┼─────────────────────┼───────────────────────┼───────────────────────┤
│ Run; h / hO         │ Given               │ Actual finite sleep   │ YES on premise        │
│                     │                     │ premise               │                       │
│ hf; source facts    │ Named P-Fd          │ P-Fd producers below  │ YES; actual source    │
│ origin; FaultQ      │ Named P-Fd          │ qcOrigin, existing    │ YES; no new quorum    │
│                     │                     │ quorum                │                       │
│ hState              │ Named P-Cl1         │ cleanState_of_hist    │ YES; actual cut       │
│ hHist               │ Named P-Cl1         │ clean_invariant       │ YES; enabled history  │
│ hOutput             │ Named P-Cl1         │ clean_gateOutput_body │ YES; enabled gates    │
│ hprov               │ Proved              │ outage_joined_provena │ YES; actual joined    │
│                     │                     │ nce                   │ read                  │
│ htransfer           │ Named P-Cl1         │ cleanHistoryAt_body   │ YES; actual joined    │
│                     │                     │                       │ HEAD                  │
│ B; hne              │ Selected            │ Initial confirmed     │ YES in non-genesis    │
│                     │                     │ read                  │ arm                   │
│ hc                  │ Named P-Ar / proved │ Fast/slow; empty G    │ YES on branch         │
│                     │                     │ cert                  │                       │
│ beta; hBeta         │ Proved              │ protected_initial_lif │ YES; actual Clean     │
│                     │                     │ t                     │ origin                │
│ hEmpty              │ Local split         │ G = empty             │ YES only in this arm  │
│ hReg; hFirst        │ Proved branch       │ First actual emission │ YES in regression arm │
│ hResults; hF        │ Proved              │ ScopedBridge event    │ YES; bounded prefix   │
│                     │                     │ state                 │                       │
│ G stable seed       │ Proved              │ ScopedPrefix vote     │ YES with actual       │
│                     │                     │ seed                  │ horizon               │
│ s; j; enabled gate  │ Proved              │ caught_up_gate_scope  │ YES; actual W read    │
│ Batch; awake; epoch │ Proved              │ caught_up_gate_scope  │ YES; exact receiver   │
│                     │                     │                       │ epoch                 │
│ hLow at j           │ Local split         │ F monotonic from j to │ YES in low arm        │
│                     │                     │ t                     │                       │
│ S at j+1            │ OPEN P-Ou           │ Exact O11-W-SEED      │ Guarded goal;         │
│                     │                     │ below                 │ unproved              │
│ Suffix S; outputs   │ Proved consumer     │ public_read_from_seed │ YES if seed supplied  │
│ Pure hS / hC / hF   │ Produced at caller  │ Seed, result and      │ YES; joined hC guard  │
│                     │                     │ frame                 │                       │
│ Legacy NoRestart    │ No active input     │ Failed port only      │ Not requested         │
└─────────────────────┴─────────────────────┴───────────────────────┴───────────────────────┘
```

## Validation

DCK P-Ou PASS: 44 strict sources; 3,313 results; all 24 default controls PASS.
Map: 62 TARGETS; 523 GREEN; eight EXPECTED-FAIL, six P-Ou and two S-Ap.
Headers PASS: 1,740 library files; zero failures. Layers: 72 inherited, zero new.
Complete GREEN exports: 342 proof modules; 253 exports; zero unaccepted; Gen zero.
Local coverage: 349 commands; home-equation control PASS; zero unaccepted.
Serial production audit: 313 results; only propext, Classical.choice, Quot.sound.
Contracts.lean proves the exact original early read/HEAD/F/duty, W-read and
protected-B outage types. O11-W-SEED is checked as a Prop and is not proved.
Both complete public exporters were built and fail at the listed legacy ports.
Evidence: .lake/sleep-pou-r12/. No public claim or protocol change; no public STOP.

No new complete finite ExecutionValid fixture was added. The existing tests include
the restart-at-9, GST=20, k=2, s=3 and restart-at-GST guard cases. The new theorems
retain Base2.valid and scope actual emissions, enabled gates and local epochs.
They do not assert prior-label join from a later gate or pre-GST delivery from join.
The exclusion alternatives stay in the existing batch/result producers.
