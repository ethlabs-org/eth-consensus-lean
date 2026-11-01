# P-Ou Round 13 handoff

Base: de637290. Branch: sleep-pou13.
Proof groups: d65236ae and b35a3548.
Status: PREPARED. The full Round 13 task is incomplete.
O11-W-SEED is still OPEN, P-Ou. No public counterexample is established.
Both complete exporter modules are GREEN under strict audits. The continuation
exporter is conditional on the exact W seed. This does not close the package.
Public claims, protocol declarations and Healing files are unchanged.

## Produced proof groups

- W gate live rows: ScopedCatchUp:288, outage_caught_up_gate_rows.
  Incompatible old rows expire by handover. Later enabled results come from
  the scoped event producer. This does not prove S compatibility at j+1.
- Arming: ScopedArming:53, outage_scoped_arming. It selects fast, slow and
  empty-G certificates. It derives joined provenance at the actual duty.
- Finite Clean inputs: Assembly/OutagePublicInputs:13, outage_clean_cut_supplier.
  It constructs every field of ScopedArming:15, OutageCleanCutInputs.
  Named leaves are cleanState_of_hist, clean_invariant, clean_gateOutput_body,
  cleanHistoryAt_body and clean_epoch_saved_row. The saved-row input retains
  the actual receiver window, epoch, origin and F alternative.
- Protected Outage body: Close:29/:55. It uses its own OutagePrem and the
  proved ScopedClose result. It requests no continuation regime or synchrony.
- Public Outage supplier: Assembly/OutagePublicInputs:34, outage_public_suppliers.
  Its full type is `OutageCompatClaim p`, with every input produced. Fast P1
  and slow P1 are tested at the unchanged public types.
- Complete scoped continuation body: ScopedJoint:29,
  outage_continuation_scoped_body. It selects arming for each actual initial
  read and joins the Round 12 public read, HEAD and F producers.
- OutageContinuation.Export:16 and Outage.Export:233/:290 compile. Their public
  result types are unchanged. The continuation seed input remains open.

All paths above are under AvailableChainFGSAProofs/Proofs unless marked otherwise.
The cited declarations contain the full Lean types and caller context.
Clean.Export exposes only two existing producer modules: EpochSaved and GateOutput.
The foundation record conversion keeps hf.cumul.1 and hf.cumul.2 separate.

## Exact remaining O11-W-SEED

The complete common caller context is ScopedJoint:13-36. It has the actual
continuation sleep premise, hf, hsrc, htsrc, emitted named rows, hClean and origin.
Scoped arming selects hc and beta for each non-genesis initial protected B.
Genesis is handled by prefix order. No marker or first-event input is assumed.
The goal is unchanged from Round 12. It is OutageWSeed in ScopedCatchUp:341;
OutageWSeed_def at :354 checks its exact expansion:

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

Caller: ScopedCatchUp:370, outage_continuation_public_reads, at the actual
post-E W gate selected by outage_caught_up_gate_scope. The low-F test at j
comes from F monotonicity to the actual inclusive public read.
ScopedJoint:29 and OutageContinuation.Export:16 expose only this remaining
producer obligation. They are consumers of the goal, not its producer.

The new row theorem removes incompatible live leases at this gate. Raw result
compatibility is already proved. These two facts do not establish the stable
seed. The proof must still resolve the gate's actual result and old S branch.
GridCO.advance retains old S when the candidate is its ancestor. No proof here
excludes an incompatible retained S in the complete caller context. No full
finite-run counterexample to the public claim is asserted.

## Consumer map

```text
┌───────────────────────────┬───────────────────────────┬────────────────────────────┐
│ Consumer                  │ Status                    │ Route                      │
├───────────────────────────┼───────────────────────────┼────────────────────────────┤
│ ContinuationReceipt       │ GREEN                     │ ScopedPaths; actual joined │
│                           │                           │ read paths                 │
│ ContinuationInduction     │ GREEN                     │ ScopedBridge and           │
│                           │                           │ ScopedEarly finite cuts    │
│ ContinuationJoint         │ GREEN, conditional        │ ScopedJoint:29; exact W    │
│                           │                           │ seed OPEN                  │
│ Close                     │ GREEN                     │ ScopedArming:53 and        │
│                           │                           │ ScopedClose:171            │
│ Outage.Export             │ GREEN; producer proved    │ Assembly/OutagePublicInput │
│                           │                           │ s:34                       │
│ OutageContinuation.Export │ GREEN, conditional        │ ScopedJoint:29; exact W    │
│                           │                           │ seed OPEN                  │
│ Assembly.Outage           │ P-As repair               │ Three caller sites: 250,   │
│                           │                           │ 264, 278                   │
│ Assembly.Root             │ P-As port after P-Ou seed │ Root:160; no new public    │
│                           │                           │ seed premise               │
└───────────────────────────┴───────────────────────────┴────────────────────────────┘
```

The six P-Ou entries from Round 12 are GREEN. The three legacy continuation
modules are ports to the scoped producers. The obsolete helpers had no current
production caller. Their exact original files remain in Git at de637290 and
in .lake/sleep-pou-r13/legacy/. Typed audits now check the current scoped types.
No audit wrapper was dropped; duplicate wrappers have distinct names.
The package map has 69 targets, 536 GREEN and two S-Ap EXPECTED-FAIL entries.

## Exact P-As requests

1. Assembly/Outage:243/:261/:275: replace the three obsolete wrapper bodies.
   Copy outage_clean_cut_supplier from Assembly/OutagePublicInputs:13 into
   the existing Assembly/Outage module as assembly_outage_clean_cut_supplier.
   Its current imports already expose every leaf through Clean.Export.
   A direct import of an Assembly sibling is forbidden by the current layer rules.
   Preserve the existing CleanCutClaim argument; it can be named _hcut.
   Use these exact current suppliers:

```lean
outage_outageCompatClaim_of p (fgsa_fgFoundationClaim p) (fgsa_srcFrameAboveClaim p)
  (fgsa_sourceDisciplineClaim p) (assembly_outage_clean_cut_supplier p)
```

   Apply its true-case P1 projection for FastP1Claim and its false case for
   SlowP1Claim. The exact replacement proofs compile in
   .lake/sleep-pou-r13/AssemblyRequests.lean; evidence: assembly-requests.log.
   The current Assembly/Outage build fails only at these three caller sites:
   outdated hstore and hnamed parameters. Evidence: p-as-consumer.log.
2. Assembly/Root:160: port the foundation and Clean arguments to the new
   exporter boundary. The exact continuation_from_seed adapter is compiled
   in AssemblyRequests.lean. It uses the actual named supplier bundle and
   takes exactly OutageWSeed. P-Ou must prove the seed before this can close
   the unconditional Root theorem. Add no seed premise to a public claim.
3. Integrate the production-only audit fragment and local coverage rows under
   the existing full proof audit key. Import production modules for each printed
   declaration. Keep test imports out of the serial production audit.
4. The two package-map EXPECTED-FAIL entries remain S-Ap: AvailableChainFGSARun
   and AvailableChainFGSARun.Tests.Axioms. They are outside this repair group.

## SCOPE-NARROW 1-5

Proved and named inputs have actual finite-cut producers. Receipt requests use
selected witnesses, receiver floors, actual joined readers and local epochs.
Gates are enabled. Cross-node service retains the source's actual GST cut.
Joinedness supplies no pre-GST deadline. The W seed is OPEN and is not certified
TRUE in any of the requested ordinary finite sleep scenarios.

```text
┌────────────────────┬────────────────────┬────────────────────┬────────────────────┐
│ Input              │ Status             │ Producer           │ Guard              │
├────────────────────┼────────────────────┼────────────────────┼────────────────────┤
│ h / hO             │ Given              │ Actual public      │ Finite run and     │
│                    │                    │ sleep premise      │ horizon            │
│ hf                 │ Named P-Fd         │ fgsa_fgFoundationC │ Source premise;    │
│                    │                    │ laim               │ durable / epoch    │
│                    │                    │                    │ split              │
│ hsrc; hdisc        │ Named P-Fd         │ fgsa_srcFrameAbove │ Actual sources and │
│                    │                    │ Claim; sourceDisci │ emitted rows       │
│                    │                    │ plineClaim         │                    │
│ FaultQ             │ Proved             │ pre.faultQ_of_pos; │ Positive healthy   │
│                    │                    │ outage_cut_pos     │ cut                │
│ hClean.state       │ Proved             │ outage_clean_cut_s │ i <= timeIdx(b0)   │
│                    │                    │ upplier            │                    │
│ hClean.history     │ Proved             │ clean_invariant in │ Actual finite      │
│                    │                    │ supplier           │ Clean cut          │
│ hClean.output      │ Proved             │ clean_gateOutput_b │ Enabled gates      │
│                    │                    │ ody in supplier    │ before cut         │
│ hClean.transfer    │ Proved             │ cleanHistoryAt_bod │ Actual joined HEAD │
│                    │                    │ y in supplier      │ reader             │
│ hClean.saved       │ Proved             │ clean_epoch_saved_ │ Awake window; own  │
│                    │                    │ row in supplier    │ epoch; F           │
│                    │                    │                    │ alternative        │
│ hprov              │ Proved             │ outage_joined_prov │ Actual duty and    │
│                    │                    │ enance             │ local prior tick   │
│ B; hne             │ Selected           │ Initial confirmed  │ Actual initial     │
│                    │                    │ read; genesis      │ public read        │
│                    │                    │ split              │                    │
│ hc                 │ Proved             │ outage_scoped_armi │ Fast / slow /      │
│                    │                    │ ng                 │ empty G branch     │
│ beta; hBeta        │ Proved             │ protected_initial_ │ Selected Clean     │
│                    │                    │ lift               │ origin             │
│ origin             │ Named P-Fd         │ SourceDisciplineAt │ Actual stored      │
│                    │                    │ .2.2               │ carrier and source │
│                    │                    │                    │ quorum             │
│ hResults; hF       │ Proved             │ ScopedBridge event │ Actual finite      │
│                    │                    │ state              │ event prefix       │
│ HEAD / paths       │ Proved             │ ScopedBridge /     │ Selected carrier;  │
│                    │                    │ ScopedPaths        │ reader floor;      │
│                    │                    │                    │ join; GST cut      │
│ s; j; batch; epoch │ Proved             │ caught_up_gate_sco │ Actual enabled W   │
│                    │                    │ pe                 │ gate and receipt   │
│                    │                    │                    │ epoch              │
│ low-F test         │ Local split        │ F monotonicity to  │ Only the low-F     │
│                    │                    │ actual read        │ branch             │
│ W gate live rows   │ Proved             │ caught_up_gate_row │ s >= restoredLabel │
│                    │                    │ s                  │ + k                │
│ S at j+1           │ OPEN, P-Ou         │ Exact OutageWSeed  │ Truth not          │
│                    │                    │ goal               │ certified; no      │
│                    │                    │                    │ producer yet       │
│ W suffix output    │ Conditional        │ public_read_from_s │ Needs the exact W  │
│                    │ consumer           │ eed                │ seed               │
│ Legacy NoRestart   │ No active input    │ Retired failed     │ No public exporter │
│                    │                    │ helpers            │ request            │
└────────────────────┴────────────────────┴────────────────────┴────────────────────┘
```

The proofs retain the ordinary sleep, restart-at-GST, restart-at-9, GST=20,
k=2/s=3, suppressed-gate and exclusion guards. Existing guard fixtures compile
under DCK. No new complete finite ExecutionValid fixture was added.
The actual Clean supplier is proved from HealthyPrefixSleep₂ and FaultQ; no
all-honest join, unconditional saved row or future restored-seed cut is requested.

## Validation and saved evidence

All paths below are under .lake/sleep-pou-r13/.

- dck.log: DCK P-Ou PASS; 48 strict sources, 3,401 results; all 24 controls PASS.
- layers.log: 72 inherited findings, zero new.
- headers.log: PASS; 1,744 library files; zero failures.
- exports.log: 375 proof modules; 253 exports; zero unaccepted; Gen zero.
- coverage.log: 367 local rows; home-equation control PASS; zero unaccepted.
- serial.log and serial-strict.log: 329 results; standard axioms only.
- public-exporters.log and assembly-suppliers.log: both complete exporters
  and the actual Outage supplier compile. Final --wfail evidence is in dck.log.
- w-rows-audit.log: strict W gate row audit; the W seed is checked as a Prop.
- contracts.log: exact original Round 11/12 solved contracts compile with the
  required Claims import. The W seed is type-checked and is not proved.
- assembly-requests.log: four exact P-As adapters compile with standard axioms.
- p-as-consumer.log: the three remaining P-As caller failures are saved.

Round 11's OpenTypes PASS statement was incorrect. O11-OUTAGE failed there
because Claims imports were absent. The Round 11 handoff and report are corrected;
the successful Round 13 Contracts rerun is the current evidence.
No checker, allowance or baseline was changed. New Lean lines are at most 100.
