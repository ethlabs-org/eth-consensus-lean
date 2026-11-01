# P-Ou Round 8 handoff

Base: d8964408. Branch: sleep-pou8. Proof groups: 3d644dca, 9fdada2a.
P-Ou is PREPARED, not CLOSED. Public claims and protocol declarations are unchanged.
The full continuation closure requested for Round 8 is not complete.
This handoff supersedes Round 7 for prefix receipt, inclusion services and post-E counts.

## Completed producers

RestoredBatch:388, outage_continuation_receipt, consumes P-Ar's
arming_continuation_prefix_receipt. Tests/OutageServices:18 uses the regime-only result.
The P-Ar request is discharged. The earlyTime(q) <= b₀ guard remains in its producer.

ReceiverInputs:982, inclusion_receiver_inputs, constructs the complete narrowed record.
:1059, inclusion_receiver_inputs_of_clean, supplies it from the actual Clean sleep regime.
:1045 proves the full synchrony projection from the Clean cut and GST=0.
Suppliers:151 supplies the export adapter. No assumed hInputs callback remains.

Early service has an actual early tick, the vote-time GST cut, and F_receiver <= K.
Retained service has the prior-label GST cut and F_receiver <= N.erase.
ExactProposalRetained:325 proves the cone first; :820 derives the proposal floor
before service is requested. The existing inclusion_retained_reads name/type is kept.
All retained score floors get services from InclusionServices, including frozen HEADs
and both directions of named-body transfer. Each field uses its exact anchor and epoch.

The relay step is local. RelayKernel gives HEAD pool provenance from the actual joined
tick. It requests no cross-node service for a late local pool entry. For example,
Delta=2, r=1, GST=0, and a first honest acceptance at y at 17 permit peer receipt at 19.
The local pool at v(2)=18 can already contain the vote. The old relay field still
requested cross-node service before 18. This internal field was removed.

InclusionGateService now takes the actual enabled gate and produces receipt scope
from its target floors. InclusionGateBody:16 proves the gate was enabled for the
caught-up post-tick reader. The hScopes export callback is removed. The three changed
Clean exporters compile independently in .lake/sleep-pou-r8/CleanExportConsumer.lean.
The whole Outage exporter still fails on its inherited outage closure dependencies.

RelayKernel and InclusionServices port the needed merged P-WC kernels into the
Outage lane. Cross-family imports are forbidden by LANE. No other owner source changed.

## Restored and healthy counts

ReceiverInputs:837, outage_healthy_result_of_compatible_heads, uses the healthy joined
set and the faulty count. It needs only fresh HEAD receipt, not target-body receipt.
:1064, outage_post_e_joined_count, derives the strict count at each actual post-handover
vote inside the horizon. It does not extend the fixed A union W count beyond E.
:1078 proves the canonical FirstRestored label.
:1097, outage_continuation_results_of_head_history, covers every enabled honest gate
with r < s. It uses E on r..r+k+1 and the healthy set after that window.
Every service has the vote-time GST cut derived from h.gst and FirstRestored.

The one remaining invariant input to this adapter is exactly:

```lean
∀ s q K, restoredLabel p b₁ < s →
  outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
    (SA.voteTime p.toParams s) →
  HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
    (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
  Block.Compatible K B
```

This is OPEN P-Ou work. The adapter is conditional, not unconditional global hResults.
The full joint induction must produce this history. Do not replace it with a future
callback, an all-honest seed, or NoRestart. Later conditional hTargets remain open.

## P-Cl2 growth and P-As handoff

GrowthSuppliers:15, clean_growth_suppliers, produces the inclusive gate witness and
both callbacks required by Outage/Growth:24/:30 from the closed field interfaces.
It supplies all inclusion and gate service records itself.
Tests/OutageGrowthSuppliers:20, growth_suppliers_from_clean, supplies every field from
cleanHistoryAt_body, cleanTruncAt_body and the actual Foundation producers.
Tests/OutageGrowthSuppliers:86, growth_claim_from_producers, compiles the exact unfolded
P20 production consumer with those callbacks. No hInputs, hScopes, compatibility or
inclusion assumption remains in that tested composition.

P-As must apply this checked cross-lane composition in Assembly/Outage. Its code is
in the independent test; copy the production imports and body, never import the test.
The production GrowthSuppliers module stays inside its lane and takes field interfaces.
Public assembly closure is not claimed from a test. No P-As source was edited.
P-As must also remove the named hInputs/hScopes arguments from its three Clean calls
into Outage/Export. Their services now have actual producers in P-Ou.

## Exact remaining P-Ou work

- Produce later scoped good-HEAD compatibility and the conditional target invariant.
- Use that invariant to discharge the global result adapter, including the post-E case.
- Port ContinuationInduction:37 and ContinuationJoint:671/:871 through all restored
  labels, expiry handover and the healthy suffix. Their NoRestart/all-honest lane remains.
- Port Close:84 and the complete Outage/Export and OutageContinuation/Export consumers.
- Apply the existing deadline and row-handover consumers to the produced global results.

These are owned proof tasks. They are not missing P-Ar prefix or inclusion-service inputs.
No public premise or meaning change is proposed. No public STOP is claimed.

## Registration and validation

51 TARGETS, 511 GREEN, 9 EXPECTED-FAIL: seven P-Ou and two S-Ap.
The four new targets are RelayKernel, InclusionServices, GrowthSuppliers, and the
independent OutageGrowthSuppliers test. GREEN records compilation, not family closure.

DCK PASS: 43 strict sources, 3,221 results, all 24 default controls PASS.
Complete GREEN exports: 331 proof modules, 253 exports, zero unaccepted, zero Gen exports.
Complete local coverage: 257 commands; its control PASS; zero unaccepted.
Production-only serial fragment: 231 strict results, with no test-module import.
Headers PASS: zero failures. Layers: 72 inherited findings, zero new.
Only propext, Classical.choice and Quot.sound occur in the strict audits.
All added Lean lines are at most 100 characters. Whitespace and ownership pass.
No proof placeholder, project axiom, unsafe evaluation, heartbeat increase,
checker/baseline/allowance/toolchain change, review, agent, push, rebase, merge or ssh.
No throttle override or lake update. Only own blocked build processes were stopped.

Evidence: .lake/sleep-pou-r8/dck.log, exports.log, coverage.log, serial-audit.log,
clean-exports.log, headers-final.log, layers-final.log and group-build.log.
The audit and coverage fragments use the existing canonical key for serial integration.

## SCOPE-NARROW input audit

YES means true with the stated event, floor, prefix, GST or conditional branch.
It does not certify an unproduced future invariant. Fields from closed owners have
an actual composition test. Production assembly wiring remains a separate handoff.
Repeated inputs are grouped by role. This table includes the Round 7 roles and all
Round 8 service, count, growth and local provenance roles.

```text
┌──────────────────────┬─────────────────────┬──────────────────────┬──────────────────────┐
│ Input                │ Status / owner      │ Producer or guard    │ True in sleep runs   │
├──────────────────────┼─────────────────────┼──────────────────────┼──────────────────────┤
│ p,c,E,rho; labels    │ Given               │ Actual model objects │ Structural           │
│ Base2; hs; hdelta    │ Producer P-Fd       │ Regime Base2 fields  │ YES                  │
│ roots; receipt roots │ Producer Base2      │ Base2.idealization   │ YES, scoped          │
│ h; hSync; hGST       │ Given regimes       │ Healthy /            │ YES on premise       │
│                      │                     │ continuation         │                      │
│ hDelivery; cut       │ Producer            │ withinOn of regime   │ YES in cut           │
│ hStart; hPub         │ Proved at caller    │ Exact public anchor  │ YES, exact anchor    │
│ hDeadline; hCR       │ Proved at caller    │ Phase arithmetic     │ YES, exact read      │
│ hhor; hCut; hgate    │ Proved at caller    │ Cut / actual tick    │ YES, finite horizon  │
│ hx; hy; hJ           │ Producer            │ Actual reader /      │ YES, named nodes     │
│                      │                     │ source               │                      │
│ hG; readEpoch        │ Producer            │ PersistenceSleep:192 │ YES, enabled only    │
│ ht; hTarget; hfast   │ Producer TSrc       │ Actual action / HEAD │ YES, guarded         │
│ hC; hresult          │ Actual event        │ Executed result      │ YES when nonempty    │
│ hNX; ready; history  │ Producer            │ Exact object service │ YES, admissible      │
│ hf; hsrc; htsrc      │ Producer P-Fd       │ Foundation / sources │ YES on premise       │
│ hq                   │ Given supplier      │ FaultQ supplier      │ Conditional          │
│                      │                     │ input                │                      │
│ hState; hHist        │ Producer P-Cl1      │ Clean/Closure:128    │ YES with hq          │
│ htransfer            │ Producer P-Cl1      │ Clean/Closure:220    │ YES, joined reader   │
│ hprov                │ Producer P-Cl1      │ Clean/Service:719    │ YES, actual HEAD     │
│ hc (general)         │ Producer P-Ar       │ ArmingConstruction:3 │ YES, equal cut       │
│                      │                     │ 98                   │                      │
│ hread; hne           │ Selected witness    │ Protected output     │ YES, chosen B        │
│ hbeta; named scope   │ Selected witness    │ Actual FG / root     │ YES, named body      │
│                      │                     │ lift                 │                      │
│ hnamed               │ Producer P-Fd       │ Sources:180 + views  │ YES, emitted rows    │
│ hSource; hRows       │ Proved P-Ou         │ ReceiverInputs:506/5 │ YES, includes W      │
│                      │                     │ 41                   │                      │
│ bad; hfault; hbad    │ Proved P-Ou         │ Faults or A union W  │ YES, explicit bound  │
│ E1; hBound           │ Proved P-Ou         │ ReceiverInputs:708   │ YES, before recovery │
│ H; hCount; hpart     │ Producer from E     │ GoodVotes:20/89      │ YES in E window      │
│ hSelected; hrest     │ Proved P-Ou         │ Joined seats /       │ YES, all receivers   │
│                      │                     │ origin               │                      │
│ hlow / hBF           │ Local case split    │ F <= B / B <= F      │ YES, branch only     │
│ hFB at late gates    │ Proved on history   │ ScopedInduction:69   │ YES with sources     │
│ hTargets after r     │ Open P-Ou           │ Later good duty      │ Not yet certified    │
│                      │                     │ proof                │                      │
│ hHeads good set      │ Proved before r     │ ScopedInduction:28   │ OPEN after r         │
│ selected services    │ Producer P-Ou       │ ReceiverInputs:618   │ YES with low targets │
│ shared scope adapter │ Conversion only     │ GoodVotes:182        │ Not a producer       │
│ hResults after r     │ Open P-Ou           │ 1097 needs HEAD      │ Conditional only     │
│                      │                     │ history              │                      │
│ deadline hResults    │ Open P-Ou           │ 1097 actual prefix   │ Not yet certified    │
│                      │                     │ input                │                      │
│ Inclusion early      │ Producer P-Ou       │ ReceiverInputs:943/9 │ YES, GST + floor     │
│                      │                     │ 82                   │                      │
│ Inclusion relay      │ Local producer      │ RelayKernel local    │ YES, actual tick     │
│                      │                     │ provenance           │                      │
│ Inclusion retained   │ Producer P-Ou       │ InclusionServices    │ YES, GST + floor     │
│                      │                     │ score floors         │                      │
│ NoRestart lane       │ Removed Induction   │ Legacy continuation  │ Not a sleep input    │
│ all-honest seeds     │ Removed Induction   │ G seed + in-flight   │ YES, scoped seed     │
│ continuation prefix  │ Producer P-Ar       │ ArmingKernel:901 +   │ YES, prefix cut      │
│                      │                     │ RestoredBatch:388    │                      │
│ sender; hinj; bad    │ Explicit witnesses  │ Release:187          │ YES, actual seats    │
│ hbad release rule    │ Proved P-Ou         │ GoodVotes:413        │ YES, A union W       │
│ hDuty covered        │ Proved P-Ou         │ ScopedInduction:81   │ YES before restore   │
│ hSeed in-flight      │ Producer P-Ar       │ ArmingDutySleep:299  │ YES, actual emission │
│ hLocal G seed        │ Produced P-Ou       │ ReceiverInputs:558   │ YES, G only          │
│ hr; hcut; hend       │ Regime + cert       │ 351: E1 / budget     │ YES before restore   │
│ hI; hK; hBefore      │ Actual prefix       │ Tick time and index  │ YES, bounded events  │
│ late HEAD services   │ Produced P-Ou       │ ReceiverInputs:757   │ YES, enabled gate    │
│ late target bodies   │ Not requested       │ GoodVotes:559        │ May be below F       │
│ result good history  │ Open P-Ou           │ 1097 scoped HEADs    │ Not yet certified    │
│ post-E counts        │ Producer P-Ou       │ ReceiverInputs:1064  │ YES from handover    │
│ scoped read t        │ Proved P-Ou         │ ScopedInduction:386  │ YES before restore   │
│ raw test joined      │ Actual guard        │ gateStep_fresh:271   │ YES, joined only     │
│ restart test wake    │ Model argument      │ Kept durable rows    │ YES at exact wake    │
│ early ie/hie         │ Actual tick         │ ReceiverInputs:943   │ YES, finite read     │
│ early hFloor         │ Produced at caller  │ Retained cone frame  │ YES, selected K      │
│                      │                     │ bound                │                      │
│ retained hFloor      │ Produced at caller  │ ExactProposalRetaine │ YES before service   │
│                      │                     │ d:820                │                      │
│ prior vote GST       │ Produced Clean      │ ExactProposalReceipt │ YES, GST=0           │
│                      │                     │ s:18                 │                      │
│ proposal GST         │ Produced from prior │ InclusionServices    │ YES, later anchor    │
│                      │                     │ current duty         │                      │
│ score geometry D     │ Selected floor      │ Source and receiver  │ YES, selected D      │
│                      │                     │ F <= D               │                      │
│ sourceEpoch          │ Produced locally    │ Current proposal     │ YES, exact epoch     │
│                      │                     │ join                 │                      │
│ frozenHeads          │ Producer P-Ou       │ RelayKernel          │ YES, exact anchor    │
│                      │                     │ acceptance origin    │                      │
│ forward/backward     │ Producer P-Ou       │ InclusionServices:   │ YES, per floor       │
│                      │                     │ accepted body        │                      │
│ late local HEAD      │ No service request  │ Joined-tick pool     │ YES, no GST needed   │
│                      │                     │ provenance           │                      │
│ old relay callback   │ Removed             │ Late local receipt   │ FALSE in some runs   │
│                      │                     │ counterexample       │                      │
│ old early callback   │ Narrowed            │ Target below         │ Needs caller floor   │
│                      │                     │ receiver F           │                      │
│ gate hTargets        │ Produced locally    │ Exact emitted        │ YES, actual gate     │
│                      │                     │ proposal HEAD        │                      │
│ gate hScope          │ Produced P-Ou       │ ReceiverInputs:1014  │ YES, GST + targets   │
│ caught-up gate       │ Produced P-Ou       │ InclusionGateBody:16 │ YES, actual tick     │
│ hOrdered/hBounds     │ Producer P-Cl2      │ Clean history        │ YES, finite cut      │
│                      │                     │ projections          │                      │
│ hOutputs/hOrigins    │ Producer P-Cl2      │ Truncation + gate    │ YES, bounded reads   │
│                      │                     │ output               │                      │
│ growth field inputs  │ Closed owner fields │ GrowthSuppliers:15   │ YES, exact test      │
│ growth regime call   │ Actual composition  │ Tests/OutageGrowthSu │ YES, kernel check    │
│                      │                     │ ppliers              │                      │
│ growth assembly      │ Handoff P-As        │ Use actual tested    │ Not yet integrated   │
│                      │                     │ producers            │                      │
│ hHeads global        │ Open P-Ou           │ outageHeadReader at  │ Not yet produced     │
│                      │                     │ emission             │                      │
│ restored count       │ Producer from E     │ r <= s <= r+k+1      │ YES, E window        │
│ healthy count        │ Producer regime     │ s >= r+k+1; horizon  │ YES after E          │
│ result hGST          │ Produced regime     │ FirstRestored + gst  │ YES, vote anchor     │
│                      │                     │ <= b1                │                      │
│ r canonical          │ Proved P-Ou         │ ReceiverInputs:1078  │ YES, least label     │
└──────────────────────┴─────────────────────┴──────────────────────┴──────────────────────┘
```
