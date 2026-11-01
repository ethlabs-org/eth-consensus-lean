# P-Ou Round 9 handoff

Base: afc304e6. Branch: sleep-pou8. Later HEAD group: 67447e61.
P-Ou is PREPARED, not CLOSED. Public claims and protocol declarations are unchanged.
The complete Round 9 closure task is not complete.
This handoff updates Round 8 for later marker transport, local gate results and
causal healthy-suffix induction. Its prefix, inclusion and growth handoffs still apply.

## Completed later HEAD work

LaterHeads:17 proves marker persistence through a restart with RMonoAll and the
durable FG tree. It requests no cross-epoch vote or stamp persistence.
:94 and :137 prove clocked root and contested HEAD compatibility from scoped names
and the current covered stable invariant.

LaterHeads:170, outage_later_marker_receipt, serves one stored marker at the actual
later joined HEAD read. The anchor is proposalTime(s+1), not the marker's old receipt
cut. The marker vote precedes that anchor, which is after GST. The current reader F
must be compatible with B; the low branch gives F <= B <= P. The finalized branch
uses F directly. The service uses an actual retained acceptance origin, exact
proposal history, actual tick horizon, and the receiver's joined epoch.

LaterHeads:246 combines this producer with the local named frame and compatible
live rows. It does not require B below the newly joined receiver's stable output.
:279 derives B <= K for an actual emitted protected HEAD before its lease expires.
:317 derives the receiver floor in the conditional F <= B branch. This does not
assert covering targets at every later label or at every newly woken receiver.

ReceiverInputs:1097 now supplies outage_continuation_result_of_head_history for one
actual enabled gate label. The existing global adapter forwards to it. E counts stay
inside r..r+k+1; the post-E case uses the actual healthy joined count and horizon.
ContinuationGate:118 ports outageV_restored_gate to that interface. Its gate-step
proof handles the suppressed branch by normalization. It no longer imports the
legacy ContinuationReceipt lane.

## Causal healthy suffix and deadlines

ScopedContinuation:19, outage_continuation_event_induction, carries global source
history, named rows, all-honest durable F compatibility, and G-only stable inclusion.
It handles restart, delivery, enabled gate and suppressed gate events. A restart
uses kept stableRecord. An enabled gate supplies its actual join guard. The generic
consumer takes results only for actual enabled gates in its bounded event prefix.

ScopedContinuation:139 proves that all rows at a post-handover HEAD read have passed
the expiry filter. A conflicting row has an actual write origin before or at r and
an exact deadline <= OutageEnd(r). Deadline equality removes the row.

ScopedContinuation:158, outage_marker_continuation_induction, jointly produces the
healthy suffix's HEAD and gate compatibility, source names, F compatibility, G-only
stable inclusion, and conflicting-row deadline bound. It consumes the actual marker
and a finite seed after gate(m), with r+k <= m. At each gate its HEAD read precedes
the gate index. Earlier results give the row bound at that read; source history at
that read gives the names. LaterHeads produces its marker service. The regime then
produces the gate count and fresh HEAD service. No future HEAD/result/service callback
and no all-honest stable seed remains in this suffix theorem.

ScopedContinuation:261 is the inclusive public-read adapter. It consumes the current
event invariant, including same-time and horizon deliveries.

## Exact remaining P-Ou work

The marker suffix has these finite prefix inputs, all owned by P-Ou:

```lean
hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams m))
hy : y ∈ rho.honest
hP : P ∈ (storeAt p c E rho k y).fg.TF
hBJ : FGBlock.Preceq B (heightView p P).J
hnz : (heightView p P).h_j ≠ 0
hm : restoredLabel p b₁ + p.k ≤ m
hStart : afterTicksIdx rho (SA.gateTime p.toParams m) ≤ I
hSeed : OutageSourceHistory p c E rho (eraseFG B) I
hCover : ∀ x ∈ coveredNodes p E rho fast b₀,
  Block.Preceq (eraseFG B) (S_at p c E rho I x)
hPrefix : ∀ j x s C, j < I → x ∈ rho.honest → restoredLabel p b₁ < s →
  enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
  Block.Compatible C (eraseFG B)
```

These are actual marker and finite-prefix goals, not a regime-only producer.
Do not assume that every run has a marker. The no-regression branch still needs its
own covering-HEAD induction. The first regression must be shown to be contested
using selected joined good voters, exact local retained services and the E count.
A marker before r+k also needs the restored-window bridge before using this suffix.

The full HEAD history after r remains OPEN until those finite goals are produced.
Later protected hTargets is proved only under actual protection and strict expiry.
Use compatibility for marker HEADs; do not strengthen them to covering targets.

ContinuationJoint:671/:871 and Close:84 still need the full scoped read/duty ports.
The public caught-up W output branch needs its actual post-E gate, batch receipt,
awake interval and epoch. G-only inclusion is not all-honest inclusion.
ContinuationInduction and ContinuationReceipt retain their legacy code and are
EXPECTED-FAIL. Both complete exporters remain EXPECTED-FAIL. No public change or
public counterexample STOP is claimed. No P-Ar or P-Cl1 supplier request was added.

## Counterexample checks

Tests/OutageLaterHeads:13 checks restart=9, delta=1: HEAD label 3 at 13 is suppressed
but its gate at 18 is joined. It therefore cannot certify a batch at that earlier
HEAD. :20 rejects GST=20 at the label-3 marker anchor 12. :26 permits the later
label-6 anchor 24. :32 rejects label 6 as an E-window count when r=2, k=2.
These are kernel-checked guard regressions, not complete execution counterexamples.
:38 composes marker service with the actual P-Fd RMonoAll producer.
The provided rev-ph1e sketches remain the full-run source evidence.

## Registration and validation

54 TARGETS; 515 GREEN; eight EXPECTED-FAIL (six P-Ou and two S-Ap).
GREEN records compilation, not family closure. New proof modules are LaterHeads and
ScopedContinuation. The new standalone test is OutageLaterHeads. ContinuationGate
moves to GREEN. Local coverage and the production-only serial fragment are current.

All new proof modules and guard tests pass exact default-heartbeat builds.
Headers PASS, zero failures. Layers: 72 inherited findings, zero new.
Complete export check: 334 proof modules, 253 exports, zero unaccepted, zero Gen exports.
DCK PASS: 44 strict sources, 3,245 results, all 24 default controls PASS.
Local coverage: 281 commands, control PASS, zero unaccepted.
Serial production-only audit: 250 strict results; only the three standard axioms.
Full evidence is recorded in the Round 9 report.
Evidence: .lake/sleep-pou-r9/. No checker, baseline, allowance or toolchain was changed.

## SCOPE-NARROW input audit

This 107-row table retains all Round 8 roles and adds the new marker and suffix roles.
YES means true with the stated event, floor, prefix, GST or branch guard.
OPEN finite seeds and the first marker are not certified regime-only producers.
The suffix theorem produces all future results from these finite inputs; it does not
supply the inputs itself. The wake and pre-GST runs fail the exact local guards.

```text
┌───────────────────────┬───────────────────────┬───────────────────────┬───────────────────────┐
│ Input                 │ Status / owner        │ Producer or guard     │ True in sleep runs    │
├───────────────────────┼───────────────────────┼───────────────────────┼───────────────────────┤
│ p,c,E,rho; labels     │ Given                 │ Actual model objects  │ Structural            │
│ Base2; hs; hdelta     │ Producer P-Fd         │ Regime Base2 fields   │ YES                   │
│ roots; receipt roots  │ Producer Base2        │ Both idealization     │ YES, exact root scope │
│                       │                       │ fields                │                       │
│ h; hSync; hGST        │ Given regimes         │ Healthy /             │ YES on premise        │
│                       │                       │ continuation          │                       │
│ hDelivery; cut        │ Producer              │ withinOn of regime    │ YES in cut            │
│ hStart; hPub          │ Proved at caller      │ Exact public anchor   │ YES, exact anchor     │
│ hDeadline; hCR        │ Proved at caller      │ Phase arithmetic      │ YES, exact read       │
│ hhor; hCut; hgate     │ Proved at caller      │ Cut / actual tick     │ YES, finite horizon   │
│ hx; hy; hJ            │ Producer              │ Actual reader /       │ YES, named nodes      │
│                       │                       │ source                │                       │
│ hG; readEpoch         │ Producer              │ PersistenceSleep:192  │ YES, enabled only     │
│ ht; hTarget; hfast    │ Producer TSrc         │ Actual action / HEAD  │ YES, guarded          │
│ hC; hresult           │ Actual event          │ Executed result       │ YES when nonempty     │
│ hNX; ready; history   │ Producer              │ Exact object service  │ YES, admissible       │
│ hf; hsrc; htsrc       │ Producer P-Fd         │ Foundation / sources  │ YES on premise        │
│ hq                    │ Given supplier        │ FaultQ supplier input │ Conditional           │
│ hState; hHist         │ Producer P-Cl1        │ Clean/Closure:128     │ YES with hq           │
│ htransfer             │ Producer P-Cl1        │ Clean/Closure:220     │ YES, joined reader    │
│ hprov                 │ Producer P-Cl1        │ Clean/Service:719     │ YES, actual HEAD      │
│ hc (general)          │ Producer P-Ar         │ ArmingConstruction:39 │ YES, equal cut        │
│                       │                       │ 8                     │                       │
│ hread; hne            │ Selected witness      │ Protected output      │ YES, chosen B         │
│ hbeta; named scope    │ Selected witness      │ Actual FG / root lift │ YES, named body       │
│ hnamed                │ Producer P-Fd         │ Sources:180 + views   │ YES, emitted rows     │
│ hSource; hRows        │ Proved P-Ou           │ ReceiverInputs:506/54 │ YES, includes W       │
│                       │                       │ 1                     │                       │
│ bad; hfault; hbad     │ Proved P-Ou           │ Faults or A union W   │ YES, explicit bound   │
│ E1; hBound            │ Proved P-Ou           │ ReceiverInputs:708    │ YES, before recovery  │
│ H; hCount; hpart      │ Producer from E       │ GoodVotes:20/89       │ YES in E window       │
│ hSelected; hrest      │ Proved P-Ou           │ Joined seats / origin │ YES, all receivers    │
│ hlow / hBF            │ Local case split      │ F <= B / B <= F       │ YES, branch only      │
│ hFB at late gates     │ Proved on history     │ ScopedInduction:69    │ YES with sources      │
│ hTargets after r      │ Partial P-Ou          │ LaterHeads protected  │ YES with hp; full     │
│                       │                       │ target                │ OPEN                  │
│ hHeads good set       │ Partial P-Ou          │ Contested / marker    │ First marker OPEN     │
│                       │                       │ HEAD                  │                       │
│ selected services     │ Producer P-Ou         │ ReceiverInputs:618    │ YES with low targets  │
│ shared scope adapter  │ Conversion only       │ GoodVotes:182         │ Not a producer        │
│ hResults after r      │ Partial P-Ou          │ Marker causal         │ YES in marker suffix  │
│                       │                       │ induction             │                       │
│ deadline hResults     │ Partial P-Ou          │ Marker induction      │ Finite prefix OPEN    │
│                       │                       │ results               │                       │
│ Inclusion early       │ Producer P-Ou         │ ReceiverInputs:943/98 │ YES, GST + floor      │
│                       │                       │ 2                     │                       │
│ Inclusion relay       │ Local producer        │ RelayKernel local     │ YES, actual tick      │
│                       │                       │ provenance            │                       │
│ Inclusion retained    │ Producer P-Ou         │ InclusionServices     │ YES, GST + floor      │
│                       │                       │ score floors          │                       │
│ NoRestart lane        │ Removed Induction     │ Legacy continuation   │ Not a sleep input     │
│ all-honest seeds      │ Removed Induction     │ G seed + in-flight    │ YES, scoped seed      │
│ continuation prefix   │ Producer P-Ar         │ ArmingKernel:901 +    │ YES, prefix cut       │
│                       │                       │ RestoredBatch:388     │                       │
│ sender; hinj; bad     │ Explicit witnesses    │ Release:187           │ YES, actual seats     │
│ hbad release rule     │ Proved P-Ou           │ GoodVotes:413         │ YES, A union W        │
│ hDuty covered         │ Proved P-Ou           │ ScopedInduction:81    │ YES before restore    │
│ hSeed in-flight       │ Producer P-Ar         │ ArmingDutySleep:299   │ YES, actual emission  │
│ hLocal G seed         │ Produced P-Ou         │ ReceiverInputs:558    │ YES, G only           │
│ hr; hcut; hend        │ Regime + cert         │ 351: E1 / budget      │ YES before restore    │
│ hI; hK; hBefore       │ Actual prefix         │ Tick time and index   │ YES, bounded events   │
│ late HEAD services    │ Produced P-Ou         │ ReceiverInputs:757    │ YES, enabled gate     │
│ late target bodies    │ Not requested         │ GoodVotes:559         │ May be below F        │
│ result good history   │ Partial P-Ou          │ Marker causal         │ YES after its cut     │
│                       │                       │ induction             │                       │
│ post-E counts         │ Producer P-Ou         │ ReceiverInputs:1064   │ YES from handover     │
│ scoped read t         │ Proved P-Ou           │ ScopedInduction:386   │ YES before restore    │
│ raw test joined       │ Actual guard          │ gateStep_fresh:271    │ YES, joined only      │
│ restart test wake     │ Model argument        │ Kept durable rows     │ YES at exact wake     │
│ early ie/hie          │ Actual tick           │ ReceiverInputs:943    │ YES, finite read      │
│ early hFloor          │ Produced at caller    │ Retained cone frame   │ YES, selected K       │
│                       │                       │ bound                 │                       │
│ retained hFloor       │ Produced at caller    │ ExactProposalRetained │ YES before service    │
│                       │                       │ :820                  │                       │
│ prior vote GST        │ Produced Clean        │ ExactProposalReceipts │ YES, GST=0            │
│                       │                       │ :18                   │                       │
│ proposal GST          │ Produced from prior   │ InclusionServices     │ YES, later anchor     │
│                       │                       │ current duty          │                       │
│ score geometry D      │ Selected floor        │ Source and receiver F │ YES, selected D       │
│                       │                       │ <= D                  │                       │
│ sourceEpoch           │ Produced locally      │ Current proposal join │ YES, exact epoch      │
│ frozenHeads           │ Producer P-Ou         │ RelayKernel           │ YES, exact anchor     │
│                       │                       │ acceptance origin     │                       │
│ forward/backward      │ Producer P-Ou         │ InclusionServices:    │ YES, per floor        │
│                       │                       │ accepted body         │                       │
│ late local HEAD       │ No service request    │ Joined-tick pool      │ YES, no GST needed    │
│                       │                       │ provenance            │                       │
│ old relay callback    │ Removed               │ Late local receipt    │ FALSE in some runs    │
│                       │                       │ counterexample        │                       │
│ old early callback    │ Narrowed              │ Target below receiver │ FALSE in some runs    │
│                       │                       │ F                     │                       │
│ gate hTargets         │ Produced locally      │ Exact emitted         │ YES, actual gate      │
│                       │                       │ proposal HEAD         │                       │
│ gate hScope           │ Produced P-Ou         │ ReceiverInputs:1014   │ YES, GST + targets    │
│ caught-up gate        │ Produced P-Ou         │ InclusionGateBody:16  │ YES, actual tick      │
│ hOrdered/hBounds      │ Producer P-Cl2        │ Clean history         │ YES, finite cut       │
│                       │                       │ projections           │                       │
│ hOutputs/hOrigins     │ Producer P-Cl2        │ Truncation + gate     │ YES, bounded reads    │
│                       │                       │ output                │                       │
│ growth field inputs   │ Closed owner fields   │ GrowthSuppliers:15    │ YES, exact test       │
│ growth regime call    │ Actual composition    │ Tests/OutageGrowthSup │ YES, kernel check     │
│                       │                       │ pliers                │                       │
│ growth assembly       │ Handoff P-As          │ Use actual tested     │ Not yet integrated    │
│                       │                       │ producers             │                       │
│ hHeads global         │ Open P-Ou             │ First marker + prefix │ Not yet produced      │
│ restored count        │ Producer from E       │ r <= s <= r+k+1       │ YES, E window         │
│ healthy count         │ Producer regime       │ s >= r+k+1; horizon   │ YES after E           │
│ result hGST           │ Produced regime       │ FirstRestored + gst   │ YES, vote anchor      │
│                       │                       │ <= b1                 │                       │
│ r canonical           │ Proved P-Ou           │ ReceiverInputs:1078   │ YES, least label      │
│ marker k,hk; y,hy;    │ Selected actual       │ Stored carrier at     │ YES, branch witness   │
│ P,hP                  │ source                │ HEAD                  │                       │
│ marker B<=J; h_j!=0   │ Partial P-Ou          │ Named contested frame │ First-marker OPEN     │
│ reader i,hi; x,hx     │ Actual HEAD read      │ Actual event + honest │ YES, bounded tick     │
│ reader hJ             │ Actual local guard    │ outageHeadReader      │ YES at this read      │
│ marker m<=s           │ Phase guard           │ Earlier marker label  │ YES in later branch   │
│ marker hGST           │ Produced regime       │ gst + restored vote   │ YES if r<=m           │
│                       │                       │ cut                   │                       │
│ marker hmono          │ Producer P-Fd         │ RMonoAll / Foundation │ YES across wakes      │
│ marker acceptance     │ Producer from store   │ block_accepted_origin │ YES, durable origin   │
│ send<=marker vote     │ Proved locally        │ Schedule event order  │ YES, exact origin     │
│ marker anchor a       │ Proved locally        │ Later slot start      │ YES after GST         │
│ marker public/horizon │ Proved locally        │ Base delta + actual   │ YES, finite read      │
│                       │                       │ tick                  │                       │
│ marker floor F<=P     │ Proved by split       │ F<=B<=P at reader     │ YES in low branch     │
│ marker epoch/history  │ Producer local        │ Joined read + named   │ YES, exact anchor     │
│                       │ service               │ body                  │                       │
│ marker retained TF    │ Producer durable      │ store_durable         │ YES across restart    │
│                       │ store                 │                       │                       │
│ marker hNames         │ Joint source          │ named_of_source_histo │ YES on prefix         │
│                       │ projection            │ ry                    │                       │
│ marker live rows      │ Producer P-Ou         │ After-handover expiry │ YES on prior results  │
│ protected hp,hNames   │ Scoped event          │ G post-tick           │ YES before expiry     │
│                       │ invariant             │ protection            │                       │
│ protected hs; ht      │ Actual local guard    │ s!=0 and vote<expiry  │ YES in branch         │
│ conditional hlow      │ Local case split      │ Receiver F<=B         │ YES in low branch     │
│ joint I,hStart,hI,hi  │ Actual finite prefix  │ All-ticks cut +       │ YES, exact cut        │
│                       │                       │ length                │                       │
│ joint hSeed,hCover    │ Open P-Ou prefix      │ Sources and G stable  │ No all-honest seed    │
│ joint hPrefix         │ Open P-Ou prefix      │ Enabled results       │ No future callback    │
│                       │                       │ before I              │                       │
│ joint hResults        │ Produced suffix       │ Causal marker         │ YES after finite seed │
│                       │                       │ induction             │                       │
│ suffix hm             │ Phase guard           │ m>=r+k                │ YES in healthy branch │
│ suffix named sources  │ Produced jointly      │ Earlier HEAD -> gate  │ YES, causal indices   │
│ suffix row deadlines  │ Produced jointly      │ Exact old write       │ YES, <=handover       │
│                       │                       │ origin                │                       │
│ read hS,hF            │ Current invariant     │ Inclusive event       │ YES, G stable / all F │
│                       │                       │ prefix                │                       │
└───────────────────────┴───────────────────────┴───────────────────────┴───────────────────────┘
```
