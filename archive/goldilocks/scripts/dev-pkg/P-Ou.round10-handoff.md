# P-Ou Round 10 handoff

Base: aef1dd45. Branch: sleep-pou10. Proof group: dada200f.
P-Ou is PREPARED, not CLOSED. The complete Round 10 task is incomplete.
Public claims and protocol declarations are unchanged.

## Proved prefix and read facts

ScopedInduction:28, outage_good_head_through_restored, permits the actual good HEAD
at r. :102, outage_event_induction_before_vote_cut, takes an exact vote-label bound
for its finite endpoint. The original two theorem signatures remain as wrappers.
No existing caller needs a new premise.

ScopedPrefix:15 defines regression only at an actual emitted HEAD with the scoped
joined reader guard. :40 selects the first label. :55 selects the first event,
including earlier reads at the same label. These are branch selections, not proofs
that a regression exists in every run.

ScopedPrefix:93 constructs the auxiliary zero-length arming regime. Its W set is
contained in the actual continuation W set, so the actual E1 bound suffices.
:151 produces the source history, named history, G-only stable seed and label-r
good-target coverage at I0 = afterTicksIdx rho (earlyTime r). It uses the actual
arming certificate, P-Cl1 Clean state/provenance and P-Fd foundation. The endpoint
is freezeTime r; only labels <= r can supply its good HEADs. The length-V bound
keeps this endpoint before the original covering deadline. The horizon guard
is earlyTime r <= horizon, supplied whenever a later actual gate needs the seed.

ScopedPrefix:235 proves the no-regression continuation from those producers.
It takes no source, stable, result or service seed. E supplies the first restored
batch. Later gates use earlier actual scoped HEADs. Sources and F compatibility
are global; stable inclusion is G-only. :298 produces the finite prefix at the
first actual regression from the first-event branch. This does not produce the
prefix after that regression through the marker suffix's initial cut.

ScopedPrefix:338 proves frozen-path membership at the actual joined reader.
The earlier receipt tick is strictly after that reader's join cutoff and no later
than its freeze. The actual join proves both stamp-epoch facts. P-Fd durable TF
and RStoreEpoch preserve the selected path and its strict original stamp.
This theorem does not promise receipt of every durable carrier at every receiver.
:394 constructs a stored nonzero marker from an actual contested named frame.
:415 proves contest from local retained scores and the uncontested filtered-path
witnesses. Those two local producers remain O10-2 below.

ScopedContinuation:157 proves a later actual joined HEAD from the marker, current
names and earlier results at that read. :194 now permits r <= m < r+k, with the
finite prefix ending after gate max(m,r+k). The induction uses :157 directly.
This removes the late-marker restriction; it does not construct the early bridge.

ScopedCatchUp:16 extracts the actual public W-reader gate and its awake suffix.
The regime produces that gate's batch at earlyTime s. The actual joined gate
produces the epoch from actionCut(voteTime s) to idxBefore(earlyTime s).
The gate label is >= r+k. Its HEAD can still be inside E at the boundary.
:54 proves all inclusive output inclusions in the local B <= F branch.
The other W output branch remains O10-4.

## Exact remaining P-Ou obligations

Common telescope: the actual OutageContinuationSleepPrem, FGFoundation, TSrc,
SrcFrameAboveStmt, emitted-name supplier, P-Cl1 CleanState at indices <= timeIdx b0,
ArmingJoinedProvenance, and ArmingSleepGateCert for the protected non-genesis B.
These are the complete arguments of outage_first_regression_prefix at
ScopedPrefix:298. Use the selected first actual regression and its first-event
absence guard from :55. The prefix's source/names/F/G conclusions are produced.
No NoRestart or all-honest stable seed is available from this telescope.

- O10-1: connect the no-regression and first-event branches to the public
  arming/read assembly, including reads before I0. The core no-regression
  continuation and its initial seed are proved. The actual certificate is a
  P-Ar producer, not an extra public premise.
- O10-2: at that first actual joined regression, produce hRoot, hScores and hPath
  with exactly the types in ScopedPrefix:415. hPath is requested only under
  contest=false. Use the preceding selected joined good voters, the actual E
  count (or the healthy count beyond E), their exact local retained services,
  receiver F floors and stamp epochs. :338 supplies frozen membership once the
  selected path has its actual receipt. Then :415 gives contest, and :394 gives
  P in TF, B <= J(P), and h_j(P) != 0. A conversion or assumed scope is not the
  missing producer. The local root argument outside G before handover also
  needs its actual compatible live rows; do not use an all-honest S invariant.
- O10-3: from that marker, produce the complete finite prefix through
  I = afterTicksIdx rho (gateTime (max m (r+k))). The exact seed telescope is
  ScopedContinuation:194. Required outputs are:

```lean
OutageSourceHistory p c E rho (eraseFG B) I
∀ x ∈ coveredNodes p E rho fast b₀,
  Block.Preceq (eraseFG B) (S_at p c E rho I x)
∀ j x s C, j < I → x ∈ rho.honest → restoredLabel p b₁ < s →
  enabledGateAt p c E rho j x s → gateResultAt p c E rho j = some (some C) →
  Block.Compatible C (eraseFG B)
```

  The first-read prefix at ScopedPrefix:298 stops before the marker. It is not
  this later prefix. The suffix theorem produces all results after this cut;
  it requests no future HEAD or result callback.
- O10-4: at the actual W gate returned by ScopedCatchUp:16, prove compatibility
  of the post-gate S with B in the branch where B is not below the reader F.
  Carry the actual batch, epoch and awake interval into the bounded continuation
  to the public read. Compatible raw results alone do not establish a new
  stable seed at an arbitrary W receiver. No all-honest inclusion is requested.
- O10-5: obtain global hHeads by joining the no-marker branch, first-read prefix,
  early bridge and causal marker suffix. Quantify only over actual scoped joined
  readers and actual emitted targets. Later marker targets need compatibility;
  keep covering-target demands inside actual protected or independently proved
  covering branches. Then port ContinuationJoint:671/:871, Close:84, the legacy
  continuation targets and both complete public exporters.

All five obligations stay P-Ou. No new P-Ar, P-Cl1, P-H1 or P-As request is made.
The original six P-Ou EXPECTED-FAIL entries remain; none is reclassified by a
partial source theorem. Public consumer builds still reach removed noRestart
projections and obsolete all-honest induction calls. No public STOP is claimed.

## Scope regressions and validation

Tests/OutageLaterHeads retains the wake=9, GST=20 and fixed E-window guards.
New tests distinguish a post-End gate from a post-End HEAD count, show that the
early-marker finite cut follows a HEAD used by the next gate, and exclude an
asleep deterministic read from actual regression selection. These are checked
scope regressions, not complete ExecutionValid counterexample runs.

56 TARGETS; 517 GREEN; eight EXPECTED-FAIL (six P-Ou and two S-Ap).
DCK P-Ou PASS: 44 strict sources, 3,265 results, all 24 default controls PASS.
Headers PASS: zero failures. Layers: 72 inherited findings, zero new.
Complete GREEN exports: 336 proof modules, 253 exports, zero unaccepted, zero Gen exports.
Local coverage: 301 commands, home-equation control PASS, zero unaccepted.
Serial production-only audit: 267 strict results, only the three standard axioms.
All changed/new proof modules and the eight guard regressions compile at default heartbeats.
The public consumer build was attempted and still fails at inherited legacy ports.
Proof group: dada200f. Final validation record: the subsequent documentation commit.
Evidence: .lake/sleep-pou-r10/. No checker, baseline, allowance, toolchain,
heartbeat, public claim or protocol source is changed.

## SCOPE-NARROW input audit

The table retains all Round 9 roles and adds the Round 10 roles. YES is conditional
on the stated actual read, branch, floor, epoch or finite prefix. It does not mean
that an OPEN producer has been proved. The protected B and arming certificate are
part of the common telescope. Legacy all-honest inputs in EXPECTED-FAIL code are
port failures, not supplier requests from the active sleep interface.

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
│ hHeads good set       │ Partial P-Ou          │ No-regression prefix; │ YES in exact branch   │
│                       │                       │ marker read           │                       │
│ selected services     │ Producer P-Ou         │ ReceiverInputs:618    │ YES with low targets  │
│ shared scope adapter  │ Conversion only       │ GoodVotes:182         │ Not a producer        │
│ hResults after r      │ Partial P-Ou          │ No-regression +       │ YES after produced    │
│                       │                       │ marker suffix         │ seed                  │
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
│ hHeads global         │ Open P-Ou             │ First-marker bridge   │ Actual scoped reads   │
│                       │                       │ O10-2/3               │ only                  │
│ restored count        │ Producer from E       │ r <= s <= r+k+1       │ YES, E window         │
│ healthy count         │ Producer regime       │ s >= r+k+1; horizon   │ YES after E           │
│ result hGST           │ Produced regime       │ FirstRestored + gst   │ YES, vote anchor      │
│                       │                       │ <= b1                 │                       │
│ r canonical           │ Proved P-Ou           │ ReceiverInputs:1078   │ YES, least label      │
│ marker k,hk; y,hy;    │ Selected actual       │ Stored carrier at     │ YES, branch witness   │
│ P,hP                  │ source                │ HEAD                  │                       │
│ marker B<=J; h_j!=0   │ Produced after        │ ScopedPrefix          │ YES, actual contested │
│                       │ contest               │ marker-of-names       │ read                  │
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
│ joint I,hStart,hI,hi  │ Actual finite prefix  │ gate max(m,r+k);      │ YES, exact cut        │
│                       │                       │ event length          │                       │
│ joint hSeed,hCover    │ Partial P-Ou          │ Vote seed; marker     │ YES, G stable only    │
│                       │                       │ bridge OPEN           │                       │
│ joint hPrefix         │ Partial P-Ou          │ First-read prefix;    │ Finite enabled gates  │
│                       │                       │ bridge OPEN           │ only                  │
│ joint hResults        │ Produced suffix       │ Causal marker         │ YES after finite seed │
│                       │                       │ induction             │                       │
│ suffix hm             │ Proved phase guard    │ r<=m; cut=max(m,r+k)  │ YES, early markers    │
│                       │                       │                       │ allowed               │
│ suffix named sources  │ Produced jointly      │ Earlier HEAD -> gate  │ YES, causal indices   │
│ suffix row deadlines  │ Produced jointly      │ Exact old write       │ YES, <=handover       │
│                       │                       │ origin                │                       │
│ read hS,hF            │ Current invariant     │ Inclusive event       │ YES, G stable / all F │
│                       │                       │ prefix                │                       │
│ regression            │ Actual branch         │ ScopedPrefix          │ YES, emitted joined   │
│ hk,hReader,hK         │                       │ regression definition │ read                  │
│ first event hFirst    │ Proved selection      │ First regression      │ YES, finite run       │
│                       │                       │ event theorem         │ branch                │
│ first read history    │ Proved P-Ou           │ First regression      │ YES, from arming cert │
│                       │                       │ prefix theorem        │                       │
│ hVotes; freeze cut    │ Proved P-Ou           │ Vote-cut arithmetic   │ YES, s<=r only        │
│                       │                       │ in vote seed          │                       │
│ initial hHor,hI       │ Actual prefix guards  │ Downstream tick;      │ YES, bounded read     │
│                       │                       │ inclusive cut         │                       │
│ initial               │ Proved P-Ou           │ Restored vote seed    │ YES, source + G only  │
│ hSource,hCover        │                       │                       │                       │
│ no-regression hNo     │ Proved branch guard   │ First-event dichotomy │ YES in no-marker      │
│                       │                       │                       │ branch                │
│ first hScores         │ Open P-Ou O10-2       │ Prior good batch at   │ YES with exact branch │
│                       │                       │ joined read           │                       │
│ first hPath,hRoot     │ Open P-Ou O10-2       │ Uncontested path;     │ YES with exact branch │
│                       │                       │ current rows          │                       │
│ frozen hj,hi,hAfter   │ Actual local guards   │ Receipt tick; joined  │ YES, after join       │
│                       │                       │ reader                │ cutoff                │
│ frozen hRF,hEpoch     │ Proved P-Ou           │ Joined read and event │ YES, exact interval   │
│                       │                       │ order                 │                       │
│ frozen hP,hFP         │ Actual selected path  │ Receipt; current      │ YES, selected         │
│                       │                       │ receiver F            │ admissible P          │
│ W hReader,hOutside    │ Actual public scope   │ Caught-up branch at   │ YES, actual W read    │
│                       │                       │ read                  │                       │
│ W gate,batch,awake    │ Proved P-Ou           │ ScopedCatchUp         │ YES, post-End gate    │
│                       │                       │ gate-scope            │                       │
│ W receipt epoch       │ Proved P-Ou           │ Joined gate; same     │ YES, actionCut to     │
│                       │                       │ anchor                │ early                 │
│ W finalized hBF       │ Local branch guard    │ Finalized             │ YES in finalized      │
│                       │                       │ continuation read     │ branch                │
│ W other output seed   │ Open P-Ou O10-4       │ Actual gate post-S    │ Public goal; proof    │
│                       │                       │ compatibility         │ OPEN                  │
└───────────────────────┴───────────────────────┴───────────────────────┴───────────────────────┘
```
