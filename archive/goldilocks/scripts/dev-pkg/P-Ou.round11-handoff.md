# P-Ou Round 11 handoff

Base: 9b372883. Branch: sleep-pou11.
Proof commits: a2f2caaf and 8f322f2d. Visibility commit: 4f5a41d3.
P-Ou is PREPARED. The complete Round 11 task is not complete.
Public claims, protocol declarations and healing files are unchanged.

## Completed producers

- O10-2: ScopedPaths:379, outage_first_regression_marker. The actual first
  regression produces P in TF, beta <= J(P), and nonzero h_j(P). Root, retained
  scores and the uncontested frozen path are produced internally. There is no
  score, path, root, receipt or all-honest stable seed argument.
- O10-3: ScopedBridge:249, outage_first_marker_finite_prefix. The exact endpoint
  is I = afterTicksIdx(gateTime(max(m,r+k))). It returns source history at I,
  G stable inclusion at I, and every enabled result after r before I. Early
  markers are allowed. Same-label reads use their own local contested frame.
  ScopedBridge:59 constructs the whole finite continuation, not just the cut.
- O10-5 hHeads: ScopedBridge:170, outage_continuation_scoped_heads. Its complete
  type is in that declaration, with the common context below. It quantifies only
  over actual emitted targets at scoped joined readers after r. No marker is
  required in the no-regression branch. ReceiverInputs:1159 consumes this exact
  result. The legacy consumer ports are still open.
- O10-1 after the seed: ScopedBridge:292 joins both first-event branches into
  the bounded event state. :329 reaches both inclusive public G outputs at
  earlyTime(r) <= t <= horizon. Earlier public reads remain below.
- W gate: ScopedCatchUp:68, outage_caught_up_gate_result_history, produces its
  raw result compatibility with the actual batch, awake suffix and epoch.
  This is not post-gate stable compatibility. ScopedCatchUp:54 closes the other
  branch at B <= F(timeIdx(t)).
- P-As round 6 / rev-pou10 item 2: Outage/Export:6 publicly imports
  GrowthSuppliers. Assembly/Outage keeps its existing Export route. The complete
  Export build remains separate from this visibility fix.

The old no-regression, event-first prefix, score and marker theorem names remain
wrappers with their types preserved. New label forms use absence below m, not
absence at earlier same-label events. Event-first selection supplies that guard.
The global proof contains no future HEAD, result or service callback.

## Common caller context

The following is the complete common context. It has no hReg, hFirst or marker.
The caller selects a protected non-genesis B from its actual initial confirmed
read. P-Ar supplies hc through fast_arming_scoped_on or slow_arming_scoped_on
(ArmingConstruction:398/:461). P-Cl1 supplies hState and hprov from its actual
Clean cut. P-Fd supplies hf, htsrc, hsrc, hnamed and origin. In particular, origin
is sourceDiscipline_qcOrigin (Foundations/Sources:316) with the existing caller
FaultQ input; it is not a new public premise or a request to P-Fd.

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

```

The no-regression branch is selected by ScopedPrefix:55's left alternative.
Only the regression branch takes hReg and hFirst at the actual first event.
Their exact types remain ScopedPaths:379; they are not added to this common
context. The finite bridge and global HEAD types can be read at ScopedBridge:249
and :170. These are proved producers, not remaining hypotheses.

## Remaining exact P-Ou goals

All items below remain P-Ou. No new supplier request goes to another package.
The common context above is used for each type. O11-EARLY-READ includes short
finite runs where the early-r seed lies after the horizon. No future event or
seed-horizon bound is part of that goal. The inclusive index is timeIdx(t).
O11-EARLY-HEAD covers labels <= r; labels > r are proved by ScopedBridge:170.
O11-EARLY-F supplies the earlier global F branch. O11-DUTY is the exact scoped
outage duty conclusion required at Close; Join:277 defines its actual emitted
HEAD and proposal parent clauses. No all-honest duty conclusion is requested.

### O11-EARLY-READ — OPEN, P-Ou

```lean
∀ x t, b₀ ≤ t → t ≤ rho.horizon →
  t < SA.earlyTime p.toParams (restoredLabel p b₁) →
  outageConfirmedReader p c E rho fast b₀ b₁ x t →
  Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
  Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
  Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
  (x ∈ coveredNodes p E rho fast b₀ →
    Block.Preceq B (S_at p c E rho (timeIdx rho t) x) ∧
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
    Block.Preceq B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t))
```

### O11-EARLY-HEAD — OPEN, P-Ou

```lean
∀ s q K, s ≤ restoredLabel p b₁ → b₀ ≤ SA.voteTime p.toParams s →
  SA.voteTime p.toParams s ≤ rho.horizon →
  outageHeadReader p E rho fast b₀ b₁ (rho.seatOf (.base (.head s)) q)
    (SA.voteTime p.toParams s) →
  HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
    (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
  Block.Preceq B K
```

### O11-EARLY-F — OPEN, P-Ou

```lean
∀ x t, x ∈ rho.honest → b₀ ≤ t → t ≤ rho.horizon →
  t < SA.earlyTime p.toParams (restoredLabel p b₁) →
  Block.Compatible B (F_at p c E rho (timeIdx rho t) x)
```

### O11-DUTY — OPEN, P-Ou

```lean
DutiesExtendScoped p c E rho fast B b₀ b₁
```

### Actual W branch and finite endpoints

ScopedCatchUp:16 selects s and j from the actual public reader. Its guard is
r+k <= s, j < timeIdx(t), and an enabled tick at gateTime(s). The regime produces
BatchReceiptAt at earlyTime(s). The enabled guard produces the receipt epoch
from actionCut(voteTime(s)) to idxBefore(earlyTime(s)). The public reader supplies
AwakeClosed and RestartFreeTime from gateTime(s) to t. The actual public read
bound is t <= horizon. There is no prior-HEAD join or count inferred from the gate.

The finalized branch is tested at timeIdx(t), as in ScopedCatchUp:54. If it fails,
monotone F gives failure at j as well. The types below test that low branch at j.
Global named history gives the F <= B floor there. The required stable seed is
at j+1, after the actual gate. The continuation ends at timeIdx(t), including
same-time deliveries and horizon events. O11-W-READ's seed is precisely the output
of O11-W-SEED; it is not a new public input or a global stable invariant.

### O11-W-SEED — OPEN, P-Ou

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

### O11-W-READ — OPEN, P-Ou

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
  Block.Compatible B (S_at p c E rho (j + 1) x) →
  Block.Compatible B (S_at p c E rho (timeIdx rho t) x) ∧
  Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).stable x t) ∧
  Block.Compatible B (V2.D.outputAt E rho (fgsaInterface p c).confirmed x t) ∧
  Block.Compatible B (F_at p c E rho (timeIdx rho t) x)
```

## O11-OUTAGE — OPEN, P-Ou; Close's separate caller context

Close is called with OutagePrem, not with the stronger continuation regime.
Use the same actual model, hf, htsrc, hnamed, hsrc, hState, hprov, selected B,
hne, hc and hBeta above. Replace h by the following exact premise:

```lean
variable (hO : OutagePrem p c fast E rho ⟨T, b₀, b₁⟩ ΔF)
```

No global synchrony, E-window or post-E joined count is requested for this
outage-only port. P-Ar supplies hc from hO.set. P-Cl1 supplies the same actual
Clean cut. ScopedInduction supplies the pre-restoration G protection, source
history and duty history; OutageE1 supplies the A union W release bound.
The exact protected-B result required for the scoped Close assembly is:

```lean
(∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
  ∀ y t, b₀ ≤ t → t < b₁ →
    outageConfirmedReader p c E rho fast b₀ b₁ y t →
    Block.Preceq B (V2.D.outputAt E rho g y t)) ∧
DutiesExtendScoped p c E rho fast B b₀ b₁ ∧
FCompatBefore p c E rho B b₁ ∧
LeaseOrFFrom p c E rho (coveredNodes p E rho fast b₀) B
  (SA.gateTime p.toParams (coverLabel p b₀)) b₁
```

The public caller applies this separately to each initial protected B, selected
from its confirmedReader at T and actual output. Genesis uses its prefix-order
fact. This yields P1Concl and OutageCompatAt with the existing public quantifiers.
The exporter goal is exactly OutageCompatAt p c E rho fast pt, as defined in
Claims/Outage:144, under OutagePrem p c fast E rho pt DeltaF. The complete supplier
parameter list remains Outage/Export:334/:406. Those existing port bodies still
use obsolete all-honest conclusions and must be replaced by the scoped result.

The continuation exporter similarly selects hc for each protected B. Its final
goal is OutageContinuationConcl p c E rho fast T b0 b1, under the exact
OutageContinuationSleepPrem in the common context. Claims/OutageContinuation:9
and Statements/OutageContinuation:40 give the full unchanged public types.
Use hf.cumul's durable and epoch forms. RStoreCumul and NoRestart in the legacy
internal assembly are port failures; neither is an active sleep supplier request.

## Conditional targets and consumer changes

There is no remaining covering-target factory at later general gates. In the
active continuation, ScopedBridge:59 calls ReceiverInputs:1097 with compatibility
of actual emitted scoped HEADs, and :170 produces that compatibility globally.
ScopedCatchUp:68 uses the same route at the actual W gate. This replaces the old
legacy covering callbacks; it does not prove B <= every later target.

The covering branch retained by O11-EARLY-HEAD is exact: label s <= r, actual
scoped joined reader, voteTime(s) inside [b0,horizon], and actual emitted target K.
Before restoration its reader is in G; the pre-expiry protected producer is
LaterHeads:279 with OutageProtection at that actual read and
voteTime(s) < gateTime(coverLabel(b0)) + L(p). The initial in-flight branch uses
arming_inflight_heads_sleep. The event induction must produce those facts when
porting O11-EARLY-HEAD and O11-DUTY. Equality at expiry is handled by the finite
vote-cut induction and initial good batch, not by a strict-pre-expiry helper.
No extra covering target is requested outside these branches.

The finalized target branch is already proved by F <= liveRoot <= HEAD when
B <= F at that actual HEAD read. The retained-score branch tests F <= B at the
same read; the proof derives it from current F compatibility and actual regression.
Services for K or crossing U use only their selected ancestors above current F,
actual source tick <= previous early cut, post-GST prior vote, and current joined
read. The exact theorem is ScopedPaths:100. Neither arbitrary durable TF receipt
nor all-honest prior-label joinedness is requested.

## Failed consumer map

The six P-Ou modules remain EXPECTED-FAIL. These are port sites, not producer types.
Every needed open producer is stated above; completed producers are linked above.

```text
┌───────────────────────────┬───────────────────────────────────────────────────────────────────┐
│ Consumer                  │ Required work                                                     │
├───────────────────────────┼───────────────────────────────────────────────────────────────────┤
│ ContinuationReceipt       │ Port to ScopedPaths:100/185/379; obsolete global NoRestart        │
│                           │ receipt helpers. No new producer.                                 │
│ ContinuationInduction     │ Port to ScopedBridge:59/292 and ScopedInduction;                  │
│                           │ O11-EARLY-READ/F/DUTY at earlier cuts.                            │
│ ContinuationJoint         │ O11-EARLY-READ/HEAD/F and O11-W-SEED/READ; use ScopedBridge:170   │
│                           │ for global hHeads.                                                │
│ Close                     │ O11-OUTAGE under its own OutagePrem; use scoped arming and        │
│                           │ pre-restoration induction; remove noRestart/duties_and_outputs.   │
│ Outage.Export             │ Close and O11-OUTAGE in the OutagePrem context. GrowthSuppliers   │
│                           │ visibility is done.                                               │
│ OutageContinuation.Export │ ContinuationJoint ports plus O11-EARLY-* and O11-W-SEED/READ;     │
│                           │ existing supplier parameters.                                     │
└───────────────────────────┴───────────────────────────────────────────────────────────────────┘
```

## Validation and scope assessment

DCK P-Ou PASS: 44 strict sources; 3,297 axiom results; all 24 default controls PASS.
Map: 60 TARGETS; 521 GREEN; eight EXPECTED-FAIL (six P-Ou and two S-Ap).
Headers PASS with zero failures. Layers: 72 inherited findings, zero new.
Complete GREEN exports: 340 proof modules, 253 exports, zero unaccepted, zero Gen exports.
Local coverage: 333 commands; home-equation control PASS; zero unaccepted.
Serial production-only audit: 297 results; only propext, Classical.choice, Quot.sound.
Correction in Round 13: OpenTypes failed at O11-OUTAGE because Claims imports were absent.
The successful exact-contract rerun is .lake/sleep-pou-r13/Contracts.lean and contracts.log.
That rerun proves the solved contracts and checks the unproved W seed only as a Prop.

The actual public consumer build still fails in Close, ContinuationReceipt and
ContinuationInduction. The joined export modules cannot compile through those
failures. None is reclassified by a partial producer. GrowthSuppliers itself builds,
and the public source import route is present. No complete public claim is CLOSED.

The new theorem guards exclude the rev-ph1e failures: restart-at-9 suppresses
label 3's HEAD even though its gate can be enabled; GST=20 excludes service at
labels 2 and 3. A restart at GST=20 permits the label-6 joined read and its post-GST
label-5 batch. Two new kernel guard tests check those cases. They are not complete
ExecutionValid run fixtures. The produced theorems quantify over Base2.valid and
allow restarts at GST; no prior global join, NoRestart or all-honest S field is added.

The scope table below covers the active explicit inputs and exact open targets.
YES is conditional on its stated event, branch, floor, epoch or regime. An OPEN
public goal is identified as unproved; the table does not certify its producer.
The older kernel input table remains Round 10's table; its source/service rows are
unchanged. Round 11 supersedes its OPEN first-marker, bridge and global hHeads rows.
No falsely scoped service callback is left as a new public assumption.

## SCOPE-NARROW table

```text
┌───────────────────────┬───────────────────────┬───────────────────────┬───────────────────────┐
│ Input                 │ Status / owner        │ Producer / guard      │ Sleep assessment      │
├───────────────────────┼───────────────────────┼───────────────────────┼───────────────────────┤
│ Common run/labels     │ Given                 │ Actual model and      │ YES, structural       │
│                       │                       │ horizon               │                       │
│ h; sleep regimes      │ Given                 │ OutageContinuationSle │ YES on premise        │
│                       │                       │ epPrem                │                       │
│ hf                    │ Named P-Fd            │ FGFoundation supplier │ YES on premise        │
│ htsrc; hsrc; hnamed   │ Named P-Fd            │ Source discipline     │ YES on premise        │
│                       │                       │ suppliers             │                       │
│ origin; FaultQ        │ Named P-Fd            │ sourceDiscipline_qcOr │ YES, existing quorum  │
│                       │                       │ igin                  │ input                 │
│ hState; hprov         │ Named P-Cl1           │ Clean cut and joined  │ YES, exact cut/read   │
│                       │                       │ provenance            │                       │
│ hc; B; hne; hBeta     │ Named P-Ar / selected │ Scoped arming at      │ YES, selected B       │
│                       │                       │ public anchor         │                       │
│ hReg; hFirst          │ Proved branch         │ First actual event    │ YES only in           │
│                       │                       │ selection             │ regression arm        │
│ hNo lower labels      │ Proved                │ No-lower-of-first-eve │ YES, lower labels     │
│                       │                       │ nt                    │ only                  │
│ Prior H; hCount       │ Proved                │ E or post-E joined    │ YES, actual prior     │
│                       │                       │ count                 │ label                 │
│ Pool hOther           │ Proved                │ Stored seat           │ YES, A union W /      │
│                       │                       │ provenance            │ healthy               │
│ Prior hTargets        │ Proved                │ Arming seed / no      │ YES, selected prior   │
│                       │                       │ lower regression      │ good set              │
│ Prior hRec; hScores   │ Proved                │ Early services and    │ YES, current F floor  │
│                       │                       │ local epoch           │                       │
│ Prior source P        │ Proved                │ Nonempty joined good  │ YES, actual prior     │
│                       │                       │ batch                 │ emission              │
│ hRoot; live rows      │ Proved                │ G S / old gate origin │ YES, scoped actual    │
│                       │                       │ / expiry              │ reader                │
│ Crossing source U     │ Proved with named     │ Honest crossed-height │ YES, actual source <= │
│                       │ origin                │ row                   │ early                 │
│ Selected X; floor     │ Proved at caller      │ F <= X <= selected    │ YES, admissible       │
│                       │                       │ P/U                   │ ancestor              │
│ Source/join/GST cuts  │ Proved at caller      │ Actual tick and prior │ YES, exact current    │
│                       │                       │ label                 │ read                  │
│ Frozen stamp epoch    │ Proved                │ Joined read; no       │ YES, wake at GST      │
│                       │                       │ restart after cut     │ allowed               │
│ Uncontested hPath     │ Proved                │ Selected frozen path  │ YES, contest=false    │
│                       │                       │ and height            │ branch                │
│ Marker P; hBJ; hnz    │ Proved O10-2          │ First regression      │ YES, regression       │
│                       │                       │ marker                │ branch only           │
│ Finite                │ Proved O10-3          │ First marker finite   │ YES, cut after max    │
│ hSeed/Cover/Prefix    │                       │ prefix                │ gate                  │
│ Later hHeads          │ Proved O10-5 core     │ Global scoped HEAD    │ YES, actual emitted   │
│                       │                       │ producer              │ after r               │
│ hResults after r      │ Proved                │ Actual HEAD to        │ YES, bounded prefix   │
│                       │                       │ enabled gate          │                       │
│ Event                 │ Proved                │ Both event branches   │ YES after early-r     │
│ hSource/names/F/G S   │                       │                       │ seed                  │
│ Inclusive G outputs   │ Proved                │ Covered read after    │ YES, bounded public   │
│                       │                       │ seed                  │ read                  │
│ Earlier read/F/duty   │ Open P-Ou             │ O11-EARLY-*; O11-DUTY │ Guarded public goals; │
│ goals                 │                       │                       │ unproved              │
│ W gate/batch/awake/ep │ Proved                │ Actual caught-up gate │ YES, finite public    │
│ och                   │                       │ scope                 │ read                  │
│ W raw results         │ Proved                │ Global hHeads at      │ YES; not stable seed  │
│                       │                       │ actual gate           │                       │
│ W finalized branch    │ Proved                │ B <= F at timeIdx(t)  │ YES in branch         │
│ W low branch test     │ Local split           │ Not B <= F at j       │ YES in branch; F <= B │
│                       │                       │                       │ derived               │
│ W S at j+1            │ Open P-Ou             │ Exact O11-W-SEED type │ Guarded public goal;  │
│                       │                       │                       │ unproved              │
│ W S/output at         │ Open P-Ou             │ Exact O11-W-READ type │ YES conditional on    │
│ timeIdx(t)            │                       │                       │ produced seed         │
│ NoRestart/all-honest  │ No active sleep input │ Legacy EXPECTED-FAIL  │ Not requested         │
│ seeds                 │                       │ ports                 │                       │
│ Legacy later cover    │ Removed from active   │ Bridge uses           │ Not requested         │
│ callbacks             │ route                 │ compatibility         │                       │
└───────────────────────┴───────────────────────┴───────────────────────┴───────────────────────┘
```

Evidence: .lake/sleep-pou-r11/; public-consumers.log records the failed ports.
