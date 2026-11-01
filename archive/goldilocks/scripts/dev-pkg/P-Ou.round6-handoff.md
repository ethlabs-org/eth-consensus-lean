# P-Ou Round 6 handoff

Base: 4b561a23. Branch: sleep-pou6. Proof source: 84255dd4.
Commits: 3a05ccac, e050d23e, 7783e1e2, 84255dd4.
P-Ou remains PREPARED, not CLOSED. Public claims and protocol declarations are unchanged.
This file supersedes the pending hRows and fast hLast requests in the Round 5 handoff.
The continuation prefix request remains open.

## Proved pending seed

ReceiverInputs:506, outage_arming_sources_scoped, takes HealthyPrefixSleep2, TSrc,
and ArmingSleepGateCert. It proves:

```lean
OutageSourceHistory p c E rho B
  (afterTicksIdx rho (SA.gateTime p.toParams (l + 1)))
```

The strict-before branch uses source_below. At the pending time, TSrc gives fast support.
The pre-cut joined majority and CStar put the faulty count below the release threshold.
An honest supporting HEAD has an actual joined emission. The certificate's joined_heads
puts that HEAD above D. Since B is below D, the source is compatible with B.
The source can be in W. The proof does not use the old all-honest pending_input.

ReceiverInputs:541, outage_arming_named_scoped, converts this history through
outage_named_of_source_history. Its hnamed input has the actual P-Fd producer
Foundations/Sources:180, sourceDiscipline_emittedName. OutageServices:131 checks the
producer with the explicit SimplexFG-to-heightView conversion.

ReceiverInputs:558, outage_arming_protection_scoped, supplies P-Ar's complete hRows
boundary to pending_gate_lease_or_F_scoped_on. It returns OutageProtection and the
fullTree-or-Z domain alternative only for coveredNodes.

ReceiverInputs:593, outage_fast_seed_scoped, consumes fast_arming_scoped_on.
No hLast input is needed. OutageServices:108 supplies the actual Clean state, history,
joined transfer, and retained provenance producers. The equal-cut request is satisfied.
The old last-label helpers remain as special cases.

## Selected restored services and result split

GoodVotes:169 defines OutageGateReceiptScope for selected seats H. Its services field
requests only their actual honest emitted HEADs. The old full GateReceiptScope is
restricted only when a full pending batch has already been produced. The restriction
lemma is a conversion, not a producer.

ReceiverInputs:618, outage_restored_good_scope, constructs the selected scope from
Base2, actual restored transport, FGFoundation, an enabled gate, and these exact inputs:

```lean
hGST : E.t_GST ≤ SA.voteTime p.toParams s
hlow : Block.Preceq (F_at p c E rho i x) B
hTargets : ∀ q ∈ H, ∀ K, HeadTargetAtEmission p c E rho
  (rho.seatOf (.base (.head s)) q) (ofHead p ⟨.seat (.head s) q, K.root⟩)
    (SA.voteTime p.toParams s) K → Block.Preceq B K
```

The enabled guard supplies the actual receiver join and read epoch. Durable F monotonicity
puts the early receiver floor below B. The target input makes each selected HEAD
admissible there. The receiver can be in W. No all-honest target service is requested.

GoodVotes:512, outage_finalized_gate_result, proves B below C when B is below receiver F.
It needs only the actual enabled gate and nonempty executed result. GoodVotes:526 keeps
this B-below-F branch separate from the F-below-B count branch.

ReceiverInputs:662, outage_restored_result_of_good_targets, supplies all receipt services
in the count branch. It consumes the actual E count, the good-seat mapping, and the
opponent bound. It still needs current F compatibility and this conditional target input:

```lean
hTargets : Block.Preceq (F_at p c E rho i x) B →
  ∀ q K, rho.seatOf (.base (.head s)) q ∈
    outageH p E rho s \ outageW p E rho fast b₀ r →
  HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
    (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
  Block.Preceq B K
```

Owner: P-Ou. The full joint induction must produce this input at later labels.
The theorem is not an unconditional hTargets producer and is not global hResults.
E supplies the count only on its stated label window. Later labels need the restored
healthy count and the continued good-HEAD invariant.

## A union W source transition

ReceiverInputs:380 selects a supporting HEAD outside any bad set that includes faults
and has count below the release level. ReceiverInputs:708 derives the fixed A union W
release bound from E1, including before recovery starts.

ReceiverInputs:720, outage_source_of_good_heads, gives compatibility of every actual
honest source, including W. It uses the fixed A union W bound and this joint input:

```lean
hHeads : ∀ q K, rho.seatOf (.base (.head s)) q ∈
  outageH p E rho s \ outageW p E rho fast b₀ r →
  HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
    (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
  Block.Compatible K B
```

Owner: P-Ou. This is a source transition with a joint invariant input. It does not prove
the good-HEAD invariant. No row seed or all-honest duty premise is used.

## Exact open work

- P-Ou: later conditional hTargets and current receiver F compatibility at all actual gates.
- P-Ou: global hResults after r. The bounded PersistenceDeadlines input is still:

```lean
∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
  gateResultAt p c E rho j = some (some C) → Block.Compatible C B
```

- P-Ou: InclusionReceiverInputs, ExactProposalReceipts:229. The early field keeps the
  horizon and actual reader guards. The relay field keeps the actual ih tick. The retained
  field needs its proposal service and ScoreServiceScope for each selected floor geometry.
  A record conversion or callback is not a producer of these services.
- P-Ou: Induction:120 and ContinuationInduction:37. Replace the old all-honest seeds and
  NoRestart lanes by covered protection, selected good duties, global source/named history,
  and the fixed A union W release invariant. Do not infer NoRestart from a sleep regime.
- P-Ou: ContinuationJoint:671/871, Close:84, Suppliers, both Exports, OutageInduction.
  The actual consumer check still fails in Induction and ContinuationReceipt.
- P-Ar: continuation prefix adapter at RestoredBatch:377:

```lean
∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
  (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool) (T b₀ b₁ ΔF : Time),
  OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
  OutagePrefixReceipt p c E rho fast T b₀
```

The other P-As assembly boundaries in the Round 5 handoff remain open under their
existing exact types. No other package source was edited.

## SCOPE-NARROW input audit

The table groups repeated binder names by role. YES means true at the stated actual
read, event, or guarded branch. It does not mean an arbitrary time or object has service.
An open row is an unproved producer obligation. It is not a closure result.
The table covers the Round 5 transport/deadline inputs and all Round 6 input additions.

```text
┌──────────────────────┬──────────────────┬───────────────────────┬──────────────────────┐
│ Input                │ Status / owner   │ Producer or guard     │ True in sleep runs   │
├──────────────────────┼──────────────────┼───────────────────────┼──────────────────────┤
│ p,c,E,rho; labels    │ Given            │ Actual model objects  │ Structural           │
│ Base2; hs; hdelta    │ Producer P-Fd    │ Regime Base2 fields   │ YES                  │
│ roots; receipt roots │ Producer Base2   │ Base2.idealization    │ YES, scoped          │
│ h; hSync; hGST       │ Given regimes    │ Healthy /             │ YES on premise       │
│                      │                  │ continuation          │                      │
│ hDelivery; cut       │ Producer         │ withinOn of regime    │ YES in cut           │
│ hStart; hPub         │ Proved at caller │ Exact public anchor   │ YES, exact anchor    │
│ hDeadline; hCR       │ Proved at caller │ Phase arithmetic      │ YES, exact read      │
│ hhor; hCut; hgate    │ Proved at caller │ Cut / actual tick     │ YES, finite horizon  │
│ hx; hy; hJ           │ Producer         │ Actual reader /       │ YES, named nodes     │
│                      │                  │ source                │                      │
│ hG; readEpoch        │ Producer         │ PersistenceSleep:192  │ YES, enabled only    │
│ ht; hTarget; hfast   │ Producer TSrc    │ Actual action / HEAD  │ YES, guarded         │
│ hC; hresult          │ Actual event     │ Executed result       │ YES when nonempty    │
│ hNX; ready; history  │ Producer         │ Exact object service  │ YES, admissible      │
│ hf; hsrc; htsrc      │ Producer P-Fd    │ Foundation / sources  │ YES on premise       │
│ hq                   │ Given supplier   │ FaultQ supplier input │ Conditional          │
│ hState; hHist        │ Producer P-Cl1   │ Clean/Closure:128     │ YES with hq          │
│ htransfer            │ Producer P-Cl1   │ Clean/Closure:220     │ YES, joined reader   │
│ hprov                │ Producer P-Cl1   │ Clean/Service:719     │ YES, actual HEAD     │
│ hc (general)         │ Producer P-Ar    │ ArmingConstruction:39 │ YES, equal cut       │
│                      │                  │ 8                     │                      │
│ hread; hne           │ Selected witness │ Protected output      │ YES, chosen B        │
│ hbeta; named scope   │ Selected witness │ Actual FG / root lift │ YES, named body      │
│ hnamed               │ Producer P-Fd    │ Sources:180 + views   │ YES, emitted rows    │
│ hSource; hRows       │ Proved P-Ou      │ ReceiverInputs:506/54 │ YES, includes W      │
│                      │                  │ 1                     │                      │
│ bad; hfault; hbad    │ Proved P-Ou      │ Faults or A union W   │ YES, explicit bound  │
│ E1; hBound           │ Proved P-Ou      │ ReceiverInputs:708    │ YES, before recovery │
│ H; hCount; hpart     │ Producer from E  │ GoodVotes:20/89       │ YES in E window      │
│ hSelected; hrest     │ Proved P-Ou      │ Joined seats / origin │ YES, all receivers   │
│ hlow / hBF           │ Local case split │ F <= B / B <= F       │ YES, branch only     │
│ hFB at late gates    │ Open P-Ou        │ Joint named/frame IH  │ Not yet certified    │
│ hTargets after r     │ Open P-Ou        │ Joint good-HEAD IH    │ Not yet certified    │
│ hHeads good set      │ Open P-Ou        │ Joint good-HEAD IH    │ Not yet certified    │
│ selected services    │ Producer P-Ou    │ ReceiverInputs:618    │ YES with low targets │
│ shared scope adapter │ Conversion only  │ GoodVotes:182         │ Not a producer       │
│ hResults after r     │ Open P-Ou        │ Full joint induction  │ Not yet certified    │
│ deadline hResults    │ Open P-Ou        │ j < i at this writer  │ Not yet certified    │
│ Inclusion early      │ Open P-Ou        │ 229: actual read/cut  │ Not yet certified    │
│ Inclusion relay      │ Open P-Ou        │ Actual tick + anchor  │ Not yet certified    │
│ Inclusion retained   │ Open P-Ou        │ Score floors /        │ Not yet certified    │
│                      │                  │ service               │                      │
│ NoRestart lane       │ Legacy only      │ Run.Tests.Sleep       │ FALSE in sleep       │
│                      │                  │ joinRun               │                      │
│ all-honest seeds     │ Legacy only      │ Replace by G / goods  │ Not sleep producers  │
│ continuation prefix  │ Open P-Ar        │ RestoredBatch:377     │ Not yet produced     │
└──────────────────────┴──────────────────┴───────────────────────┴──────────────────────┘
```

The selected service record has a named conditional producer. Its target geometry is
still a P-Ou obligation. The all-honest pending source history is proved, not assumed.
The full InclusionReceiverInputs and both joint inductions are not produced in this round.
No new public premise or public meaning change is proposed. No public STOP is claimed.

## Registration and checks

45 TARGETS, 504 GREEN, 11 EXPECTED-FAIL: nine P-Ou and two S-Ap.
No target moved from EXPECTED-FAIL to GREEN. GREEN records compilation, not closure.
The complete local inventory has 201 commands. Its serial production audit imports use
production modules under the existing canonical key. No new key or allowance is added.
ReceiverInputs and RestoredBatch use public CatchUp imports and public service constructors.

Final validation on proof source 84255dd4:
DCK P-Ou PASS: 504 GREEN modules, 41 strict sources, 3,165 axiom results, and 24 controls.
Complete GREEN exports: 321 proof modules, 253 exports, zero unaccepted and zero Gen exports.
Complete local coverage and its control PASS for 201 commands.
Layers: 72 inherited findings, zero new. Module headers: four inherited failures,
including one in GoodVotes; two inherited failures in owned files were removed.
The three other failures are P-Ar-owned ArmingKernel and ArmingLocal imports.
All strict local roots compile with only propext, Classical.choice, and Quot.sound.
Evidence: .lake/sleep-pou-r6/. Checkers, baselines, allowances, and toolchain are unchanged.
