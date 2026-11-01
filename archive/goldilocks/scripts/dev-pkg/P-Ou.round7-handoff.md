# P-Ou Round 7 handoff

Base: a6ffe4a1. Branch: sleep-pou6. Proof groups: b7cf0f36, 714f8489, 337c0238, 181f601e.
P-Ou is PREPARED, not CLOSED. Public claims and protocol declarations are unchanged.
This handoff supersedes Round 6 for Induction and the release header repair.
No other package source changed except the authorized Shared/Release append.

## Completed release and result inputs

Shared/Release:187, fgsa_releaseCount_le_senders, is the authorized public count lemma.
GoodVotes uses a public import and supplies its actual A union W sender bound.
No P-Ou file uses import-all. The three header findings left are P-Ar-owned.

GoodVotes:559, outageV_gate_of_emitted_heads, bounds conflicting result support with
actual fresh HEADs in the late pool. It needs no target-body receipt or active-body
membership for a selected good seat. Named root identity identifies every resolved
support target with the actual emitted body.

ReceiverInputs:757, outage_restored_result_of_compatible_heads, produces these HEAD
receipts from Base2, synchrony, the actual enabled gate, and the vote-time GST cut.
The receiver can be in W. Its remaining invariant input is exactly:

```lean
∀ q K, rho.seatOf (.base (.head s)) q ∈
  outageH p E rho s \ outageW p E rho fast b₀ r →
HeadTargetAtEmission p c E rho (rho.seatOf (.base (.head s)) q)
  (ofHead p ⟨.seat (.head s) q, K.root⟩) (SA.voteTime p.toParams s) K →
Block.Compatible K B
```

The strict count remains the actual good-set count at s. E supplies it only on its
label window. This theorem is a conditional result producer, not global hResults.
The earlier F <= B / B <= F split and stronger conditional hTargets API remain.

## Completed scoped pre-restoration joint induction

ScopedInduction:18 defines OutageCoveredDutyHistory. Its post-pending emission clause
is only for coveredNodes. No awake or join fact is assumed for all honest receivers.

ScopedInduction:81, outage_event_induction_scoped, proves one complete event induction:
restart, delivery, and tick. It carries global OutageSourceHistory, scoped duty history,
global OutageNamedHistory, and covered OutageProtection. Release uses A union W.
The endpoint is the pre-restoration cut and can equal lease expiry. At a new source
or release tick, an actual good HEAD is either the in-flight seed or an earlier
covered duty. OutageSourceHistory includes actual sources from W.

ScopedInduction:351, outage_armed_induction_scoped, supplies every seed. P-Ar's
arming_inflight_heads_sleep supplies the in-flight emission bound. ReceiverInputs
supplies source history and covered protection from the actual gate certificate.
E1 and the outage budget supply the release bound and expiry bound.
The P-Fd source inputs use the exact cross-lane interface. Tests/OutageServices:155
supplies sourceDiscipline_tSrc and sourceDiscipline_emittedName and constructs the
Clean state and joined provenance from their actual producers.

ScopedInduction:386, outage_armed_read_scoped, reads the inclusive event prefix.
Every honest F is compatible. Covered receivers retain B in S and have the full
lease-or-F conclusion, including the fullTree-or-Z domain alternative.

Induction is the canonical import of this scoped implementation. The old all-honest
ArmingCert seed and NoRestart lane were removed. The true empty duty seed remains.
The downstream consumers must use the new scoped interface. GREEN records compilation;
it does not mean the public outage family is closed.

## Exact remaining work

- P-Ou: later conditional hTargets, with the existing receiver F case split.
- P-Ou: good-HEAD compatibility after r and after the E count window.
- P-Ou: global hResults for all enabled honest gates with r < s. The fresh-HEAD result
  producer now discharges receipt service, but needs the continued good-HEAD invariant
  and a count producer outside E's stated window.
- P-Ou: InclusionReceiverInputs, ExactProposalReceipts:229. Its early, relay, and retained
  fields still need their full actual producers. Horizon and actual reader-tick guards
  remain. ScoreServiceScope requests every selected floor geometry; a conversion of an
  assumed scope is not a producer.
- P-Ou: ContinuationInduction. Its old NoRestart and all-honest continuation lane remains
  unported. The new pre-restoration proof does not reach after restoration or handover.
- P-Ou: ContinuationJoint, Close, Suppliers, and both Exports.
  Their old calls to the removed all-honest induction interface must be replaced by
  the scoped producers and the remaining full continuation proof.
- P-Ar: continuation prefix adapter at RestoredBatch:377, as in the Round 6 handoff.
- P-As: existing assembly and Shared/Claims adapter requests, as in the Round 6 handoff.

No new public premise or public meaning change is proposed. No public STOP is claimed.
No callback for future good HEADs, global results, or the Inclusion record is declared
proved. These are exact open P-Ou producer obligations.

## SCOPE-NARROW input audit

YES means true at the stated event, read, prefix, or conditional branch. It does not
mean service for every object at arbitrary times. Repeated names are grouped by role.
The generic induction seeds are inputs to a consumer; the armed wrapper and the actual
Clean/P-Fd test are their named producers. Their receiver scope is G.
The table includes prior-round input roles and all Round 7 additions.

```text
┌──────────────────────┬────────────────────┬───────────────────────┬──────────────────────┐
│ Input                │ Status / owner     │ Producer or guard     │ True in sleep runs   │
├──────────────────────┼────────────────────┼───────────────────────┼──────────────────────┤
│ p,c,E,rho; labels    │ Given              │ Actual model objects  │ Structural           │
│ Base2; hs; hdelta    │ Producer P-Fd      │ Regime Base2 fields   │ YES                  │
│ roots; receipt roots │ Producer Base2     │ Base2.idealization    │ YES, scoped          │
│ h; hSync; hGST       │ Given regimes      │ Healthy /             │ YES on premise       │
│                      │                    │ continuation          │                      │
│ hDelivery; cut       │ Producer           │ withinOn of regime    │ YES in cut           │
│ hStart; hPub         │ Proved at caller   │ Exact public anchor   │ YES, exact anchor    │
│ hDeadline; hCR       │ Proved at caller   │ Phase arithmetic      │ YES, exact read      │
│ hhor; hCut; hgate    │ Proved at caller   │ Cut / actual tick     │ YES, finite horizon  │
│ hx; hy; hJ           │ Producer           │ Actual reader /       │ YES, named nodes     │
│                      │                    │ source                │                      │
│ hG; readEpoch        │ Producer           │ PersistenceSleep:192  │ YES, enabled only    │
│ ht; hTarget; hfast   │ Producer TSrc      │ Actual action / HEAD  │ YES, guarded         │
│ hC; hresult          │ Actual event       │ Executed result       │ YES when nonempty    │
│ hNX; ready; history  │ Producer           │ Exact object service  │ YES, admissible      │
│ hf; hsrc; htsrc      │ Producer P-Fd      │ Foundation / sources  │ YES on premise       │
│ hq                   │ Given supplier     │ FaultQ supplier input │ Conditional          │
│ hState; hHist        │ Producer P-Cl1     │ Clean/Closure:128     │ YES with hq          │
│ htransfer            │ Producer P-Cl1     │ Clean/Closure:220     │ YES, joined reader   │
│ hprov                │ Producer P-Cl1     │ Clean/Service:719     │ YES, actual HEAD     │
│ hc (general)         │ Producer P-Ar      │ ArmingConstruction:39 │ YES, equal cut       │
│                      │                    │ 8                     │                      │
│ hread; hne           │ Selected witness   │ Protected output      │ YES, chosen B        │
│ hbeta; named scope   │ Selected witness   │ Actual FG / root lift │ YES, named body      │
│ hnamed               │ Producer P-Fd      │ Sources:180 + views   │ YES, emitted rows    │
│ hSource; hRows       │ Proved P-Ou        │ ReceiverInputs:506/54 │ YES, includes W      │
│                      │                    │ 1                     │                      │
│ bad; hfault; hbad    │ Proved P-Ou        │ Faults or A union W   │ YES, explicit bound  │
│ E1; hBound           │ Proved P-Ou        │ ReceiverInputs:708    │ YES, before recovery │
│ H; hCount; hpart     │ Producer from E    │ GoodVotes:20/89       │ YES in E window      │
│ hSelected; hrest     │ Proved P-Ou        │ Joined seats / origin │ YES, all receivers   │
│ hlow / hBF           │ Local case split   │ F <= B / B <= F       │ YES, branch only     │
│ hFB at late gates    │ Proved on history  │ ScopedInduction:69    │ YES with sources     │
│ hTargets after r     │ Open P-Ou          │ Later good duty proof │ Not yet certified    │
│ hHeads good set      │ Proved before r    │ ScopedInduction:28    │ OPEN after r         │
│ selected services    │ Producer P-Ou      │ ReceiverInputs:618    │ YES with low targets │
│ shared scope adapter │ Conversion only    │ GoodVotes:182         │ Not a producer       │
│ hResults after r     │ Open P-Ou          │ Full joint induction  │ Not yet certified    │
│ deadline hResults    │ Open P-Ou          │ j < i at this writer  │ Not yet certified    │
│ Inclusion early      │ Open P-Ou          │ 229: actual read/cut  │ Not yet certified    │
│ Inclusion relay      │ Open P-Ou          │ Actual tick + anchor  │ Not yet certified    │
│ Inclusion retained   │ Open P-Ou          │ Score floors /        │ Not yet certified    │
│                      │                    │ service               │                      │
│ NoRestart lane       │ Removed Induction  │ Legacy continuation   │ Not a sleep input    │
│ all-honest seeds     │ Removed Induction  │ G seed + in-flight    │ YES, scoped seed     │
│ continuation prefix  │ Open P-Ar          │ RestoredBatch:377     │ Not yet produced     │
│ sender; hinj; bad    │ Explicit witnesses │ Release:187           │ YES, actual seats    │
│ hbad release rule    │ Proved P-Ou        │ GoodVotes:413         │ YES, A union W       │
│ hDuty covered        │ Proved P-Ou        │ ScopedInduction:81    │ YES before restore   │
│ hSeed in-flight      │ Producer P-Ar      │ ArmingDutySleep:299   │ YES, actual emission │
│ hLocal G seed        │ Produced P-Ou      │ ReceiverInputs:558    │ YES, G only          │
│ hr; hcut; hend       │ Regime + cert      │ 351: E1 / budget      │ YES before restore   │
│ hI; hK; hBefore      │ Actual prefix      │ Tick time and index   │ YES, bounded events  │
│ late HEAD services   │ Produced P-Ou      │ ReceiverInputs:757    │ YES, enabled gate    │
│ late target bodies   │ Not requested      │ GoodVotes:559         │ May be below F       │
│ result good history  │ Open P-Ou          │ 757: actual targets   │ Conditional after r  │
│ post-E counts        │ Open P-Ou          │ Healthy continuation  │ Not yet produced     │
│ scoped read t        │ Proved P-Ou        │ ScopedInduction:386   │ YES before restore   │
│ raw test joined      │ Actual guard       │ gateStep_fresh:271    │ YES, joined only     │
│ restart test wake    │ Model argument     │ Kept durable rows     │ YES at exact wake    │
└──────────────────────┴────────────────────┴───────────────────────┴──────────────────────┘
```

## Registration and validation

47 TARGETS, 507 GREEN, 9 EXPECTED-FAIL: seven P-Ou and two S-Ap.
Induction and Tests/OutageInduction moved to GREEN. ScopedInduction is a new GREEN target.
The complete local inventory has 225 commands, including the authorized Shared lemma.
Serial audit fragments import production modules and use the existing canonical key.
Checkers, baselines, allowances, toolchain, and protocol declarations are unchanged.


Tests/OutageInduction is now an independent compiled kernel audit. Its disclosure,
contested-frame, lease, and phase tests remain. The raw saved-result test requires
the actual joined gate. Restart tests check retained obligations and protection.
The old empty-lock restart assertion was false under the approved model and was
replaced. The public Close and exporter roots were checked separately and remain open.
The complete local inventory has 225 commands.

Final validation on proof source 181f601e:

- DCK P-Ou PASS: 507 GREEN modules, 42 strict audit sources, 3,189 results,
  and all 24 default controls. Only propext, Classical.choice, and Quot.sound occur.
- Complete GREEN exports PASS: 325 proof modules, 253 exports, zero unaccepted
  and zero Gen exports.
- Complete local coverage and its control PASS: 225 commands.
- Layers: 72 inherited findings, zero new. Headers: three inherited P-Ar failures,
  zero P-Ou failure. No allowance or baseline was added.
- The changed production roots and both independent outage kernel tests compile.
  The actual remaining continuation and exporter consumer roots were attempted.
  They still fail in ContinuationInduction, ContinuationReceipt, Close and Shared/Claims.
- New Lean lines are at most 100 characters. Whitespace and source ownership pass.
  No sorry, admit, project axiom, native_decide, heartbeat increase, checker change,
  toolchain change, protocol change, review, agent, push, rebase, merge, or ssh was added.
  No throttle override or lake update was used. Only own processes were interrupted.

Evidence: .lake/sleep-pou-r7/dck-final.log, exports-final.log, coverage-final.log,
layers-final.log, headers-final.log, export-repair-build.log, scoped-consumer-build.log,
induction-tests-build2.log and open-consumers.log. Complete scope table: scope-table.txt.
P-Ou remains PREPARED. Full continuation, global hResults, later conditional hTargets,
InclusionReceiverInputs, and final public closure remain open.
