# P-WC Round 3 handoff

Base: 7e4509db. Branch: sleep-pwc3.
Status: PREPARED. These suppliers compile with --wfail.
The complete event induction and the assembly consumers remain open.
Public Claims/Statements and public P23 are unchanged.

Import WC StepService or WCG StepService from the corresponding proof directory.
Each family has its own supplier modules. WCG has no WC proof import.

The internal participation input keeps every time from the first covered vote:
`SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon`.
Do not reduce this input to votes before the earlier gate actor is selected.
P-As must keep the source interval and continuation interval through this selection.
The source endpoint is inclusive; use the continuation count after that endpoint.

The store input is `RStoreDurable ∧ RStoreEpoch`. Use RMonoAll and RFrameNextEpoch.
The wake input is RestartsAtWakes. No sleep caller can supply global NoRestart.

The full service contracts follow. The implicit parameters are
`p : Params`, `c : AppCodec In`, `E : Generic.Env V`, and
`rho : V2.D.Run V (fgsa p c)`, with DecidableEq V and Fintype V.

```lean
abbrev WCService4Statement (ΔF : Time) (w : HealingWitness) (iStar : Nat) : Prop :=
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hwakes : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfault : (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_hfaultX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
      enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar →
    (∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i) →
    ∀ j x s B, x ∈ rho.honest → iStar ≤ j → IsGateTick p c rho j x s → w.u < s →
      gateResultAt p c E rho j = some (some B) →
      SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
        i ≤ rho.events.length → confirmedReaderIdx p c E rho y i →
          Block.Preceq B (S_at p c E rho i y)
```

Supplier: `wc_service4 : WCService4Statement p c E rho ΔF w iStar`.

```lean
abbrev WCGService4Statement (ΔF : Time) (w : HealingWitness) (iStar : Nat) : Prop :=
  ∀
  (_hvalid : V2.D.ExecutionValid E rho)
  (_hlinked : V2.D.Linked (fgsaFamilies p c).linked rho)
  (_hcstar : V2.D.CStar (fgsaFamilies p c).fresh rho)
  (_hwakes : V2.D.RestartsAtWakes E rho)
  (_hdelta : E.Δ = p.Δ)
  (_hroots : NamedReceiptRootCollisionFree p c E rho)
  (_hsync : Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF))
  (_hdeltaF : E.Δ ≤ ΔF)
  (_hfaultQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
  (_haccountable : FinalitySlashableBound p c E rho)
  (_hpart : ∀ t, SA.voteTime p.toParams (w.u + 1) ≤ t → t ≤ rho.horizon →
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card)
  (_hstore : RStore p c E rho)
  (_hcumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho)
  (_hmono : RMonoAll p c E rho)
  (_hactive : RActive p c E rho)
  (_hframe : RFrameExactNext p c E rho)
  (_hmeta : RFrameNextEpoch p c E rho)
  (_hrec : RRec p c E rho)
  (_hgeo : RGeo p c E rho)
  (_hcert : RCert p c E rho)
  (_hsrc : TSrc p c E rho)
  (_hlabel : LabelBound p c E rho)
  (_hqc : RQCOrigin p c E rho)
  (_hstrat : RStrat p c E rho)
  (_hnoslash : ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x)
  (_hemitted : ∀ j x r a e, HonestRowAt p c E rho j x r a →
    namedEntry a.payload.height_pair = some e →
    ∃ C B, actionSourceFG p c E rho x r = some (some C) ∧
      e = (hOf p.E p.cfg C, (derive p.E p.cfg C).T_h.root) ∧
      FGBlock.Preceq (derive p.E p.cfg C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some B) ∧
      Block.Preceq (eraseFG C) B ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
  (_htargets : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    Block.Preceq row.1 (storeAt p c E rho i x).base.stableRecord)
  (_hlease : ∀ i x row, row ∈ (storeAt p c E rho i x).base.obligations →
    ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
      (row.1, row.2.1) ∈
      (let wcView := actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s));
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b B)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView s b).map (fun g => (b, g)))) ∧
      row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
      row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
      ∀ k w C, j < k → k < i → enabledGateAt p c E rho k x w →
        let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
        GridCO.savedGenuine pre.base w = none →
        SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
        (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
        (row.1, row.2.1) ∉ (let wcView := actView pre;
        (wcView.blocks.filter (fun b => b != .genesis && Block.preceq b C)).flatMap
          (fun b => (@GridCO.admissionLevels GridCO.slowLeasePolicy
            p.toParams.engine p.n .root wcView w b).map (fun g => (b, g)))))
  (_hfast : ∀ i x,
    ∀ s X, X ∈ (FGSA.fastWriteAt (storeAt p c E rho i x) s).getD [] →
      ∃ j < i, V2.D.restartFree rho x j i ∧
        enabledGateAt p c E rho j x s ∧ gatePassedAt p c E rho j ∧
        ∃ B, gateResultAt p c E rho j = some (some B) ∧
          Block.Preceq X B ∧ fastAt p c E rho x s X)
  (_hdeadlines : ∀ i x,
    ∀ K g deadline, (K, g, deadline) ∈ (storeAt p c E rho i x).base.obligations →
      ∀ B, B ≠ .genesis → Block.Preceq B K →
        Gen.AC.Root.ProtectsUntil (storeAt p c E rho i x).base B g deadline)
  (_hheldRows : ∀ i x W, HeldAt p c E rho i x W → ∀ a ∈ chainRows W,
    ∃ (wire : RowWire p.n) (r : Nat), wire.toRow? = some a ∧
      wire.auth = .seat .fg a.signer ∧ ∃ k o t, k < i ∧
        rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner p c rho wire z → z ∈ rho.honest →
          HonestRowBefore p c E rho i z r wire ∧ p.actionTime r ≤ t)
  (_hscopeRows : ∀ D, RootBlockInRun p c E rho (eraseFG D) → ∀ a ∈ chainRows D,
    rho.seatOf (.base .fg) a.signer ∈ rho.honest → ∃ j r wire,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) a.signer) r wire ∧
      wire.toRow? = some a ∧ wire.auth = .seat .fg a.signer)
  (_hfinalHead : ∀ j z r a u, HonestRowAt p c E rho j z r a →
    RowSigner p c rho a z → a.toRow? = some u → ∀ fp,
    u.finality_pair = some fp → ∃ B, HeldAt p c E rho j z B ∧
      fp.height = (heightView p B).h_j ∧ fp.target = (heightView p B).J.root ∧
      TargetQCAt p.E B fp.height (heightView p B).J),
  WCSeed p c E rho w iStar →
    (∀ i, iStar ≤ i ∧ i ≤ rho.events.length → WCInv p c E rho w iStar i) →
    ∀ j x s B, x ∈ rho.honest → iStar ≤ j → IsGateTick p c rho j x s → w.u < s →
      gateResultAt p c E rho j = some (some B) →
      SA.gateTime p.toParams s + 4 * p.Δ ≤ rho.horizon →
      ∀ i y, afterTicksIdx rho (SA.gateTime p.toParams s + 4 * p.Δ) ≤ i →
        i ≤ rho.events.length → confirmedReaderIdx p c E rho y i →
          Block.Preceq B (S_at p c E rho i y)
```

Supplier: `wcg_service4 : WCGService4Statement p c E rho ΔF w iStar`.

The original gate and later reader inclusion types follow. The implicit parameters
also include `w : HealingWitness` and `iStar : Nat`. These suppliers carry the
service inclusion to both stable and confirmed getters.

```lean
theorem wc_gate_result_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x)
```

```lean
theorem wc_gate_result_outputs {n j : Nat} {x : V} {s : Slot} {B : Block} {t : Time}
    (hS : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (inv : WCInv p c E rho w iStar n) (hr : WCResult p c E rho w iStar n j x s B)
    (ht : SA.gateTime p.toParams s ≤ t) (hin : timeIdx rho t ≤ n)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g x t)
```

```lean
theorem wc_service_result_outputs {d t : Time} {B : Block} {y : V}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hservice : ∀ i x, afterTicksIdx rho d ≤ i → i ≤ rho.events.length →
      confirmedReaderIdx p c E rho x i → Block.Preceq B (S_at p c E rho i x))
    (hcut : afterTicksIdx rho d ≤ timeIdx rho t)
    (hy : confirmedReaderIdx p c E rho y (timeIdx rho t))
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g y t)
```

```lean
theorem wcg_gate_result_served {i j : Nat} {x : V} {s : Slot} {B : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (hi : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) :
    Block.Preceq B (S_at p c E rho (j + 1) x)
```

```lean
theorem wcg_gate_result_outputs {n j : Nat} {x : V} {s : Slot} {B : Block} {t : Time}
    (hS : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (inv : WCInv p c E rho w iStar n) (hr : WCResult p c E rho w iStar n j x s B)
    (ht : SA.gateTime p.toParams s ≤ t) (hin : timeIdx rho t ≤ n)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g x t)
```

```lean
theorem wcg_service_result_outputs {d t : Time} {B : Block} {y : V}
    (hS : V2.D.ScheduleWellFormed E rho)
    (hservice : ∀ i x, afterTicksIdx rho d ≤ i → i ≤ rho.events.length →
      confirmedReaderIdx p c E rho x i → Block.Preceq B (S_at p c E rho i x))
    (hcut : afterTicksIdx rho d ≤ timeIdx rho t)
    (hy : confirmedReaderIdx p c E rho y (timeIdx rho t))
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed]) :
    Block.Preceq B (V2.D.outputAt E rho g y t)
```

The gate path anchor is voteTime(s), with deadline earlyTime(s), receiver x,
and first=0. The transfer path anchor is earlyTime(s), with deadline
freezeTime(s), receiver y, and first=0. Pass this receiver's enabled gate
or the exact next voter's joinedAt guard. AnchorCoverage also supplies the
separate epoch from the strict Count read through the consuming action.

The four Count implementations now live in WC/StepGateBatch,
WC/StepTransferReceipts, WCG/StepGateBatch, and WCG/StepTransferReceipts.
Dynamics imports its family suppliers. The pinned Dynamics caller lines
1531 and 2817 map to these two WCG modules.

Serial integration: add the production imports and audit commands from
claude-files/sleep-pwc-round2-audit-fragment.txt to the existing
FGSAProofs audit key. The corresponding coverage fragment uses that same key.
Import these production modules directly into Tests.Axioms.
Do not import Tests.WeakContinuationSleepAxioms there. Keep that standalone
audit registered through the test glob. No new canonical coverage key is needed.

## Round 3 supplier changes

Status remains PREPARED. Four of the 21 original open targets now compile:
WC StepFacts, StepOutput, StepReconcile, and FinalBelow. The other 17 targets
remain EXPECTED-FAIL, with owner P-WC. Their failures include local proof work.
None of the five open family tests currently fails only on a P-As bridge.

Both wc_stepRestart and wcg_stepRestart now prove the full preservation
statements. They no longer return False. Import StepRestart from the matching
family. The original Step and Dynamics wrappers consume these modules.
The delivery, tick, and retrospective paths in the joint producer remain open.

ReceiptOrigins provides wc_receiptOrigins or wcg_receiptOrigins. The latest
replay origin records its exact stamp and restartFree from j+1 to the read.
StepFacts provides current-epoch saved origins and finite facts. WCG's facts
were extracted from Dynamics so they compile apart from the joint producer.

ProposalHistory provides wc_historyMax and wc_history_previousHeads. The
maximum takes ScheduleWellFormed. The previous-HEAD supplier takes the all-time
joined count and a joined original reader. It selects a separate joined actor
at the earlier gate. Proposal's remaining path and Count consumers are open.

StepOutput provides wc_outputStep or wcg_outputStep. Each returns monotonicity
and one of three exact origins: kept output, an enabled gate result, or received
finality. The input includes compatibility of the prior output with next-event
finality. The joint producer must prove that input from the bounded history.
This local event supplier does not replace WCSeededInductionStatement.

StepReconcile scopes its output reader by confirmedReaderIdx at the prior
index. FinalBelow uses the approved reader scope and receipt-root projection.
WCG has matching StepOutput, StepReconcile, and FinalBelow modules.

Serial integration: use the production imports and commands in
claude-files/sleep-pwc-round3-audit-fragment.txt. Use the matching coverage
fragment under AvailableChainFGSAProofs.Tests.Axioms. The corrected round-2
fragment keeps exactly its original 196 rows. Do not import a test module into
Tests.Axioms. The family audit stays registered through the test glob.

The architecture fragment lists the new family modules and their dependencies.
Apply it to the architecture map in the serial integration window. Do not mark
P-WC CLOSED until the original event, Proposal, Empty, consumer, and test targets
compile. Public claims and P23 are unchanged.

Empty's local restart replay now passes the exact wake time to restore.
The internal wcg_empty_live_of_finalBelow adapter no longer takes NoRestart source.
Its remaining source-reader scope repairs are local P-WC work; keep it
EXPECTED-FAIL. No participation or half-cap input was added to the empty route.

## Round 4 suppliers

Status: PREPARED. Eight of the 17 original open targets now compile; nine
remain EXPECTED-FAIL P-WC. No open target was reassigned to P-As.

WC StepTransfer now returns WCRetrospectiveStatement with the joined
next-slot reader guard. WCG Dynamics supplies the matching retrospective
statement. WC Step and WCG Dynamics supply the complete event step and
seeded induction. WC Induction also supplies the sleep safety adapter.
The event proof handles kept, gate, and received-finality output origins.
Next-event finality compatibility follows from the earlier target action
in the prior bounded history. Restart remains full WCInv preservation.

WC Proposal supplies WCProposalPivotStatement. WC ExactProposal supplies
WCProposalAdmissionStatement and WCExactProposalStatement. These existing
Statements are unchanged. Their internal Count and retained-read helpers
now take the all-time joined count, durable/epoch stores, and the actual
joined consuming reader. Import the production modules directly.

New production modules: WC/HeadRelay, WCG/HeadRelay, WC/ProposalService,
WC/ExactReceipts, and WC/InclusionGate. StepGateBatch exposes
wc_gate_active_heads. InclusionGate supplies wc_exact_gate_raw; the full
Inclusion consumer is still open. WCG HeadRelay has no WC proof import.

The old WC headRead_stamped, headRead_laterPath, and previous-path helpers
state NoRestart explicitly. They are legacy interfaces. Sleep adapters
use wc_duty_head_path and the current receiver's joined duty scope.
Assembly/WeakContinuationGrowth callers of those old helpers are P-As
port items; do not infer NoRestart from a sleep regime. Exact new supplier
types and file:line anchors are in the Round 4 report artifacts.

Serial integration: import production modules and copy the 285 commands
from claude-files/sleep-pwc-round4-audit-fragment.txt into Tests.Axioms
under its existing canonical key. Use the matching coverage fragment.
Keep WeakContinuationSleepAxioms and the Proposal test audit registered
through the test glob. No test-module import or allowance is needed.

Round 4 final validation PASS: DCK 532 GREEN, 40 strict roots, 3,613
results, 24 controls. Local exports 200 modules / 252 exports / zero
unaccepted. Layers zero new. Status remains PREPARED with nine local
P-WC expected failures. Implementation head: 16e578fb.

## Round 5 — 2026-10-10

Status: PREPARED for serial integration. All nine original open owned targets
compile with --wfail. There is no remaining on-map EXPECTED-FAIL target.
Inclusion and cached safety commit: 54542242. Final check results follow below.

The exact type inventory is claude-files/sleep-pwc-round5-supplier-types.txt.
Its declaration anchors are in sleep-pwc-round5-declarations.txt. Both truncated
Round 3 reconcile entries now contain their complete source types.

Completed suppliers:

- Inclusion.lean:21, wc_prior_below_proposal: pass a joined selected reader at
  pt.s. Retrospective transfer receives that same next-vote guard.
- Inclusion.lean:69, wc_proposal_gates: pass enabledGateAt for each gate actor,
  receipt-root idealization, receiver epochs, and all-time joined service.
  The gate result is exact; suppressed gates are outside this supplier's scope.
- Inclusion.lean:170, wc_inclusion6_result: returns an exact original WCResult
  as well as ServedFromGateAt. wc_inclusion6 keeps the existing scoped type.
- Safety.lean:285, wc_cachedSafety, and WCG Safety.lean:286, wcg_cachedSafety:
  finite seeded induction supplies WCCachedSafety. Stored outputs keep order
  during sleep and restart. Existing scoped safety types are projections.
- Empty.lean:452, wcg_empty_readerReplay: a matched local prefix preserves the
  exact source confirmedReaderIdx. It transfers the enabled gate, local epochs,
  awake interval, and applied wakes. Same-time wake ordering is retained.
- Empty.lean:672, wcg_empty_finalBelow: the source service reader is confirmed,
  and its matched prefix time is no later than the continuation prefix time.

P-As caller ports (unowned files, left unchanged):

Assembly/WeakContinuationGrowth.lean:543/:565/:578 still use the old Inclusion
helper telescopes. Use the Round 5 joined reader and enabled gate forms.
wc_suffix_mono also takes schedule and seed; its conclusion is unchanged.
Use wc_inclusion6_result to retain the original result evidence.

Assembly/WeakContinuationGrowth.lean:36 calls the internal growth implementation.
Growth.lean:35 now takes these explicit component values before its existing
WCGrowthStatement result. The existing statement and public claims are unchanged:

```lean
hcache : WCCachedSafety p c E rho iStar Q
hcover : ∀ pt : PtSP, u + 2 ≤ pt.s →
  HonestProposal E rho (fgsaInterface p c) pt.s pt.P →
  SA.gateTime p.toParams pt.s ≤ rho.horizon →
  ∃ x ∈ rho.honest,
    Block.Preceq pt.P (S_at p c E rho rho.events.length x)
```

WC checkpoint proves both components from the seeded induction and exact
original result. No new public assumption is required. The cached result at
horizon orders a trigger output even if that trigger reader later sleeps.
The deadline inclusion still uses the public confirmed-reader guard.

Assembly/WeakContinuationGrowth.lean:990 must supply Empty.lean:608 cached source
safety and Empty.lean:609 source proposal coverage before the finalBelow bridge:

```lean
hcache : WCCachedSafety p c E source iSource w.QStar
hcover : ∀ pt : PtSP, w.u + 2 ≤ pt.s →
  HonestProposal E source (fgsaInterface p c) pt.s pt.P →
  SA.gateTime p.toParams pt.s ≤ source.horizon →
  ∃ x ∈ source.honest, Block.Preceq pt.P
    (V2.D.outputAt E source (fgsaInterface p c).stable x source.horizon)
```

Produce hcache with wcg_cachedSafety from the source seeded induction. Produce
hcover with the source exact original-gate result and cached monotonicity.
The source comparison witness need not remain honest in the continuation.
Empty replays the trigger reader in the source before it makes this comparison.
No continuation participation or half-cap premise is added to the empty route.

Assembly/WeakContinuationGrowth.lean:1002 must pass that cached source safety to
wcg_empty_finalBelow. Its existing source service supplier now has this final
reader clause (Empty.lean:686); use the completed WCGService4Statement supplier:

```lean
∀ k y, afterTicksIdx source (SA.gateTime p.toParams s + 4 * p.Δ) ≤ k →
  k ≤ source.events.length → confirmedReaderIdx p c E source y k →
  Block.Preceq B (S_at p c E source k y)
```

The caller ports remain P-As work. All owned tests use explicit component
contracts and compile; no owned test waits only on a P-As bridge.
No P-As, public Claims/Statements, P23, dependency, checker, or baseline file
was changed. No public meaning STOP occurred.

Round 5 final validation: package DCK PASS. 541 GREEN modules, 43 strict roots,
3,662 results, and 24 controls PASS. Complete local export/coverage PASS:
207 proof modules, 252 exports, zero unaccepted. Production strict audit:
313 commands/results; all 285 Round 4 rows retained. Growth has four local
contract commands; Inclusion has two; Empty has 15. Proposal retains three.
Only propext, Classical.choice, and Quot.sound occur. Layers: 72 inherited /
zero new; source scopes PASS. git diff --check and added-line bounds PASS.
Proof commits: 54542242 and 9d6e4742. No new module or allowance is needed.
All owned work is GREEN. Status: PREPARED for serial integration and P-As ports.

## Round 6 — import repair and input audit

Base ef79e7cf; source commit c914737e. PREPARED. All 71 targets remain GREEN.
ExactReceipts uses the public CatchUp import and target-service constructors.
One authorized theorem: fgsa_target_service_genesis, Shared/CatchUp:417.
Its type is TargetReceiptService E rho Block.genesis freeze x; proof Or.inl rfl.
Public claims and existing statement types are unchanged.

Validation PASS: DCK (43 strict roots, 3,663 results, 24 controls); headers;
layers (72 inherited / zero new); complete local exports (207 proof modules /
252 exports / zero unaccepted); 314 local coverage commands; source scopes;
git diff --check. All 265 public family theorem types print without truncation.

Serial integration: use the Round 6 audit, coverage, and architecture fragments
in claude-files/. They retain all Round 5 rows and add the genesis theorem
under the existing Tests.Axioms key. Production imports only. Do not copy
the standalone sleep audit as an import into Tests.Axioms.

The Round 5 exact component types and unowned caller anchors still apply.
The next table names true scoped producers and exact open obligations.
Each of 2,065 explicit binder entries is classified in
claude-files/sleep-pwc-round6-input-inventory.json. Full source telescopes and
record fields are in sleep-pwc-round6-input-signatures.txt; compiled types
are in sleep-pwc-round6-supplier-types.txt. No anonymous premise is omitted
from the full type evidence. The table groups repeated fields once.

## Round 6 — SCOPE-NARROW input audit

Scope: all 265 public theorems declared in the two owned proof directories,
plus their WC statement and WCG interface telescopes. Both Export facades
contain imports only. The audit includes local suppliers visible through those
imports; it does not claim closure of imported unowned family packages.

Abbreviations: WC = Proofs/WeakContinuation; WCG = Proofs/WeakContinuationGrowth;
Foundations, Shared, and Assembly = the corresponding FGSAProofs/Proofs paths;
Regimes = FGSAClaims/Statements/Regimes. Full paths and exact hypotheses are in
claude-files/sleep-pwc-round6-input-signatures.txt. Compiled types are in
claude-files/sleep-pwc-round6-supplier-types.txt. Repeated telescope inputs are
listed once below; 2,065 explicit named binder occurrences are classified in
claude-files/sleep-pwc-round6-input-inventory.json; each occurrence retains its
full quantifiers in those files.
Rows 66 and 67 cover individual selected facts and data parameters. They
are conditional inputs, not unproduced universal service records.

TRUE means true in the stated regime and selected scope. A valid finite run
alone does not imply synchrony, hash idealization, fault/participation bounds,
recovery, a seed, or agreement with another run. These public conditional
premises are not hidden new assumptions. No record is claimed true at arbitrary
cuts. Named unowned declarations with open ports are not certified by this
package DCK. A consumer, restriction, or conversion is not counted as producer.

Producer anchor: wc_finalBelow at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/FinalBelow.lean:17.
Producer anchor: wc_finiteFacts at
  AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuation.lean:412.
Producer anchor: wc_relay_head_relay_scope at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/HeadRelay.lean:429.
Producer anchor: wc_relay_head_emission_scope at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/HeadRelay.lean:1065.
Producer anchor: wc_transfer_path_coverage at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/AnchorCoverage.lean:162.
Producer anchor: wcg_transfer_path_coverage at
  AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/AnchorCoverage.lean:162.
Producer anchor: wcg_retrospective at
  AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:256.
Producer anchor: wc_retained_score_scope at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactReceipts.lean:125.
Producer anchor: wc_local_proposal_service at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactReceipts.lean:13.
Producer anchor: wc_accepted_target_service at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactReceipts.lean:90.
Producer anchor: wc_emitted_proposal_service at
  AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactReceipts.lean:250.
Producer anchor: fgsa_storedTargetsBelowOutput at
  AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:58.

```text
┌───────────────────────────────┬───────────────────────────────┬───────────────────────────────┐
│ Explicit input                │ Status / named producer /     │ Ordinary finite sleep run     │
│                               │ open owner                    │                               │
├───────────────────────────────┼───────────────────────────────┼───────────────────────────────┤
│ 01 valid; schedule;           │ Named: Base₂.valid; Execution │ TRUE for valid finite runs.   │
│ hV/hE/hS/hschedule            │ Valid.toScheduleWellFormed.   │ Schedule is a projection.     │
│                               │ Regimes:20.                   │                               │
│ 02 linked; cstar              │ Input: Base₂.linked/cstar,    │ Conditional setup law;        │
│                               │ Regimes:21-22. Owner: regime  │ validation alone does not     │
│                               │ caller.                       │ imply it.                     │
│ 03 RestartsAtWakes;           │ Input: Base₂.restartsAtWakes, │ TRUE in approved finite sleep │
│ hwakes/hnr                    │ Regimes:23. Owner: regime     │ runs; no global NoRestart     │
│                               │ caller.                       │ inference.                    │
│ 04 delta; deltaF; ΔF; G and   │ Input: Base₂.delta and        │ Conditional parameter laws;   │
│ gapPos                        │ synchrony regime. Owner:      │ not arbitrary run facts.      │
│                               │ regime caller.                │                               │
│ 05                            │ Input:                        │ Conditional digest            │
│ NamedReceiptRootCollisionFree │ Base₂.receiptIdealization,    │ idealization on named receipt │
│                               │ Regimes:27. Owner: regime     │ scope; not all values.        │
│                               │ caller.                       │                               │
│ 06 NamedRootCollisionFree     │ Named: Base₂.idealization,    │ TRUE under receipt            │
│                               │ Regimes:32. Safety-only       │ idealization; conditional     │
│                               │ projection.                   │ otherwise.                    │
│ 07 PartialSynchronyBy; hsync  │ Input: Recovery₂.sync,        │ Conditional delivery regime;  │
│                               │ Regimes:98;                   │ bounds only ready,            │
│                               │ continuation.sync. Owner:     │ non-excluded objects.         │
│                               │ caller.                       │                               │
│ 08 fault count; FaultQ;       │ Named:                        │ Conditional WC bound. No      │
│ FaultX                        │ Foundations/Counts:14,19.     │ FaultX required by WCG.       │
│                               │ Input fault count: regime     │                               │
│                               │ caller.                       │                               │
│ 09 joined participation;      │ Input: continuation           │ Conditional count at all      │
│ hpart/hP                      │ joinedParticipation;          │ covered times. Does not       │
│                               │ source/suffix join port.      │ require all honest joined.    │
│                               │ Open: P-As.                   │                               │
│ 10 WCG FaultQ / half cap      │ Proved: WCG/Counts:32,49,57   │ TRUE on the nonempty route.   │
│                               │ from nonempty suffix          │ Empty suffix has no half-cap  │
│                               │ participation.                │ premise.                      │
│ 11 FinalitySlashableBound;    │ Input: WCG                    │ Conditional public            │
│ haccountable                  │ continuation.accountable.     │ accountability bound, permits │
│                               │ Owner: regime caller.         │ retained-set shrink.          │
│ 12 RStore; hstore             │ Named: Foundations/Store:19   │ TRUE for protocol stores,     │
│                               │ fgsa_rStore.                  │ also through restart.         │
│ 13 RStoreDurable              │ Named: Foundations/Store:35   │ TRUE across restarts; durable │
│                               │ fgsa_rStoreDurable.           │ trees and signed rows only.   │
│ 14 RStoreEpoch                │ Named: Foundations/Store:39   │ TRUE for the exact receiver   │
│                               │ fgsa_rStoreEpoch.             │ restart-free index interval.  │
│ 15 RMonoAll; hmono            │ Named: Foundations/Store:46   │ TRUE through restart; FG      │
│                               │ fgsa_rMonoAll.                │ state bounds, not raw vote    │
│                               │                               │ stamps.                       │
│ 16 RActive; hactive           │ Named: Foundations/Store:84   │ TRUE for active views. No     │
│                               │ fgsa_rActive.                 │ receipt request for all       │
│                               │                               │ durable TF blocks.            │
│ 17 RFrameExactNext; hframe    │ Named: Foundations/Store:78   │ TRUE structural frame         │
│                               │ fgsa_rFrameExactNext.         │ identity at the actual store. │
│ 18 RFrameNextEpoch; hmeta     │ Named: Foundations/Store:153  │ TRUE with the field's         │
│                               │ fgsa_rFrameNextEpoch.         │ receiver epoch. No all-run    │
│                               │                               │ stamp persistence.            │
│ 19 RRec; hrec                 │ Named:                        │ TRUE store reconcile law.     │
│                               │ Foundations/Reconcile:80      │                               │
│                               │ fgsa_rRec.                    │                               │
│ 20 RGeo; hgeo; RCert; hcert   │ Named: Foundations/Certificat │ TRUE certificate geometry and │
│                               │ es:15,30.                     │ validity laws.                │
│ 21 TSrc; hsrc; LabelBound;    │ Named:                        │ TRUE scheduled source-time    │
│ hlabel                        │ Foundations/Sources:35,131.   │ and label bounds.             │
│ 22 RQCOrigin; hqc; RStrat;    │ Named:                        │ TRUE under valid linked setup │
│ hstrat                        │ Foundations/Sources:316,428.  │ and FaultQ; not universal     │
│                               │ Exact BasePrem caller port    │ receipt scopes.               │
│                               │ open: P-As.                   │                               │
│ 23 EmittedRowsNoSlash;        │ Named: Foundations/Client:17  │ TRUE under Linked; honest     │
│ hnoslash                      │ fgsa_clientSafeAll.           │ emitted rows only.            │
│ 24 hemitted                   │ Named:                        │ TRUE for the actual honest    │
│ height/action/gate callback   │ Foundations/Sources:180       │ named row. Original source    │
│                               │ sourceDiscipline_emittedName. │ gate and ancestry kept.       │
│ 25 htargets stored obligation │ Named:                        │ TRUE for stored obligations   │
│ callback                      │ FGSA/Proofs/LeaseOutput:35;   │ below cached output. Not TF   │
│                               │ Foundations/Leases:58.        │ receipt service.              │
│ 26 hlease origin and          │ Named:                        │ TRUE for actual writes; later │
│ last-write callback           │ Foundations/Leases:500.       │ tests use enabledGateAt.      │
│                               │ Enabled-guard adapter open:   │ Suppressed gates write no     │
│                               │ P-As.                         │ lease.                        │
│ 27 hfast epoch/origin         │ Named partial:                │ TRUE for volatile current     │
│ callback                      │ Foundations/Leases:541. Exact │ fast writes; reset erases     │
│                               │ restartFree adapter open:     │ them. Adapter is still        │
│                               │ P-As.                         │ needed.                       │
│ 28 hdeadlines protection      │ Named: Foundations/Leases:592 │ TRUE for actual obligation    │
│ callback                      │ fgsa_leaseOrigins_ancestorDea │ ancestry and its stored       │
│                               │ dlines.                       │ deadline.                     │
│ 29 hheldRows carriage         │ Named:                        │ TRUE for actual HeldAt        │
│ callback                      │ Foundations/Carrier:125       │ carriers, their rows, and     │
│                               │ held_chain_row_origin_before. │ earlier delivery occurrences. │
│ 30 hscopeRows callback        │ Named:                        │ TRUE for named in-run scope   │
│                               │ Assembly/WeakContinuation:47  │ and honest signers, not       │
│                               │ wc_scopedRowOrigins. Assembly │ emitted-only receipt scope.   │
│                               │ port open: P-As.              │                               │
│ 31 hfinalHead target-QC       │ Named: Foundations/Cap:293    │ TRUE for the actual honest    │
│ callback                      │ cap_finality_head.            │ finality row and its exact    │
│                               │                               │ target.                       │
│ 32 WCSeed; hseed/hs           │ Named candidate:              │ Selected recovered source     │
│                               │ Assembly/WC:480;              │ snapshot only. FALSE at an    │
│                               │ Assembly/WCGSeed:137,283.     │ arbitrary finite cut.         │
│                               │ Exact sleep port open: P-As.  │ RecoverySleep₂ keeps all      │
│                               │                               │ honest awake after GST; no    │
│                               │                               │ extra continuation join       │
│                               │                               │ premise.                      │
│ 33 WCFiniteFacts; finite      │ Proved suffix:                │ TRUE for bounded actual       │
│ input                         │ WC/StepFacts:298;             │ stores and original           │
│                               │ WCG/StepFacts:297. Source     │ occurrences under the lane    │
│                               │ seed port open: P-As.         │ inputs.                       │
│ 34 WCInv; hi/hinv/inv         │ Proved: WC/Induction:18;      │ TRUE after the selected       │
│                               │ WCG/Dynamics:885 plus WC      │ WCSeed under lane inputs; not │
│                               │ causal producer.              │ before that seed.             │
│ 35 WCResult; hr/hresult       │ Proved existence:             │ TRUE for an actual nonempty   │
│                               │ WC/StepGateHistory:19;        │ suffix result. FALSE for a    │
│                               │ WCG/StepGateHistory:19.       │ suppressed gate result.       │
│                               │ Enabled: WC/Epoch:142;        │                               │
│                               │ WCG/Epoch:186.                │                               │
│ 36 WCBelowHistory; hb/history │ Proved: WC/Safety:34,66;      │ TRUE for selected seed        │
│                               │ WCG/Safety:34,66; invariant   │ prefixes or actual completed  │
│                               │ origins.                      │ result origins.               │
│ 37 WCFinalizedOccurrence; hf  │ Proved: WC/Origins:30 and     │ TRUE for scoped actual        │
│                               │ WCG/Origins:111, from exact   │ carriers; no receipt required │
│                               │ finality fields and row       │ for all TF members.           │
│                               │ origins.                      │                               │
│ 38 WCFinalityTargetEarlierSta │ Proved: WC/StepFinality:18    │ TRUE under exact held-row/QC  │
│ tement; hcausal               │ wc_finalityTargetEarlier. WCG │ origin inputs. WCG producer   │
│                               │ consumes that same additive   │ port open: P-As.              │
│                               │ supplier.                     │                               │
│ 39 WCDutyInput; hd/h          │ Proved selection:             │ TRUE only for actual enabled  │
│                               │ WC/ProposalService:42, actual │ duties. FALSE for arbitrary   │
│                               │ joined clock; gate pre-join:  │ suppressed duty inputs.       │
│                               │ WC/Epoch:158; WCG/Epoch:41.   │                               │
│ 40 WCHeadRead; h/read         │ Proved: WC/StepTransfer:23;   │ TRUE for selected joined      │
│                               │ WCG/Dynamics:256;             │ next-slot reads. Prior-slot   │
│                               │ WC/ProposalHistory:149.       │ request has its own join      │
│                               │                               │ guard.                        │
│ 41 WCControllingRow           │ Selected certificate witness: │ TRUE only for an actual       │
│                               │ WC/Frame:30 and WCG/Frame:30. │ controlling certificate row;  │
│                               │                               │ preserves frame and ancestry. │
│ 42 WCUsableHighSourcesBelow;  │ Open construction at selected │ Conditional selected source   │
│ hhigh                         │ duty: caller P-WC; from WCInv │ bound, not receipt for every  │
│                               │ high-source fields. Frame:30  │ W at every receiver.          │
│                               │ consumes it.                  │                               │
│ 43 WCFrameBelow / LiveBelow / │ Proved: WC/Frame:30,257,282;  │ TRUE at the selected duty     │
│ PathBelow / DutyView          │ WCG/Frame:30,257,282.         │ under lane inputs; duty view  │
│                               │ Requires actual duty and      │ is frozen for HEAD.           │
│                               │ high-source evidence.         │                               │
│ 44 WCProposalPivot; hpivot    │ Proved: WC/Proposal:860       │ TRUE for a selected honest    │
│                               │ wc_proposalPivot.             │ proposal; previousHeads asks  │
│                               │                               │ joined at the prior vote.     │
│ 45                            │ Proved: WC/ExactProposal:260  │ TRUE for the exact emitted    │
│ WCProposalAdmittedBeforeVote  │ wc_proposalAdmission.         │ proposal and an actual joined │
│                               │                               │ consuming HEAD reader.        │
│ 46 WCCachedSafety;            │ Proved: WC/Safety:285;        │ TRUE from seeded induction    │
│ hcache/hsafe                  │ WCG/Safety:286. Source caller │ through finite horizon,       │
│                               │ construction open: P-As.      │ including sleeping cached     │
│                               │                               │ outputs.                      │
│ 47 SeededInduction /          │ Proved: WC/Induction:18;      │ TRUE under their explicit     │
│ FrameLive / Safety /          │ Frame:257; Safety:361;        │ lane telescopes. A callback   │
│ FinalBelow callbacks          │ FinalBelow. WCG analogues use │ value is not an extra regime  │
│                               │ Dynamics:885.                 │ fact.                         │
│ 48 HeadRelayServiceScope;     │ Proved:                       │ TRUE for selected             │
│ hScope                        │ WC/HeadRelay:429,928,1065;    │ accepted/emitted HEAD and     │
│                               │ WCG equivalents. Exact        │ joined/enabled receiver;      │
│                               │ anchors and receiver epoch.   │ service is guarded by         │
│                               │                               │ non-exclusion.                │
│ 49 ReceiverService /          │ Proved:                       │ TRUE for the selected         │
│ TargetReceiptService          │ WC/ExactReceipts:13,90,250;   │ admissible target; receiver   │
│                               │ Shared/CatchUp:417,422. No    │ floor F <= target is          │
│                               │ input universal receipt       │ explicit. Genesis             │
│                               │ bundle.                       │ unconditional.                │
│ 50                            │ Proved:                       │ TRUE for selected             │
│ ReceiptCoverageAnchorPremises │ WC/AnchorCoverage:47,162; WCG │ paths/receiver. Gate          │
│                               │ counterparts;                 │ anchor=vote, deadline=early;  │
│                               │ WC/ProposalService:138.       │ transfer anchor=early,        │
│                               │                               │ deadline=freeze.              │
│ 51 ScoreServiceScope;         │ Proved scopes:                │ TRUE only for exact           │
│ RetainedServiceScope;         │ WC/ExactReceipts:125;         │ source/target joined duties,  │
│ ScoreRunGeometry              │ ExactProposal:181. Geometry   │ target floors, actual frozen  │
│                               │ selected by retained read     │ histories.                    │
│                               │ suppliers.                    │                               │
│ 52 IsGateTick; enabledGateAt; │ Selected event input. Enabled │ IsGateTick alone does not     │
│ gatePassedAt                  │ producer:                     │ imply enabled. Nonempty gate  │
│                               │ WC/Epoch:16,121,142;          │ result gives enabled. Raw     │
│                               │ WCG/Epoch:16,186,192.         │ gate formula has no write     │
│                               │                               │ claim.                        │
│ 53 joinedAt / headReader /    │ Selected read guards;         │ TRUE only at the actual       │
│ caughtUp / confirmedReaderIdx │ WC/ProposalService:14,42.     │ reader tick.                  │
│                               │ Current epoch:                │ WakesAppliedAtIdx preserves   │
│                               │ WC/Epoch:275,357,413;         │ same-time restart order.      │
│                               │ WCG/Epoch:130.                │                               │
│ 54 hH selected joined seats;  │ Proved local construction:    │ TRUE for selected joined seat │
│ hL pool provenance            │ WC/StepGateBatch:91;          │ set and actual pool objects;  │
│                               │ ProposalService:333; WCG gate │ no every-honest join          │
│                               │ batch.                        │ requirement.                  │
│ 55 hrec exact gate receipts;  │ Proved: WC/StepGateBatch:91;  │ TRUE for selected joined      │
│ hbatch; hhead; hprior         │ Inclusion:170 constructs      │ cohort and enabled gate.      │
│                               │ hhead/hprior for              │ Suppressed gates treated by   │
│                               │ Inclusion:69.                 │ Epoch:165.                    │
│ 56 hgate callback on current  │ Proved:                       │ TRUE for enabled gates only,  │
│ enabled tick                  │ WC/Step:388,399,410,421 gate  │ after seed label. No write    │
│                               │ cases; WCG/Dynamics:479.      │ requested at suppressed       │
│                               │ StepOutput:92 is its          │ gates.                        │
│                               │ consumer.                     │                               │
│ 57 hservice later-reader      │ Proved: WC/StepService:284;   │ TRUE for confirmedReaderIdx   │
│ callback                      │ WCG/StepService:283.          │ in current epoch; not all     │
│                               │ Empty:682 consumes scoped     │ honest receivers.             │
│                               │ source service.               │                               │
│ 58 hcover cached exact        │ Proved WC: Growth:219-232     │ TRUE for selected honest      │
│ proposal coverage             │ from Inclusion:170 and cached │ proposal whose gate fits      │
│                               │ monotonicity. Source assembly │ horizon. Witness may be       │
│                               │ port open: P-As.              │ outside retained honest set.  │
│ 59 Empty hlive / hfinal /     │ Named: WC/Live:16;            │ TRUE on equal-horizon         │
│ hincl / hproposals / hout     │ WCG/Empty:672,119,600. Growth │ retained replay from selected │
│                               │ callbacks constructed in      │ source inputs. Empty needs no │
│                               │ Empty:600.                    │ continuation count.           │
│ 60 AgreesThrough₂ /           │ Input: continuation.agrees.   │ Conditional exact prefix or   │
│ RetainedAgreesThrough₂; ha    │ Owner: caller; replay         │ per-retained-node             │
│                               │ producers WC/Replay:19;       │ event/awake/input agreement.  │
│                               │ WCG/EventReplay:13.           │ Never a consequence of        │
│                               │                               │ validity alone.               │
│ 61                            │ Input public regime. Owner:   │ Conditional regime; permits   │
│ CleanGrowthContinuationSleep₂ │ caller; WCG/Counts:57         │ empty suffix and honest-set   │
│ / Base₂; hb                   │ consumes it.                  │ shrink. No all-honest join    │
│                               │                               │ field.                        │
│ 62 hno directional            │ Proved: WCG/Origins:44 from   │ TRUE on scoped directional    │
│ no-slashing callback          │ FinalitySlashableBound;       │ carriers under                │
│                               │ lowFinalized:98 uses it.      │ accountability; no extra      │
│                               │                               │ fault-count premise.          │
│ 63                            │ Input public growth regime.   │ Conditional honest joined     │
│ AwakeProposerRecurrenceFrom;  │ Owner: caller; Regimes:140.   │ proposer recurrence in        │
│ hrecurrence                   │ Growth:35 and Empty:145       │ horizon windows.              │
│                               │ consume it.                   │                               │
│ 64 NoRestart legacy hnr       │ Open input: legacy-only       │ FALSE in finite runs with     │
│                               │ caller.                       │ wakes/restarts. Not inferred  │
│                               │ WC/Proposal:58,101,142,165.   │ or used by repaired WC/Live,  │
│                               │ Owner: P-As caller port.      │ Inclusion, or exact service   │
│                               │                               │ route.                        │
│ 65 GST/read cuts; hGST;       │ Explicit selected timing      │ Conditional exact bounds.     │
│ send/anchor/deadline bounds   │ inputs; WC/ExactProposal:22   │ GST<=vote never gives         │
│                               │ window producer;              │ GST<=slotStart of same/prior  │
│                               │ WC/Epoch:470,480 anchor       │ slot.                         │
│                               │ checks.                       │                               │
│ 66 Local event/member/decode/ │ Selected facts supplied by    │ Conditional on stated         │
│ root/ancestry/floor/interval  │ the calling proof; exact      │ object/index. No assertion    │
│ hypotheses                    │ per-theorem source in         │ for arbitrary inputs. Receipt │
│                               │ input-signatures.txt. Owner:  │ service keeps actual          │
│                               │ caller P-WC, or P-As at       │ F<=target or non-exclusion.   │
│                               │ integration.                  │                               │
│ 67 Parameters and data (E/rho │ Inputs, not proof             │ No truth value. Output        │
│ /p/c/w/indices/blocks/slots/o │ obligations. Exact            │ selectors must name the two   │
│ utputs)                       │ declarations and implicit     │ public getters when that      │
│                               │ contexts in compiled          │ premise occurs.               │
│                               │ supplier-types.txt.           │                               │
│ 68 WCReceiptOrigins;          │ Proved:                       │ TRUE for actual stores.       │
│ hreceipts                     │ WC/ReceiptOrigins:415;        │ Restored stamps equal the     │
│                               │ WCG/ReceiptOrigins:415.       │ exact wake time; original     │
│                               │ Replay ports preserve each    │ acceptance remains a trigger. │
│                               │ original occurrence.          │                               │
│ 69 RetainedReadPremises       │ Proved: WC/ExactProposal:40   │ TRUE for the exact            │
│                               │ wc_retainedReads; Shared      │ proposal/HEAD pair and        │
│                               │ retained-read suppliers.      │ selected comparison cone.     │
│                               │                               │ Every receiver request has    │
│                               │                               │ the actual joined guard.      │
│ 70 WCLeaseOrigin /            │ Proved bounded suffix fields: │ TRUE for the actual stored    │
│ WCTargetOrigin                │ WC/StepFacts:298;             │ lease or certified target,    │
│                               │ WCG/StepFacts:297. Source     │ with the original source row  │
│                               │ seed construction open: P-As. │ and enabled write. These are  │
│                               │                               │ provenance, not remote        │
│                               │                               │ receipt requests.             │
│ 71                            │ Proved: WC/Origins:20 via     │ TRUE pure certificate/order   │
│ WCFinalizedCrossingStatement; │ KitFG finalizedCrossing.      │ law under its explicit        │
│ certificate-law callbacks     │ Instance: fgCertificateLaws.  │ certificate hypotheses; no    │
│                               │                               │ run-wide delivery or join     │
│                               │                               │ premise.                      │
│ 72 hAw / hBound / hmarker     │ Proved at selected duty:      │ TRUE only for the actual      │
│ local epoch callbacks         │ WC/ProposalService:58;        │ awake receiver interval and   │
│                               │ enabled gate:                 │ restart marker. Not global    │
│                               │ WC/Epoch:81,104. WCG          │ restart freedom.              │
│                               │ analogues.                    │                               │
│ 73 hB / hfinal joined-reader  │ Proved selected history/frame │ TRUE at the requested joined  │
│ floor callbacks               │ comparison:                   │ vote tick, with the selected  │
│                               │ WC/Proposal:329,399,521;      │ target floor; not every       │
│                               │ WCInv. WCG transfer           │ honest receiver.              │
│                               │ counterparts.                 │                               │
│ 74 hF bounded receiver-floor  │ Proved from RMonoAll and      │ Conditional F<=selected       │
│ callback                      │ selected F<=K bound;          │ target through the exact      │
│                               │ WC/ProposalService:254 and    │ prefix. No all-TF target      │
│                               │ both AnchorCoverage path      │ service requirement.          │
│                               │ constructors.                 │                               │
│ 75 hbefore / hcompleted /     │ Proved: WC/Proposal:234;      │ Conditional exact cut, label, │
│ htest order callbacks         │ WC/ProposalHistory:84,133;    │ event, or replay filter.      │
│                               │ WCG/EventReplay:13 and        │ These are order facts, not    │
│                               │ Seed:62,76.                   │ enabled-gate existence        │
│                               │                               │ claims.                       │
│ 76 hclosed / hpath view-path  │ Named path producer:          │ TRUE on the selected          │
│ callbacks                     │ WC/Frame:282;                 │ frame-to-target ancestry      │
│                               │ WC/ProposalService:254.       │ path. No receipt request for  │
│                               │ Caller must select the stated │ arbitrary durable TF          │
│                               │ closed view.                  │ contents.                     │
│ 77 hmax / hprev prior-result  │ Proved:                       │ TRUE for the bounded result   │
│ callbacks                     │ WC/ProposalHistory:21,149;    │ maximum and prior joined      │
│                               │ WC/Proposal:860.              │ reader. The prior vote needs  │
│                               │                               │ its own join, not current     │
│                               │                               │ join alone.                   │
│ 78 hfinal next-event output   │ Proved local construction:    │ TRUE for the actual next      │
│ compatibility callback        │ WC/Step:252; WCG/Dynamics     │ event from bounded history.   │
│                               │ event induction.              │ Does not ask for service at   │
│                               │ StepOutput:90 consumes it.    │ suppressed gates.             │
│ 79 awake participation legacy │ Proved arithmetic consumer:   │ Conditional awake count gives │
│ arithmetic input              │ WCG/Counts:15. Explicit count │ a half cap; it does not prove │
│                               │ input belongs to caller.      │ duty join. Sleep production   │
│                               │                               │ route uses joined             │
│                               │                               │ participation at Counts:32.   │
└───────────────────────────────┴───────────────────────────────┴───────────────────────────────┘
```

Audit result: no false universal receipt, gate, join, or time-cut requirement
was found in the repaired P-WC service routes. No scope statement changes are
needed in this round. Suppressed gates remain separate. Historical TF fields
in WCSeed/WCInv preserve one selected recovered carrier; they request no
receiver service for arbitrary durable carriers. RecoverySleep₂.awake and
suffixNoRestart support the recovered source snapshot after the join window.
They are not continuation premises. The exact WCSeed producer port remains
P-As work. Its all-honest source snapshot is not asserted at arbitrary cuts.

The four legacy NoRestart helpers remain conditional exports. They are false
as unconditional sleep suppliers. Repaired production routes use receiver-local
joined duty service. P-As must port its legacy callers; it must not synthesize
NoRestart from RecoverySleep₂. This is an open integration obligation.

Open producer ports: P-As must build the exact WC/WCG source seed and finite
facts; supply the enabled last-write and fast-write epoch adapters; join the
source cached safety and cached proposal coverage producers; and pass the
proved WC finality-causality supplier to WCG. Existing Round 5 unowned caller
anchors remain. No P-H1, P-H2, P-Ou, Assembly, Inhabit, public Claim, or public
Statement file changes. Status remains PREPARED until these ports are closed.
