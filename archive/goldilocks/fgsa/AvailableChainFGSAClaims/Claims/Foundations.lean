module
public import AvailableChainFGSAClaims.Statements.FinalityApi
public import AvailableChainFGSARun.Statements.Slashing
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSARun.Statements.Client
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainGeneric.Statements.AC.Lease
public import AvailableChainFGSAClaims.Statements.FrameNext
public import AvailableChainFGSAClaims.Statements.ComposeNext

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FS20 conclusion of bp.clientSafety.v1. T7.9 A is pairwise and order-free. -/
def ClientSafeAll (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  ∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A8: Linked is the only premise. Restarts are permitted (T7.9 A, route R1). -/
def ClientSafetyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    V2.D.Linked (fgsaFamilies p c).linked rho → ClientSafeAll p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
S3 X5: the family-(0) package form of client safety. -/
def ClientSafetyBaseClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → ClientSafeAll p c E rho

/- DECISION P23-A: bp.receiptCoverage.v2 uses ReceiptCoverageSleepStatement.
The legacy statement, equation, and fgsa_receiptCoverage are retired.
Internal no-restart consumers use fgsa_receiptCoverage_ready. -/

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10: all seven F1 foundation channels. BaseSet and FaultQ are in the package. -/
def FGFoundationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → FGFoundationNext p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10, G30: the source frame at every threshold.
BaseSet and FaultQ are in the package. -/
def SrcFrameAboveClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → SrcFrameAboveStmt p c E rho


open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The FG carrier of emitted or delivered proposals, including ancestors. -/
def RunFGBlock (X : FGBlock (Fin p.n)) : Prop :=
  ∃ o N,
    o.payload = Msg.proposal N ∧
    ((∃ x t, V2.D.Run.emits E rho x o t) ∨
      (∃ x t, V2.Event.deliver x o t ∈ rho.events)) ∧
    Block.Preceq (eraseFG X) N.erase

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.carrier.v1: erasure on the run carrier keeps identity and geometry. -/
def CarrierAt : Prop :=
  (∀ X Y, RunFGBlock p c E rho X → RunFGBlock p c E rho Y →
    (eraseFG X = eraseFG Y → X = Y) ∧
    (FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y))) ∧
  (∀ X, RunFGBlock p c E rho X →
    eraseFG X.parent = (eraseFG X).parent ∧
    (eraseFG X).slot = X.slot ∧ (eraseFG X).root = X.root) ∧ RCarrierView p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.store.v2: snapshot invariants and the two temporal channels.
Each temporal channel retains its NoRestart premise. -/
def StoreAt : Prop :=
  (∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
    CStoreInv p (storeAt p c E rho i x)) ∧
  (V2.D.ScheduleWellFormed E rho → RStoreCumul p c E rho ∧ RMono p c E rho)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.activeView.v2: the active tree and its unchanged vote/stamp data. -/
def ActiveViewAt : Prop := RStore p c E rho ∧ RActive p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.leaseOrigins.v2: all obligation rows have a passed gate origin.
The statement includes due rows, target order, ancestor deadlines and fast writes. -/
def LeaseOriginsAt : Prop := ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
  let st := storeAt p c E rho i x
  (∀ row ∈ st.base.obligations, ∃ j < i, ∃ s B,
    IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
    gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B) ∧
  Gen.AC.Root.LeaseMapChain st.base ∧
  (∀ K g deadline, (K, g, deadline) ∈ st.base.obligations →
    ∀ B, B ≠ .genesis → Block.Preceq B K →
      Gen.AC.Root.ProtectsUntil st.base B g deadline) ∧
  (∀ s X, X ∈ (FGSA.fastWriteAt st s).getD [] →
    ∃ j < i, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
      ∃ B, gateResultAt p c E rho j = some (some B) ∧
        Block.Preceq X B ∧ fastAt p c E rho x s X)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.sourceDiscipline.v2(a,d): actual sources, emitted names and label bounds.
DC: INTENTIONAL optional sends; every emitted row has a nonempty source pair. -/
def SourceDisciplineBaseAt : Prop :=
  TSrc p c E rho ∧ LabelBound p c E rho ∧
  (∀ j x r a, HonestRowAt p c E rho j x r a →
    ∃ e C G, namedEntry a.payload.height_pair = some e ∧
      actionSourceFG p c E rho x r = some (some C) ∧
      e = ((heightView p C).h, (heightView p C).T_h.root) ∧
      FGBlock.Preceq (heightView p C).T_h C ∧
      gateResult p c E rho x (r * p.R) = some (some G) ∧
      Block.Preceq (eraseFG C) G ∧ fastAt p c E rho x (r * p.R) (eraseFG C))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.sourceDiscipline.v1(a–d), including target/progress and finality origins. -/
def SourceDisciplineAt : Prop :=
  SourceDisciplineBaseAt p c E rho ∧ RStrat p c E rho ∧ RQCOrigin p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.carrier.v1; all runs. -/
def CarrierClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    CarrierAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.chainCertificates.v1 (00:503–514): geometry and certificates.
Consumers: P3:3259–3261, 02 §3.1, 21 H.9(a), 22 I2.
Producer: F1.1 via KitFG geometry lemmas, `height_crossing`,
`justification_certificate`, `finality_certificate`, and `provenance_finality`. -/
def ChainCertificatesAt : Prop := RGeo p c E rho ∧ RCert p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.chainCertificates.v1; all runs. -/
def ChainCertificatesClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    ChainCertificatesAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.store.v2; all runs, with local temporal premises. -/
def StoreClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    StoreAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.activeView.v2; all runs. -/
def ActiveViewClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    ActiveViewAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.leaseOrigins.v2; scheduled runs. -/
def LeaseOriginsClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    V2.D.ScheduleWellFormed E rho → LeaseOriginsAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.reconcile.v2: exact edits, fixed-F idempotence and K1.
The K1 lease premise includes due rows and has no fastWrite premise. -/
def ReconcileAt (st : State p.n) : Prop :=
  FGSA.reconcile st = { st with
    base := { st.base with
      obligations := st.base.obligations.filter (fun row => FGSA.activeCompatible st row.1)
      genuine := st.base.genuine.map
        (fun row => (row.1, row.2.filter (FGSA.activeCompatible st)))
      stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F }
    fastWrite := st.fastWrite.map
      (fun row => (row.1, row.2.filter (FGSA.activeCompatible st))) } ∧
  FGSA.reconcile (FGSA.reconcile st) = FGSA.reconcile st ∧
  (∀ F₀, FGSA.FastOrigin F₀ st → Block.Preceq F₀ (eraseFG st.fg.F) →
    (∀ row ∈ st.base.obligations, Block.Compatible row.1 (eraseFG st.fg.F)) →
    (∀ r C, (r, some C) ∈ st.base.genuine → Block.Compatible C (eraseFG st.fg.F)) →
    Block.Compatible st.base.stableRecord (eraseFG st.fg.F) →
    FGSA.reconcile st = { st with base := { st.base with
      stableRecord := if Block.preceq (eraseFG st.fg.F) st.base.stableRecord then
        st.base.stableRecord else eraseFG st.fg.F } } ∧
    Block.Preceq st.base.stableRecord (FGSA.reconcile st).base.stableRecord)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.reconcile.v2: the store claim at each reachable store. -/
def ReconcileClaim : Prop := ∀ st, Reachable p st → ReconcileAt p st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
comp.outputNesting.v2: the T7.5 NestOK conclusion at every run store. -/
def OutputNestingAt : Prop := ∀ i x, i ≤ rho.events.length → x ∈ rho.honest →
  FGSA.NestOK (storeAt p c E rho i x)

def OutputNestingClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    OutputNestingAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.frame.v1 (00:581–587), 01 §4.3: exact controls, projection and metadata.
Consumers: all frame clients. Producer: F1.1. -/
def FrameAt : Prop := RFrameExactNext p c E rho ∧ RFrameNext p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.frame.v1; all runs. -/
def FrameClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    FrameAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.sourceDiscipline.v2(a,d); no FaultQ premise. -/
def SourceDisciplineBaseClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → SourceDisciplineBaseAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.sourceDiscipline.v1(a–d); BaseSet and FaultQ. -/
def SourceDisciplineClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → SourceDisciplineAt p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Row service with the base premises, the bound on ΔF, and an awake suffix.
DC: INTENTIONAL FG transport adapter; SAME execution and no-restart premises. -/
def RowServiceBaseClaim (ΔF : Time) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    E.Δ = p.Δ → V2.D.ExecutionValid E rho → V2.D.NoRestart rho →
    Gen.V2.Duty.PartialSynchronyBy E rho (fgsaDelay E.Δ ΔF) → E.Δ ≤ ΔF →
    (∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true) →
    TRows p c E rho ΔF


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
RowServiceClaim: chapter-21 service.
DC: INTENTIONAL FG source and action adapter; SAME stated horizon. -/
def RowServiceClaim (ΔF : Time) : Prop :=
  ∀ (G : Time) (_hδ : p.δt = 2 * p.R)
    {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Unit),
    RecoverySleep₂ p c E rho G ΔF → TRows p c E rho ΔF


section

open AvailableChain.SimplexFG Gen.Pure

variable (p : Params)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:78–86;
DC Generic/Claims.lean:56 Consensus.certificatesAccountable; class: INTENTIONAL.
ROOT-DIGEST W1: Keep the conclusion with explicit scoped root premises. -/
def PureAccountableClaim : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    KitFG.RootInjectiveOn K W →
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
      FGBlock.compatible T₁ T₂ = true

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:84–87;
DC certificatesAccountable agreement corollary (L/FinalitySafety.lean:45);
class: INTENTIONAL.
ROOT-DIGEST W1: Keep the conclusion with explicit scoped root premises. -/
def PureAgreementClaim : Prop :=
  ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
    KitFG.RootInjectiveOn K W →
    FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
    ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
      FGBlock.compatible T₁ T₂ = true

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:94–110;
DC Generic/Claims.lean:59,65 Consensus.finalizedAccountable/finalizedSafe;
class: INTENTIONAL.
ROOT-DIGEST W1: Keep the conclusion with explicit scoped root premises. -/
def WholeRunAccountableClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    NamedRootCollisionFree p c E rho → FinalityExecution p c rho → WholeRunAccountable p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:104–112;
DC Generic/Claims.lean:59,65 Consensus.finalizedAccountable/finalizedSafe;
class: INTENTIONAL.
ROOT-DIGEST W1: Keep the conclusion with explicit scoped root premises. -/
def WholeRunAgreementClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    NamedRootCollisionFree p c E rho → FinalityExecution p c rho → FinalitySlashableBound p c E
      rho →
    WholeRunAgreement p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:112;
DC L/FinalitySafety.lean:61 (internal; no direct public field); class: INTENTIONAL.
ROOT-DIGEST W1: Event-prefix observations use stored W finality and scoped roots. -/
def EventPrefixAgreementClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    NamedRootCollisionFree p c E rho → FinalityExecution p c rho → FinalitySlashableBound p c E
      rho →
    ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j,
      FGBlock.compatible (storeAt p c E rho i x).fg.F (storeAt p c E rho j y).fg.F = true

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:123–129;
DC L/FinalitySafety.lean:117 (internal; no direct public field); class: INTENTIONAL.
Linked maps fixed FG seats to holders. Authentic row carriage covers all run blocks;
unit weights give the count bound. The carriage premise is main's action-indexed form
(FinalityRowCarriage, ChannelProps: HonestRowAt at p.actionTime r), stronger in form than d35's
EmitsRow at any tick; the two are equal on valid runs, and main proves this form from
ExecutionValid (fgsa_finalityRowCarriage, Accountable). -/
def FaultCountSlashableBoundClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    V2.D.Linked (fgsaFamilies p c).linked rho →
    (∀ K, FinalityBlock p c E rho K → FinalityRowCarriage p c E rho (chainRows K)) →
    (∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x) →
    (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3 →
    FinalitySlashableBound p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
F-API, dc-align-full.md:131–134; DC G/Claims.lean:61; L/FinalitySafety.lean:103; class:
INTENTIONAL.
FG restore resets F to genesis; NoRestart is required. No fault bound is needed. -/
def FinalizedMonotonicityClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    rho.events.Pairwise (fun a b => a.key ≤ b.key) → V2.D.NoRestart rho →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
G-F0b F-H; DC `Generic/Claims.lean:63` (`honestNeverSlashed`).
`UnforgeableSignatures` is SAME as the signature part of DC `UnforgeableRun`.
`Linked` is INTENTIONAL: FG rows are signed by fixed seat; the holder map
supplies DC's validator identity (F-H, `dc-align-full.md:135–141`).
The conclusion is SAME as DC. No sorted, honest_only, horizon, fault bound,
regime or restart premise is required. INTENTIONAL: validators are fixed to V = Fin p.n,
because fgsaSlashing names validators by their fixed FG seat; the other claims quantify over V. -/
def HonestNeverSlashedClaim (p : Params) : Prop :=
  ∀ {In : Type} (c : AppCodec In) (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (fgsa p c)),
    V2.D.UnforgeableSignatures E rho →
    V2.D.Linked (fgsaFamilies p c).linked rho →
    Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.finalizedSafety.v2 (00:830–840; P3 §4.7).
DC: Generic/Claims.lean:61,65 finalizedMonotone/finalizedSafe.
INTENTIONAL: event-index reads include intermediate states in one time batch. -/
def FinalizedSafetyConcl (p : Params) {V : Type} [DecidableEq V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) : Prop :=
  CompatOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) ∧
  MonoOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
bp.finalizedSafety.v2 (00:830–840; P3 §4.7).
DC: Claims.lean:61,65 Consensus.finalizedMonotone/finalizedSafe.
INTENTIONAL: the FG-SA BaseSet and a ≤ f are the run-level premises;
no recovery, proposer honesty, recurrence, or delay-ratio premise is added. -/
def FinalizedSafetyClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    FinalizedSafetyPrem p c E rho pt →
    FinalizedSafetyConcl p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
fg.finalLock.v3 (00:785–793; P3 App. A.4; adopted carrier read in RXing).
DC: DecoupledConsensusProofs/Protocol/ChainState/FinalityComparison.lean:50
NamedFinalizationBridge.finalized_preceq_of_height_lt.
INTENTIONAL: this is the fault-bounded, held-block channel over each accepted
certificate carrier; RXing retains its certificate h_F, also for genesis.
The accountability alternative is a separate result, not an added premise. -/
def FinalLockClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    FinalizedSafetyPrem p c E rho pt → RXing p c E rho

end

def FinalizedMonotonicityRestartClaim : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    rho.events.Pairwise (fun a b => a.key ≤ b.key) →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x))

end AvailableChain.FGSA.Run
end
