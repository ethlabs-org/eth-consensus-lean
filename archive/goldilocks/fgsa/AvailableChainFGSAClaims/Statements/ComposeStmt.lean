module
public import AvailableChainFGSARun.Statements.AC
public import AvailableChainFGSAClaims.Statements.Healed
public import AvailableChainFGSAClaims.Statements.FrameNext

@[expose] public section

/-! P3 App. A.1/A.10, F0.8a. The generic composition rules stay in Gen:
Gen.Pure.AGRule.holds, Gen.Pure.firstFailure_holds, Gen.Pure.WindowRule.holds
(Proofs/Pure/FirstBad). Gen.Pure.RetroAt and Gen.V2.Duty.Pending supply the
retrospective and deadline predicates. No F2 invariant enters this module. -/

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Study §5.4 (895–903): event indices between consecutive post-gate cuts.
Slot zero starts at index zero. Consumers: F5, H.14–H.17, with Gen.Pure.WindowRule. -/
def windowIdx (s : Slot) (i : Nat) : Prop :=
  (match s with
   | 0 => True
   | s' + 1 => afterTicksIdx rho (SA.gateTime p.toParams s') ≤ i) ∧
  i < afterTicksIdx rho (SA.gateTime p.toParams s)

variable {rho} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.1: study §3.1 (229–260), 01 §8.4 (795–801).
Earlier rows and certificates, bounded labels, atomic reads, and fixed tick FG state. -/
structure TimingContract : Prop where
  rowLag : ∀ j k y r a x, HonestRowAt p c E rho j y r a →
    HandlesRowAt p c E rho k x a → j < k
  certLag : RStrat p c E rho
  label : LabelBound p c E rho
  atomic : ∀ i x, x ∈ rho.honest →
    FGSA.SACompat (storeAt p c E rho i x) ∧ FGSA.NestOK (storeAt p c E rho i x)
  tickFG : ∀ x t nd, preTick E rho x t = some nd →
    ∀ nd', postClock E rho x t = some nd' → nd'.st.fg = nd.st.fg

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3 App. A.10, D09: unconditional FG channels of App. A.2.
Blueprint bp.store.v1, bp.frame.v1, bp.chainCertificates.v1,
bp.sourceDiscipline.v1, and bp.reconcile.v1. -/
structure FGFoundation : Prop where
  store : RStore p c E rho
  cumul : RStoreDurable p c E rho ∧ RStoreEpoch p c E rho
  mono : RMonoAll p c E rho
  frame : RFrameExactNext p c E rho ∧ RFrameNextEpoch p c E rho
  geo : RGeo p c E rho
  strat : RStrat p c E rho
  reconcile : RRec p c E rho


open AvailableChain.SimplexFG
open Gen.Pure

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-START (01 A.7 T-START:222–225,251–267; 22 I5:538–581), P3 A.7.
Consumers: FF1, F6, F8, FL-T7. Both clauses hold at every event index. -/
def TStart : Prop := Gen.AC.Duty.LeaseBelowOutput (fgsaAC E rho) ∧
  ∀ i x, x ∈ rho.honest →
    let st := storeAt p c E rho i x
    FGSA.liveRoot p st = eraseFG (FGSA.controls p st).Z ∨
      ∃ row ∈ st.base.obligations, st.base.now < row.2.2 ∧
        row.1 = FGSA.liveRoot p st ∧
        (∃ B ∈ FGSA.fullTree p st, eraseFG B = row.1) ∧ Block.Preceq row.1 (outputS p st)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Full-batch read (01 A.7 T-VOTE:235–242), P3 A.7. Consumer: TVote.
Admission resolves a held vote; finality coverage is the alternate case. -/
def FullVoteService (st : State p.n) (s : Slot) : Prop :=
  ∀ y (a : HeadWire p.n), y ∈ rho.honest →
    V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s) →
    GridCO.headLabel? (baseVote a) = some s →
    baseVote a ∈ GridCO.votesAt st.base s ∧
    (∀ H, GridCO.resolvedHead? (actView st) (baseVote a) = some H → H.slot ≤ s →
      baseVote a ∈ (GridCO.votesAt st.base s).filter (fun o =>
        match GridCO.resolvedHead? (actView st) o with
        | some h => decide (h.slot ≤ s)
        | none => false))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-VOTE (01 A.7 T-VOTE:235–242), P3 A.7 OD18, D67.
Consumers: FF1, F6, F8, FL-T7. Sync begins at the batch's vote time,
not at the later proposal/action. This is a composition service.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def TVote : Prop :=
  (∀ v st, Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) v →
    E.t_GST ≤ slotStartZ p (((v - 1 : Slot) : Int) - 1) →
    Gen.V2.Duty.LabelSyncOn E rho (fun o => ¬ isRowObject o) (SA.voteTime p.toParams (v - 1))
      (SA.proposalTime p.toParams v) →
    proposalStateAt p c E rho v = some st → FullVoteService p c E rho st (v - 1)) ∧
  (∀ r x nd, x ∈ rho.honest →
    E.t_GST ≤ slotStartZ p (((r * p.R + 1 : Slot) : Int) - 1) →
    Gen.V2.Duty.LabelSyncOn E rho
      (fun o => ¬ isRowObject o) (SA.voteTime p.toParams (r * p.R + 1)) (p.actionTime r) →
    postClock E rho x (p.actionTime r) = some nd →
    FullVoteService p c E rho nd.st (r * p.R + 1)) ∧
  (∀ y s (a : HeadWire p.n), y ∈ rho.honest →
    V2.D.Run.emits E rho y (ofHead p a) (SA.voteTime p.toParams s) →
    ∃ nd H, postClock E rho y (SA.voteTime p.toParams s) = some nd ∧
      H ∈ nd.st.base.blocks ∧ H.root = a.payload)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Honest resolving seats of a read (01 A.7 T-WALK:243–249,269–278), P3 A.7.
Consumer: TWalk. The other seats have total size at most m. -/
def WalkBatch (st : State p.n) (s : Slot) (raw support : List (GridCO.Wire p.n .root))
    (Q : Block) (seats : Finset (Fin p.n)) (m : Nat) : Prop :=
  support ⊆ raw ∧ (∀ o ∈ raw, GridCO.headLabel? o = some s) ∧
  (∀ a ∈ seats, rho.seatOf (.base (.head s)) a ∈ rho.honest ∧
    ∃ o ∈ support, o ∈ raw ∧ GridCO.headSeat? o = some a ∧
      ∃ H, GridCO.resolvedHead? st.base o = some H ∧ H.slot ≤ s ∧ Block.Preceq Q H) ∧
  ((GridCO.seats p.n raw).toFinset \ seats).card ≤ m ∧
  (∀ a ∈ seats, GridCO.equivocates raw a = false)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-WALK (01 A.7 T-WALK:243–249,269–278; 22 I8:637), P3 A.7.
Consumers: FF1, F6, F8, FF3–FF4, FL-*. Batch h m is the local count premise. -/
def TWalk : Prop := ∀ i x s raw support Q seats m,
  x ∈ rho.honest → Batch seats.card m →
  let st := storeAt p c E rho i x
  Q ∈ FGSA.fullTree p st → Block.Compatible (FGSA.liveRoot p st) (eraseFG Q) →
  WalkBatch p c rho st s raw support (eraseFG Q) seats m →
  Block.Preceq (eraseFG Q) (FGSA.getHead p st raw support) ∧
  ((∀ B ∈ FGSA.fullTree p st, FGBlock.Preceq Q B → B = Q) →
    FGSA.getHead p st raw support = eraseFG Q) ∧
  (∀ B, Block.Prec (FGSA.liveRoot p st) B → Block.Preceq B (FGSA.getHead p st raw support) →
    (∀ a ∈ seats, ∀ o ∈ support, GridCO.headSeat? o = some a →
      ∀ H, GridCO.resolvedHead? st.base o = some H → ¬ Block.Preceq B H) →
    B.slot = st.slot p ∨ ∃ A ∈ st.fg.TF,
      eraseFG A = B.parent ∧ (heightView p A).h < (FGSA.controls p st).lo)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The three composition services (01 §1.2), P3 A.7/A.10 D10.
Consumer: kernel. H3 and H4 remain projections of HealAC, not fields here. -/
structure CoreServices (_w : HealingWitness) : Prop where
  start : TStart p c E rho
  vote : TVote p c E rho
  walk : TWalk p c E rho

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Retained phase kinds (21 H.10:1263–1279), P3 A.10. Consumer: AttemptKey. -/
inductive PhaseKind | gap | topJ | contest
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Tasks in the per-phase budget table (21:1270–1279), P3 A.10. -/
inductive AttemptTask | raise | firstRow
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Attempt identity (21 H.10:1263–1279; HG.1–HG.5), P3 A.10.
Consumer: progress-attempt contract. A phase event ends the attempt. -/
structure AttemptKey where
  start : Nat
  frontier : Nat
  phase : PhaseKind
  task : AttemptTask
  served : Bool

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Reset arrival, exactly H.11 (21:1572–1595), P3 A.10 with lead ruling
2026-09-30. Consumers: H.12–H.17. The reset bound uses the common ΔF.
DC: INTENTIONAL row-delay bound; H0Reset and SA clocks stay unchanged.
A consumer of Q* must use ResetArrivalFullStatement. -/
def ResetArrivalStatement (G ΔF : Time) : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B'_resetF p ΔF G ≤ rho.horizon →
    ∃ w, H0Reset p c E rho w ∧ p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G

theorem ResetArrivalStatement_def (G ΔF : Time) :
    ResetArrivalStatement p G ΔF =
  (p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B'_resetF p ΔF G ≤ rho.horizon →
    ∃ w, H0Reset p c E rho w ∧
      p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Full companion: H.11 reset plus H.18 (21:2868–2876;3174–3176),
P3 A.10 with lead ruling 2026-09-30. Consumers: full H0, HealingInput,
tstarOf and joined kernel. Only the horizon adds Γ + 4Δ; reset time does not.
DC: INTENTIONAL row-delay bound; the block and gate tail stays Δ-based. -/
def ResetArrivalFullStatement (G ΔF : Time) : Prop := p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
    ∃ w, H0 p c E rho w ∧ p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G

theorem ResetArrivalFullStatement_def (G ΔF : Time) :
    ResetArrivalFullStatement p G ΔF =
  (p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
    ∃ w, H0 p c E rho w ∧ p.actionTime w.rStar < recoveryStart p E + B'_resetF p ΔF G) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Kernel point (00:1119–1134; 22 §1), P3 A.10 D12.
Consumers: FinalityKernelClaim_W and KernelPrem_W. -/
structure KernelPt where
  w : HealingWitness
  r : Nat
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Joined kernel start (21 H.18:2868–2876), P3 A.10 D44.
No consumer. This historical observation does not supply HealingInput.
KernelJoinedPrem binds the common input witness and its start time directly. -/
def kernelStart (r : Nat) : Prop := ∃ t, tstarOf p c E rho = some t ∧ t ≤ ↑r * P p


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 22:1171–1180. DC: INTENTIONAL actual opening carrier.
The emitted wire, proposer read, parent and decoded rows identify one FG block. -/
def OpeningCarrier_W (s : Slot) (A : Block) (Afg : FGBlock (Fin p.n)) : Prop :=
  ∃ o N st P,
    V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
      (V2.D.proposalTime (fgsaInterface p c) s) ∧
    N.erase = A ∧ (toWire p o).decode = some (.block s N) ∧
    proposalStateAt p c E rho s = some st ∧ FGSA.parentFG st A = some P ∧
    FGSA.fgBlock P A N.rows = Afg

theorem OpeningCarrier_W_def (s : Slot) (A : Block) (Afg : FGBlock (Fin p.n)) :
    OpeningCarrier_W p c E rho s A Afg =
  (∃ o N st P,
    V2.D.Run.emits E rho (V2.D.proposerOf rho (fgsaInterface p c) s) o
      (V2.D.proposalTime (fgsaInterface p c) s) ∧
    N.erase = A ∧ (toWire p o).decode = some (.block s N) ∧
    proposalStateAt p c E rho s = some st ∧ FGSA.parentFG st A = some P ∧
    FGSA.fgBlock P A N.rows = Afg) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 22:1171–1180, F1–F9. DC: INTENTIONAL W coverage and strict receipt.
The opening carrier is concluded and is held by all honest nodes. -/
def KernelConclusion_W (ΔF : Time) (r : Nat) : Prop := ∀ A,
  HonestProposal E rho (fgsaInterface p c) (r * p.R) A →
  ∃ Afg : FGBlock (Fin p.n), eraseFG Afg = A ∧
    OpeningCarrier_W p c E rho (r * p.R) A Afg ∧
    (∀ x ∈ rho.honest, Afg ∈ (storeAt p c E rho rho.events.length x).fg.TF) ∧
    ∃ U : FGBlock (Fin p.n), FGBlock.Preceq Afg U ∧ Afg ≠ U ∧
      (heightView p U).h = (heightView p Afg).h + 1 ∧
      ∀ x ∈ rho.honest,
        AcceptsFinalBefore p c E rho x U (kernelDeadlineW p ΔF (r + 2))

theorem KernelConclusion_W_def (ΔF : Time) (r : Nat) :
    KernelConclusion_W p c E rho ΔF r =
  (∀ A,
  HonestProposal E rho (fgsaInterface p c) (r * p.R) A →
  ∃ Afg : FGBlock (Fin p.n), eraseFG Afg = A ∧
    OpeningCarrier_W p c E rho (r * p.R) A Afg ∧
    (∀ x ∈ rho.honest, Afg ∈ (storeAt p c E rho rho.events.length x).fg.TF) ∧
    ∃ U : FGBlock (Fin p.n), FGBlock.Preceq Afg U ∧ Afg ≠ U ∧
      (heightView p U).h = (heightView p Afg).h + 1 ∧
      ∀ x ∈ rho.honest,
        AcceptsFinalBefore p c E rho x U (kernelDeadlineW p ΔF (r + 2))) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 22:1173, plan item 18. DC: INTENTIONAL split W kernel.
The same witness supplies input, services and start. Params supplies K_W ≥ 2.
The explicit FGoodE_W carrier replaces the internal kernelPat interface. -/
structure KernelPrem_W [Fintype V] (G ΔF : Time) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : KernelPt) : Prop where
  set : Recovery₂ p c E rho G ΔF
  bound : LivenessBoundW p ΔF
  window : FGoodE_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    p.R (kappaF p ΔF) pt.r
  start : tstar p pt.w ≤ ↑pt.r * P p
  hhor : kernelDeadlineW p ΔF (pt.r + 2) ≤ rho.horizon
  input : HealingInput p c E rho pt.w ΔF
  services : CoreServices p c E rho pt.w

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 22:1985–2009. DC: INTENTIONAL local Tail witness.
This is a retained local kernel. It has no QF recurrence package. -/
structure TailKernelPt (p : Params) where
  w : HealingWitness
  r : Nat
  carrier : Slot
  U : FGBlock (Fin p.n)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Blueprint 22:1985–2009, 22:1811; ruling m6. DC: INTENTIONAL local Tail contract.
Recovery₂ is the standing kernel regime.
The opening height ≥ M+1 follows from HealingInput; it is not a premise.
Params supplies capacity ≥ 2. Coverage starts at the selected honest carrier. -/
structure TailKernelPrem_W [Fintype V] (G ΔF : Time) (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (pt : TailKernelPt p) : Prop where
  set : Recovery₂ p c E rho G ΔF
  bound : LivenessBoundW p ΔF
  input : HealingInput p c E rho pt.w ΔF
  start : tstar p pt.w ≤ ↑pt.r * P p
  window : Tail_W (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    p.R (kappaF p ΔF) pt.r
  carrier : pt.r * p.R + kappaF p ΔF ≤ pt.carrier ∧
    pt.carrier ≤ (pt.r + 1) * p.R ∧
    Gen.V2.Duty.HonestSlot rho (fgsaInterface p c) pt.carrier
  high : high p pt.w pt.U
  cover : ∀ s X, pt.carrier ≤ s →
    HonestProposal E rho (fgsaInterface p c) s (eraseFG X) →
    OpeningCarrier_W p c E rho s (eraseFG X) X →
    FGBlock.Preceq pt.U (heightView p X).J ∨
      FGBlock.Preceq pt.U (finalityView p X).F
  hhor : kernelDeadlineW p ΔF (pt.r + 1) ≤ rho.horizon

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
T-side healing contract (21 H.3–H.18), P3 A.10.
Consumer: F5 composition. Only reset delivery has an H0 premise.
JOINED-START: delivery and phase services start at recoveryStart. -/
structure HealTContract (w : HealingWitness) : Prop where
  del : TDel p c E rho
  delReset : TDelReset p c E rho w
  perm : TPerm p c E rho
  repair : TRepair p c E rho
  common : TCommon p c E rho
  frontier : TFrontier p c E rho
  geom : TGeom p c E rho


/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Global frontier at an event prefix (21 H.7:918–1012), P3 A.10.
Consumers: effective events and attempts. -/
def frontierAtIdx (i : Nat) : Nat := rho.honest.sup (fun x => (storeAt p c E rho i x).fg.h_max)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Accepted top-J evidence at the frontier (21 H.7:918–1012), P3 A.10.
Consumers: phase classification and effective events. -/
def TopEvidence (i m : Nat) : Prop := ∃ x, x ∈ rho.honest ∧
  (storeAt p c E rho i x).fg.h_j + 1 = m
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Accepted contest evidence at the frontier (21 H.7:918–1012), P3 A.10.
Consumers: phase classification and effective events. -/
def ContestEvidence (i m : Nat) : Prop := ∃ x, x ∈ rho.honest ∧
  (R_at p c E rho i x).H = m ∧ (R_at p c E rho i x).contest = true
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Effective event (21 H.7:1003–1012; H.10:1263–1265), P3 A.4/A.10.
Consumers: attempts. A lower F move is not an effective event. -/
def EffectiveEvent (i : Nat) : Prop :=
  frontierAtIdx p c E rho i < frontierAtIdx p c E rho (i + 1) ∨
  (let m := frontierAtIdx p c E rho (i + 1)
   (¬ TopEvidence p c E rho i m ∧ TopEvidence p c E rho (i + 1) m) ∨
   (¬ ContestEvidence p c E rho i m ∧ ContestEvidence p c E rho (i + 1) m))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Phase selected by global accepted evidence (21 H.7:1003–1012), P3 A.10.
Consumer: AttemptValid. -/
def AttemptPhaseAt (i m : Nat) (kind : PhaseKind) : Prop :=
  match kind with
  | .gap => ¬ TopEvidence p c E rho i m ∧ ¬ ContestEvidence p c E rho i m
  | .topJ => TopEvidence p c E rho i m ∧ ¬ ContestEvidence p c E rho i m
  | .contest => ContestEvidence p c E rho i m
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
A served frontier proposal by a given time (21 HG.1:1333–1350), P3 A.10.
Consumer: the served flag of AttemptValid. -/
def ServedFrontier (m : Nat) (t : Time) : Prop := ∃ s Q Qfg,
  HonestProposal E rho (fgsaInterface p c) s Q ∧ eraseFG Qfg = Q ∧
  (heightView p Qfg).h = m ∧ SA.gateTime p.toParams s ≤ t ∧ ExactService p c E rho s Q
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Attempt validity (21 H.10:1263–1279; H.11:1572–1595; HG.1:1333–1350),
P3 A.10 D44. Consumers: progress-attempt contract and HealingAttemptPrem.
start is the event index; its resulting prefix is start+1. The inclusive-cut
alternative requires that exact resulting prefix. No budget horizon is hidden here.
The frontier may be 1: H.10 runs attempts at m = 1 (21:1467–1468, 2570–2571; ruling B21). -/
def AttemptValid (k : AttemptKey) : Prop := ∃ ev,
  rho.events[k.start]? = some ev ∧ recoveryStart p E ≤ ev.time ∧
  (EffectiveEvent p c E rho k.start ∨
    ∃ rG, recoveryStart p E ≤ p.actionTime rG ∧
      (∀ r, recoveryStart p E ≤ p.actionTime r → rG ≤ r) ∧
      ev.time = p.actionTime (rG + 2) ∧
      timeIdx rho (p.actionTime (rG + 2)) = k.start + 1) ∧
  k.frontier = frontierAtIdx p c E rho (k.start + 1) ∧ 1 ≤ k.frontier ∧
  AttemptPhaseAt p c E rho (k.start + 1) k.frontier k.phase ∧
  (k.served = true ↔ ServedFrontier p c E rho k.frontier ev.time) ∧
  (k.task = .firstRow → ∀ j y r a h e, j ≤ k.start → HonestRowAt p c E rho j y r a →
    namedEntry a.payload.height_pair = some (h, e) → h ≠ k.frontier)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Retained H.10 budget table (21:1270–1279), P3 A.10.
Consumer: progress-attempt contract. This uses the unconditional two-lease bound;
HG improvements can be separate bounds for attempts with served=true. -/
def attemptBudget (G : Time) (k : AttemptKey) : Time :=
  match k.task, k.phase with
  | .raise, .contest => ρΓ p G + 3 * P p + Γ p G - 10 * p.Δ
  | .raise, _ => ρΓ p G + 6 * P p + 2 * Γ p G - 18 * p.Δ
  | .firstRow, .contest => ρΓ p G + P p - p.Δ
  | .firstRow, _ => ρΓ p G + 4 * P p + Γ p G - 9 * p.Δ
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Event or completed task within a duration (21 H.10:1263–1279), P3 A.10.
Consumer: progress-attempt contract. Service never continues through an earlier event. -/
def AttemptEndsBy (k : AttemptKey) (budget : Time) : Prop := ∃ ev,
  rho.events[k.start]? = some ev ∧
  ∃ j ev', k.start < j ∧ rho.events[j]? = some ev' ∧ ev'.time ≤ ev.time + budget ∧
    (EffectiveEvent p c E rho j ∨
      (k.task = .raise ∧ k.frontier < frontierAtIdx p c E rho (j + 1)) ∨
      (k.task = .firstRow ∧ ∃ y r a e, HonestRowAt p c E rho j y r a ∧
        namedEntry a.payload.height_pair = some (k.frontier, e)))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Settled-frame alternatives (21 H.7:1012–1045; P3 A.4:7495–7500).
DC: SeedCommonRootComplement.lean:36,48 and FixedHeightRootCore.lean:162
(partial). INTENTIONAL: FG-SA adds the contest case and its floor m.
The lead ruling (dc-align-j2:172–178) requires an accepted certificate K;
FG certificate height is not a function of the finalized block. The existential
supplies one usable K; RXing applies to every qualifying K. Consumers pass K
and its height to RXing. This is stronger than the PhaseInterval read predicate. -/
def SettledPhaseFrame (st : State p.n) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) : Prop :=
  let R := FGSA.controls p st
  R.H = m ∧ R.contest = contested ∧ R.lo = (if contested then m else m - 1) ∧
  (match J with
   | some B => R.rootIsJ = true ∧ R.J = B ∧ R.Z = B ∧
       R.j + 1 = m ∧ contested = false ∧ FGBlock.Preceq st.fg.F B
   | none => R.rootIsJ = false ∧ R.Z = st.fg.F ∧
       (∃ K ∈ st.fg.TF, (finalityView p K).F = st.fg.F ∧
         (finalityView p K).h_F < R.lo) ∧
       ((contested = false ∧ R.j + 2 ≤ m) ∨
         (contested = true ∧ R.j + 1 = m))) ∧
  (∃ W ∈ st.fg.TF, (heightView p W).h = m ∧ FGBlock.Preceq R.Z W)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Definitional equation for `SettledPhaseFrame`.
Settled-frame alternatives (21 H.7:1012–1045; P3 A.4:7495–7500).
DC: SeedCommonRootComplement.lean:36,48 and FixedHeightRootCore.lean:162
(partial). INTENTIONAL: FG-SA adds the contest case and its floor m.
The lead ruling (dc-align-j2:172–178) requires an accepted certificate K;
FG certificate height is not a function of the finalized block. The existential
supplies one usable K; RXing applies to every qualifying K. Consumers pass K
and its height to RXing. This is stronger than the PhaseInterval read predicate. -/
theorem SettledPhaseFrame_def (st : State p.n) (m : Nat)
    (J : Option (FGBlock (Fin p.n))) (contested : Bool) :
    SettledPhaseFrame p st m J contested =
  (  let R := FGSA.controls p st
  R.H = m ∧ R.contest = contested ∧ R.lo = (if contested then m else m - 1) ∧
  (match J with
   | some B => R.rootIsJ = true ∧ R.J = B ∧ R.Z = B ∧
       R.j + 1 = m ∧ contested = false ∧ FGBlock.Preceq st.fg.F B
   | none => R.rootIsJ = false ∧ R.Z = st.fg.F ∧
       (∃ K ∈ st.fg.TF, (finalityView p K).F = st.fg.F ∧
         (finalityView p K).h_F < R.lo) ∧
       ((contested = false ∧ R.j + 2 ≤ m) ∨
         (contested = true ∧ R.j + 1 = m))) ∧
  (∃ W ∈ st.fg.TF, (heightView p W).h = m ∧ FGBlock.Preceq R.Z W)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Pre-reset phase contract (21 H.3:581–618, H.7–H.8:918–1045,
HG.1:1358–1363; 00:938–948,980–985; P3 A.4:7487–7511).
DC: SeedCommonRootComplement.lean:36,48; SeedBoundaryConeLead.lean:82;
FixedHeightRootCore.lean:162 (partial). INTENTIONAL: FG-SA has gap, top J,
and contest phases, with live controls and a frozen HEAD witness view.
The five clauses give phase order, evidence spread and HEAD inclusion,
settlement after an effective event, the additional settled-frame contract,
and frontier membership only for B and its path in the supplied view X. Strict receipt
uses event prefixes whose events all precede the deadline. A frontier rise
ends the evidence task. Lower F moves do not change the two evidence bits.
The settled clause is an extra contract, not a consequence of PhaseInterval
alone. Its accepted K is passed to RXing (dc-align-j2:172–178).
Claim form: HealingSet with a ≤ f; no reset witness. No QualSearch is used.
Frontier m ≥ 1: at m = 1 the frame is top J with J = genesis (21:286, 1236; H.10 at m = 1,
21:1467–1468, 2570–2571; ruling B21). The gap frame keeps R.j + 2 ≤ m (21:1191–1203). -/
def RPhase : Prop :=
  (∀ a b m, a ≤ b → b ≤ rho.events.length → 1 ≤ m →
    (∀ i, a ≤ i → i ≤ b → frontierAtIdx p c E rho i = m) →
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence p c E rho i m → TopEvidence p c E rho j m) ∧
      (ContestEvidence p c E rho i m → ContestEvidence p c E rho j m)) ∧
    (∀ i, a ≤ i → i ≤ b →
      ContestEvidence p c E rho i m → TopEvidence p c E rho i m)) ∧
  (∀ i ev x W m, rho.events[i]? = some ev → x ∈ rho.honest →
    recoveryStart p E ≤ ev.time → 1 ≤ m → frontierAtIdx p c E rho (i + 1) = m →
    W ∉ (storeAt p c E rho i x).fg.TF →
    W ∈ (storeAt p c E rho (i + 1) x).fg.TF → (heightView p W).h = m →
    (ev.time + p.Δ ≤ rho.horizon → ∀ y ∈ rho.honest,
      ∃ j, i < j ∧ j ≤ rho.events.length ∧
        (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + p.Δ) ∧
        (W ∈ (storeAt p c E rho j y).fg.TF ∨ m < frontierAtIdx p c E rho j)) ∧
    (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
      SA.voteTime p.toParams s ≤ rho.horizon →
      postClock E rho y (SA.voteTime p.toParams s) = some nd →
      (∃ j, i < j ∧ j ≤ timeIdx rho (SA.voteTime p.toParams s) ∧
        m < frontierAtIdx p c E rho j) ∨ W ∈ FGSA.voterBlocks p nd.st s)) ∧
  (∀ i ev v m kind, rho.events[i]? = some ev → EffectiveEvent p c E rho i →
    recoveryStart p E ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
    frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
    (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
    ∃ J,
      let root := match kind with | .topJ => some J | _ => none
      let contested := match kind with | .contest => true | _ => false
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st m root contested)) ∧
  (∀ u v m J contested, recoveryStart p E ≤ u → PhaseInterval p c E rho u v m J contested →
    ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      SettledPhaseFrame p (storeAt p c E rho i x) m J contested) ∧
  (∀ i x m (X : Finset (FGBlock (Fin p.n))) B, x ∈ rho.honest →
    i ≤ rho.events.length → 1 ≤ m → (R_at p c E rho i x).H = m →
    X ⊆ (storeAt p c E rho i x).fg.TF → B ∈ X →
    (∀ A, FGBlock.Preceq A B → A ∈ X) → (heightView p B).h = m →
    FGBlock.Preceq (R_at p c E rho i x).Z B ∧ B ∈ D_at p c E rho i x X)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Definitional equation for `RPhase`.
Pre-reset phase contract (21 H.3:581–618, H.7–H.8:918–1045,
HG.1:1358–1363; 00:938–948,980–985; P3 A.4:7487–7511).
DC: SeedCommonRootComplement.lean:36,48; SeedBoundaryConeLead.lean:82;
FixedHeightRootCore.lean:162 (partial). INTENTIONAL: FG-SA has gap, top J,
and contest phases, with live controls and a frozen HEAD witness view.
The five clauses give phase order, evidence spread and HEAD inclusion,
settlement after an effective event, the additional settled-frame contract,
and frontier membership only for B and its path in the supplied view X. Strict receipt
uses event prefixes whose events all precede the deadline. A frontier rise
ends the evidence task. Lower F moves do not change the two evidence bits.
The settled clause is an extra contract, not a consequence of PhaseInterval
alone. Its accepted K is passed to RXing (dc-align-j2:172–178).
Claim form: HealingSet with a ≤ f; no reset witness. No QualSearch is used. -/
theorem RPhase_def :
    RPhase p c E rho =
  (  (∀ a b m, a ≤ b → b ≤ rho.events.length → 1 ≤ m →
    (∀ i, a ≤ i → i ≤ b → frontierAtIdx p c E rho i = m) →
    (∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (TopEvidence p c E rho i m → TopEvidence p c E rho j m) ∧
      (ContestEvidence p c E rho i m → ContestEvidence p c E rho j m)) ∧
    (∀ i, a ≤ i → i ≤ b →
      ContestEvidence p c E rho i m → TopEvidence p c E rho i m)) ∧
  (∀ i ev x W m, rho.events[i]? = some ev → x ∈ rho.honest →
    recoveryStart p E ≤ ev.time → 1 ≤ m → frontierAtIdx p c E rho (i + 1) = m →
    W ∉ (storeAt p c E rho i x).fg.TF →
    W ∈ (storeAt p c E rho (i + 1) x).fg.TF → (heightView p W).h = m →
    (ev.time + p.Δ ≤ rho.horizon → ∀ y ∈ rho.honest,
      ∃ j, i < j ∧ j ≤ rho.events.length ∧
        (∀ l e, l < j → rho.events[l]? = some e → e.time < ev.time + p.Δ) ∧
        (W ∈ (storeAt p c E rho j y).fg.TF ∨ m < frontierAtIdx p c E rho j)) ∧
    (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
      SA.voteTime p.toParams s ≤ rho.horizon →
      postClock E rho y (SA.voteTime p.toParams s) = some nd →
      (∃ j, i < j ∧ j ≤ timeIdx rho (SA.voteTime p.toParams s) ∧
        m < frontierAtIdx p c E rho j) ∨ W ∈ FGSA.voterBlocks p nd.st s)) ∧
  (∀ i ev v m kind, rho.events[i]? = some ev → EffectiveEvent p c E rho i →
    recoveryStart p E ≤ ev.time → ev.time + 3 * p.Δ ≤ v → v ≤ rho.horizon → 1 ≤ m →
    frontierAtIdx p c E rho (i + 1) = m → AttemptPhaseAt p c E rho (i + 1) m kind →
    (∀ j, i < j → j < timeIdx rho v → ¬ EffectiveEvent p c E rho j) →
    ∃ J,
      let root := match kind with | .topJ => some J | _ => none
      let contested := match kind with | .contest => true | _ => false
      PhaseInterval p c E rho (ev.time + 3 * p.Δ) v m root contested ∧
      (∀ y s nd, y ∈ rho.honest → ev.time + 3 * p.Δ ≤ SA.voteTime p.toParams s →
        SA.voteTime p.toParams s ≤ v →
        postClock E rho y (SA.voteTime p.toParams s) = some nd →
        SettledPhaseFrame p nd.st m root contested)) ∧
  (∀ u v m J contested, recoveryStart p E ≤ u → PhaseInterval p c E rho u v m J contested →
    ∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho v → x ∈ rho.honest →
      SettledPhaseFrame p (storeAt p c E rho i x) m J contested) ∧
  (∀ i x m (X : Finset (FGBlock (Fin p.n))) B, x ∈ rho.honest →
    i ≤ rho.events.length → 1 ≤ m → (R_at p c E rho i x).H = m →
    X ⊆ (storeAt p c E rho i x).fg.TF → B ∈ X →
    (∀ A, FGBlock.Preceq A B → A ∈ X) → (heightView p B).h = m →
    FGBlock.Preceq (R_at p c E rho i x).Z B ∧ B ∈ D_at p c E rho i x X)) := by rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: INTENTIONAL FG healing source adapters; action provenance stays explicit. -/
structure HealRContract (w : HealingWitness) : Prop where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:7996; DC FixedHeightRootAdmission:289–310. INTENTIONAL: held carriers
  supply the certificate height; the phase supplies one such carrier. -/
  xing : RXing p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:7997; DC FinalityCertificates:266 (partial). INTENTIONAL: the FG-SA
  contract retains causal honest-row carriage in the held block. -/
  cap : RCap p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:7998; DC SeedCommonRootComplement:36,48 (partial). INTENTIONAL:
  the three FG-SA phases are pre-reset facts and have no witness parameter. -/
  phase : RPhase p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:7999; DC FixedHeightRootCore:396 (partial). INTENTIONAL: FG-SA
  descent uses the supplied view and earlier source causes. -/
  excl : RExcl p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:8000; DC HeightRegimeFrame.lean:120 (partial). INTENTIONAL: FG-SA retention
  is tied to the reset witness and full or HEAD view. -/
  keep : RKeep p c E rho w
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
P3:8001; DC Main:173 StoreFinalizationOnChain (partial). INTENTIONAL:
  FG-SA adds post-reset source provenance and event order. -/
  fprov : RFProv p c E rho w

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: INTENTIONAL explicit row-delay regime with its κ bound.
The H.10 budget and its horizon after the actual start event stay unchanged. -/
def ProgressAttemptStatement (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF → ∀ k ev, AttemptValid p c E rho k →
    rho.events[k.start]? = some ev → ev.time + attemptBudget p G k ≤ rho.horizon →
    AttemptEndsBy p c E rho k (attemptBudget p G k)

theorem ProgressAttemptStatement_def (G ΔF : Time) :
    ProgressAttemptStatement p G ΔF =
  (p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF → ∀ k ev, AttemptValid p c E rho k →
    rho.events[k.start]? = some ev → ev.time + attemptBudget p G k ≤ rho.horizon →
    AttemptEndsBy p c E rho k (attemptBudget p G k)) := by rfl

end AvailableChain.FGSA.Run
end
