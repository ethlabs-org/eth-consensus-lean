module
public import AvailableChainFGCompose.Statements.Finality
public import AvailableChainFGCompose.Statements.Promotion
public import AvailableChainKitFG.WindowEntriesDef
public import AvailableChainFGCompose.Statements.FinalityRecords -- shake: keep (d7a2 seed leaves)

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

/-- Exact decoded content and signer. -/
def RowNames (k : RowKind) (row : Row (Fin n)) (i : Fin n)
    (y : Nat) (U : FGBlock (Fin n)) : Prop :=
  row.signer = i ∧ match k with
  | .target => row.height_pair = .vote y U.root false
  | .progress => ∃ timeout, row.height_pair = .vote y U.root timeout

/-- Every non-genesis edge on the path increases the slot. -/
def SlotChain (X : FGBlock (Fin n)) : Prop :=
  ∀ W, FGBlock.Preceq W X → W ≠ .genesis → W.parent.slot < W.slot

/-- The semantic exact reads at the same service point and horizon. -/
def KernelExactService (A : FGACServiceReads V) (horizon : Time)
    (v : Slot) (Q : Block) : Prop :=
  (A.voteTime v ≤ horizon → ∀ x, A.honest x → A.headScope x v →
    A.headAtLabel x v = some Q) ∧
  (A.gateTime v ≤ horizon → ∀ x, A.honest x → A.gateScope x v →
    A.gate x v = some (some Q) ∧
      ∀ r, v = A.gateLabel r → A.source x r = some (some Q))

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)

/-- A carrier names its actual decoded body and its full wire-row list. -/
def kernelCarrier (o : P.Object) (s : Slot) (Q : Block) (rows : List Wire) : Prop :=
  ∃ N, decodeProposal o = some (s, N) ∧ bodyErase N = Q ∧ bodyRows N = rows
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)

/-- The full signed batch, with actual receipt, carrier, and parent reads. -/
structure BatchPrem (ΔF : Time) (k : RowKind) (q y : Nat)
    (U X : FGBlock (Fin n)) : Prop where
  schedule : V2.D.ScheduleWellFormed E rho
  fault_weight : Ef.weightOf (historyFaulty S rho) < Ef.q
  deltaF : E.Δ ≤ ΔF
  rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF
  horizon : max (T.action q) E.t_GST + ΔF ≤ T.proposal X.slot ∧
    T.proposal X.slot ≤ rho.horizon
  carrier : ∃ rows, HonestCarrier E rho I (kernelCarrier decodeProposal bodyErase bodyRows)
      X.slot (R.erase X) rows ∧
    X.rows = rows.filterMap S.decode
  after : q * T.roundSlots + 2 ≤ X.slot
  valid : ∃ Q : Finset (Fin n),
    (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧
    Ef.q ≤ Ef.weightOf Q ∧ ∀ i ∈ Q, ∃ j r a t,
      r ≤ q ∧ HonestRowAt S E rho T j (safetyHolder S rho i) r a ∧
      D.signer a = some i ∧ NamesEntry (pair := D.heightPair) k a y U ∧
      eventTime rho j = some t ∧ t = T.action r ∧
      ValidForParent E rho I parentFG validFor X.slot (R.erase X) a ∧
      HeightMatch E rho I (fun a => namedEntry (D.heightPair a))
        parentFG parentHeight X.slot (R.erase X) a
  entry : EntryAt O.height U y
  path : FGBlock.Preceq U X.parent
  above : ∀ i, safetyHolder S rho i ∈ rho.honest →
    ∀ W, FGBlock.Preceq W X.parent →
      (∃ row ∈ W.rows, RowNames k row i y U) → FGBlock.Preceq U W.parent

variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)

/-- One selected opening, middle, and early carrier, with all history cuts. -/
structure KernelMiddleWitness_W (cfg : FGConfig) (K : Nat)
    (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt) (A : Block) where
  A₀ : FGBlock (Fin n)
  B : FGBlock (Fin n)
  U : FGBlock (Fin n)
  X_D : FGBlock (Fin n)
  cD : Slot
  d : Nat

  opening : HonestProposal E rho I (pt.r * T.roundSlots) A
  eraseA : R.erase A₀ = A
  carrierA : OpeningCarrier_W decodeProposal bodyErase bodyRows
    (fun nd Q => parentFG nd Q.parent) makeFG E rho I (pt.r * T.roundSlots) A A₀
  carrierB : OpeningCarrier_W decodeProposal bodyErase bodyRows
    (fun nd Q => parentFG nd Q.parent) makeFG E rho I ((pt.r + 1) * T.roundSlots) (R.erase B) B
  carrierD : OpeningCarrier_W decodeProposal bodyErase bodyRows
    (fun nd Q => parentFG nd Q.parent) makeFG E rho I cD (R.erase X_D) X_D
  honestB : HonestProposal E rho I ((pt.r + 1) * T.roundSlots) (R.erase B)
  honestD : HonestProposal E rho I cD (R.erase X_D)
  slotA : A₀.slot = pt.r * T.roundSlots
  slotB : B.slot = (pt.r + 1) * T.roundSlots
  slotD : X_D.slot = cD
  earlySlot : (pt.r + 1) * T.roundSlots + kappaF T ΔF ≤ cD ∧ cD ≤ (pt.r + 2) * T.roundSlots

  heightA : (O.height A₀).h = d
  highA : sp.reset.M + 1 ≤ d
  heightB : (O.height B).h = d + 1
  entryB : (O.height B).T_h = U
  freshEntry : EntryAt O.height U (d + 1)
  strictAU : FGBlock.Preceq A₀ U ∧ A₀ ≠ U
  pathUB : FGBlock.Preceq U B
  freshSlot : pt.r * T.roundSlots < U.slot ∧ U.slot ≤ (pt.r + 1) * T.roundSlots
  parentAB : FGBlock.Preceq A₀ B.parent
  parentBD : FGBlock.Preceq B X_D.parent

  sourceA : ∀ x ∈ rho.honest,
    actionSourceFG R E rho T x pt.r = some (some A₀)
  sourceB : ∀ x ∈ rho.honest,
    actionSourceFG R E rho T x (pt.r + 1) = some (some B)
  serviceD : KernelExactService ac rho.horizon cD (R.erase X_D)

  heightD : (O.height X_D).h = d + 2
  justifiedD : (O.height X_D).J = U
  justifiedHeightD : (O.height X_D).h_j = d + 1
  pendingD : (SimplexFG.Window.derive Ef cfg K X_D).h_F < d + 1
  retainedD : KitFG.Window.RetainedW Ef cfg K X_D (d + 1) U

  noFirstHeight : ∀ j x q a h t,
    HonestRowAt S E rho T j x q a → historyRowHeight S D a = some h →
    d + 1 ≤ h → eventTime rho j = some t →
    T.action (pt.r + 1) ≤ t
  noSecondHeight : ∀ j x q a h t,
    HonestRowAt S E rho T j x q a → historyRowHeight S D a = some h →
    d + 2 ≤ h → eventTime rho j = some t →
    T.action (pt.r + 2) ≤ t
  noEarlyFinality : ∀ j x q a h t,
    HonestRowAt S E rho T j x q a → historyFinHeight S D a = some h →
    d + 1 ≤ h → eventTime rho j = some t →
    T.action (pt.r + 2) ≤ t

  chainA : ChainRowsBefore R E rho A₀ (T.action pt.r)
  chainB : ChainRowsBefore R E rho B (T.action (pt.r + 1))
  chainD : ChainRowsBefore R E rho X_D (T.action (pt.r + 2))
  freshD : FreshPrem R S E rho T D Ef (pt.r + 1) (d + 1) X_D
  noMixedD : NoMixedOnPath O.height X_D (d + 1)

  batchB : (O.height B.parent).h = d →
    BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
      parentFG parentHeight validFor ΔF .target pt.r d (O.height A₀).T_h B
  batchD : (O.height X_D.parent).h = d + 1 →
    BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
      parentFG parentHeight validFor ΔF .target (pt.r + 1) (d + 1) U X_D

  targetsB : ∀ x ∈ rho.honest, ∃ j a,
    HonestRowAt S E rho T j x (pt.r + 1) a ∧
    RowComplete S rho D.signer valid x a ∧ NamesEntry (pair := D.heightPair) .target a (d + 1) U

  actionsInRun : T.action (pt.r + 2) ≤ rho.horizon
  capThroughBAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (T.action (pt.r + 1)) →
    HeldAt R E rho i x W → (O.height W).h ≤ d + 1
  capThroughFinalAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (T.action (pt.r + 2)) →
    HeldAt R E rho i x W → (O.height W).h ≤ d + 2
  finalityThroughFinalAction : ∀ i x W,
    i ≤ rho.events.length → i ≤ afterTicksIdx rho (T.action (pt.r + 2)) →
    HeldAt R E rho i x W → (O.finality W).h_F < d + 1
  heldDAtFinalAction : ∀ x ∈ rho.honest,
    X_D ∈ (R.core (V2.D.Run.stateBefore E rho (afterTicksIdx rho (T.action (pt.r + 2))) x)).fg.TF
  heldAAtEnd : ∀ x ∈ rho.honest,
    A₀ ∈ (R.core (V2.D.Run.stateBefore E rho rho.events.length x)).fg.TF

/-! P0d7b-a: kernel inputs. `KernelRunFacts` replaces the FG-SA aggregates `BaseSet` and
`Recovery₂` (R7) by the consequences that the kernel reads. -/

/-- The used run facts: schedule, FG fault weight, row delay, seat link and awake suffix. -/
structure KernelRunFacts (ΔF : Time) : Prop where
  schedule : V2.D.ScheduleWellFormed E rho
  fault_weight : Ef.weightOf (historyFaulty S rho) < Ef.q
  deltaF : E.Δ ≤ ΔF
  linked : Function.Injective (safetyHolder S rho)
  awake : ∀ x ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake x t = true

variable {decodeProposal bodyErase bodyRows blockWireRows parentFG parentHeight validFor makeFG
  valid ac} in
/-- The action reads at the final middle action for the same witness. -/
structure KernelActionSupply_W {cfg : FGConfig} {K : Nat} {ΔF : Time} {sp : FGServicePoint}
    {pt : KernelPt} {A : Block}
    (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) : Prop where
  read : ∀ x nd, postClock E rho x (T.action (pt.r + 2)) = some nd →
    (R.core (V2.D.Run.stateBefore E rho (afterTicksIdx rho (T.action (pt.r + 2))) x)).fg =
      (R.core nd).fg
  service : ∀ x ∈ rho.honest, FGSourceService R E rho x (T.action (pt.r + 2))
    m.cD ((pt.r + 2) * T.roundSlots) m.X_D
  head : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
    ∃ H, R.finalityHead nd = some H ∧ H ∈ (R.core nd).fg.TF
  walk : ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
    ∀ H, R.finalityHead nd = some H → Block.Preceq (R.erase m.X_D) (R.erase H)

end AvailableChain.FGCompose
end
