module
public import AvailableChainFGCompose.Statements.FinalityKernel -- shake: keep (kernel premises)
public import AvailableChainFGCompose.Statements.FinalityReceipts -- shake: keep (receipt services)
public import AvailableChainKitFG.WindowViewsDef

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (cfg : FGConfig) (K : Nat) (valid : Wire → Bool)

/-- The exact decoded signer and finality pair. -/
def FinRowNames (row : Row (Fin n)) (i : Fin n) (y : Nat)
    (U : FGBlock (Fin n)) : Prop :=
  row.signer = i ∧ row.finality_pair = some ⟨y, U.root⟩

/-- The complete signed wire names this finality pair. -/
def FinalityNames (a : Wire) (y : Nat) (U : FGBlock (Fin n)) : Prop :=
  D.finalityPair a = some ⟨y, U.root⟩

/-- Each seat contributes a retained bit or an exact row in the child. -/
def FinalityCoveredByChild_W (X U : FGBlock (Fin n)) (y : Nat) : Prop :=
  ∃ e ∈ (SimplexFG.Window.derive Ef cfg K X.parent).W, e.j = y ∧ e.X = U ∧
    ∃ Q : Finset (Fin n), Ef.IsQuorum Q ∧ ∀ i ∈ Q,
      i ∈ e.Q ∨ ∃ row ∈ X.rows, FinRowNames row i y U

/-- Fresh signed rows keep their actual source, event, and earlier history. -/
def FreshFinalityRows_W (q y : Nat) (U : FGBlock (Fin n))
    (seats : Finset (Fin n)) (rows : Fin n → Wire) : Prop :=
  (∀ i ∈ seats, safetyHolder S rho i ∈ rho.honest) ∧ Ef.IsQuorum seats ∧
    ∀ i ∈ seats, ∃ j C,
      HonestRowAt S E rho T j (safetyHolder S rho i) q (rows i) ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) (rows i) ∧
      D.signer (rows i) = some i ∧ historyRowHeight S D (rows i) = some (y + 1) ∧
      FinalityNames S D (rows i) y U ∧
      actionSourceFG R E rho T (safetyHolder S rho i) q = some (some C) ∧
      (O.height C).h = y + 1 ∧
      ∀ j' r a h, r < q →
        HonestRowAt S E rho T j' (safetyHolder S rho i) r a →
        historyRowHeight S D a = some h → h < y + 1

variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
variable (rowValid : SimplexFG.Window.State (Fin n) → Wire → Bool)

/-- The exact batch premises, with schedule and fault consequences separated. -/
structure FinalityBatchPrem_W (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin n)) : Prop where
  schedule : V2.D.ScheduleWellFormed E rho
  fault_weight : Ef.weightOf (historyFaulty S rho) < Ef.q
  deltaF : E.Δ ≤ ΔF
  rowsReceipt : TRowsReceipt R S E rho T blockWireRows ΔF
  carrier : ∃ rows, HonestCarrier E rho I carrier X.slot (R.erase X) rows ∧
    X.rows = rows.filterMap S.decode
  after : q * T.roundSlots + kappaF T ΔF ≤ X.slot
  horizon : max (T.action q) E.t_GST + ΔF ≤ T.proposal X.slot ∧
    T.proposal X.slot ≤ rho.horizon
  parent : ∃ nd, proposalStateAt E rho I X.slot = some nd ∧
    parentFG nd (R.erase X).parent = some X.parent
  birth : ∃ B, FGBlock.Preceq B X.parent ∧
    JustificationBirth Ef (KitFG.Window.certificateHeight Ef cfg K) B y U
  retainedOrCovered : KitFG.Window.RetainedW Ef cfg K X.parent y U ∨
    KitFG.Window.CoveredW Ef cfg K X.parent y U
  batch : ∃ seats : Finset (Fin n),
    (∀ i ∈ seats, safetyHolder S rho i ∈ rho.honest) ∧ Ef.IsQuorum seats ∧
    ∀ i ∈ seats, ∃ j a,
      HonestRowAt S E rho T j (safetyHolder S rho i) q a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧
      D.signer a = some i ∧ FinalityNames S D a y U ∧
      HeldBefore R E rho blockWireRows (V2.D.proposerOf rho I X.slot) a
        (max (T.action q) E.t_GST + ΔF) ∧
      heldAtProposal R E rho I blockWireRows X.slot a ∧
      (KitFG.Window.RetainedW Ef cfg K X.parent y U →
        rowValid (KitFG.Window.parentState Ef cfg K X.parent X.slot) a = true ∧
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) a)

/-- Terminal carriage retains the same fixed batch and its actual receipts. -/
structure TerminalCarriagePrem_W (ΔF : Time) (q y : Nat)
    (A U X : FGBlock (Fin n)) where
  schedule : V2.D.ScheduleWellFormed E rho
  fault_weight : Ef.weightOf (historyFaulty S rho) < Ef.q
  deltaF : E.Δ ≤ ΔF
  carrier : ∃ rows, HonestCarrier E rho I carrier X.slot (R.erase X) rows ∧
    X.rows = rows.filterMap S.decode
  parent : ∃ nd, proposalStateAt E rho I X.slot = some nd ∧
    parentFG nd (R.erase X).parent = some X.parent
  path : FGBlock.Preceq A X.parent
  freshHeight : (O.height A).h = y + 1
  retainedOrCovered : KitFG.Window.RetainedW Ef cfg K X.parent y U ∨
    KitFG.Window.CoveredW Ef cfg K X.parent y U
  horizon : max (T.action q) E.t_GST + ΔF ≤ T.proposal X.slot ∧
    T.proposal X.slot ≤ rho.horizon
  seats : Finset (Fin n)
  rows : Fin n → Wire
  fresh : FreshFinalityRows_W R S O T E rho D Ef valid q y U seats rows
  heightEntry : ∀ i ∈ seats,
    namedEntry (D.heightPair (rows i)) = some (y + 1, (O.height A).T_h.root)
  receipt : ∀ i ∈ seats,
    HeldBefore R E rho blockWireRows (V2.D.proposerOf rho I X.slot) (rows i)
      (max (T.action q) E.t_GST + ΔF) ∧
    heldAtProposal R E rho I blockWireRows X.slot (rows i)

end AvailableChain.FGCompose
end
