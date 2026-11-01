module
public import AvailableChainFGCompose.Statements.Service
public import AvailableChainGeneric.Statements.V2.Duty.Receipt -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.V2.Duty.DeliveryBy
public import AvailableChainSimplexFG.WindowStore

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface P)
variable (entry : Wire → Option (Height × BlockId))
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → (FGBlock (Fin n)) → Wire → Bool)

structure ReceiverService (family : P.Object → Prop)
    (timely : P.State → P.Object → Prop)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (o : P.Object) (send freeze : Time) (x : V) where
  dl : Time → Time
  cut : Time
  anchor : Time
  within : Gen.V2.Duty.DeliveryWithinOn E rho family dl cut
  ready : Gen.V2.Duty.ReadyTrigger E rho o send x anchor (dl anchor)
  send_le : send ≤ anchor
  nonneg : 0 ≤ anchor
  later : anchor < dl anchor
  cut_le : dl anchor ≤ cut
  horizon : dl anchor ≤ rho.horizon
  freeze_le : dl anchor ≤ freeze
  history : Gen.V2.Duty.HistorySafeAt E rho x o anchor
  epoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho anchor)
    (V2.D.Run.idxBefore rho freeze)
  handlers : ∀ j t, anchor ≤ t → t < dl anchor →
    V2.D.Run.handlesAt E rho j x o t → P.wellFormed o = true ∧
      P.depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
      timely (V2.D.Run.stateBefore E rho j x) o
  not_excluded : P.excludes (V2.D.Run.stateBeforeTime E rho (dl anchor) x) o = false

structure FreshHeadService (family : P.Object → Prop)
    (timely : P.State → P.Object → Prop) (T : FGTiming)
    (headObject : Slot → Fin n → BlockId → P.Object)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (s : Slot) (q : Fin n) (b : BlockId) (freeze : Time) (x : V) where
  dl : Time → Time
  cut : Time
  within : Gen.V2.Duty.DeliveryWithinOn E rho family dl cut
  ready : Gen.V2.Duty.ReadyTrigger E rho (headObject s q b)
    (T.vote s) x (T.vote s) (dl (T.vote s))
  later : T.vote s < dl (T.vote s)
  cut_le : dl (T.vote s) ≤ cut
  horizon : dl (T.vote s) ≤ rho.horizon
  freeze_le : dl (T.vote s) ≤ freeze
  epoch : V2.D.restartFree rho x (V2.D.Run.actionCut rho (T.vote s))
    (V2.D.Run.idxBefore rho freeze)
  handlers : ∀ j t, T.vote s ≤ t → t < dl (T.vote s) →
    V2.D.Run.handlesAt E rho j x (headObject s q b) t →
    P.wellFormed (headObject s q b) = true ∧
      P.depsPresent (V2.D.Run.stateBefore E rho j x) (headObject s q b) = true ∧
      timely (V2.D.Run.stateBefore E rho j x) (headObject s q b)
  not_excluded : P.excludes (V2.D.Run.stateBeforeTime E rho (dl (T.vote s)) x)
    (headObject s q b) = false

def TargetReceiptService {Body : Type} (bodyObject : Slot → Body → P.Object)
    (bodyErase : Body → Block) (family : P.Object → Prop)
    (timely : P.State → P.Object → Prop) (E : Generic.Env V)
    (rho : V2.D.Run V P) (K : Block) (freeze : Time) (x : V) : Prop :=
  K = .genesis ∨ ∃ s N send, bodyErase N = K ∧
    Nonempty (ReceiverService family timely E rho (bodyObject s N) send freeze x)

structure FinalityActionReceipts {Body : Type} (T : FGTiming)
    (R : FGCoreReads P n Base Proposal Wire) (A : FGACServiceReads V)
    (E : Generic.Env V) (rho : V2.D.Run V P)
    (headHolder : Slot → Fin n → V)
    (family : P.Object → Prop) (timely : P.State → P.Object → Prop)
    (headObject : Slot → Fin n → BlockId → P.Object)
    (bodyObject : Slot → Body → P.Object) (bodyErase : Body → Block) : Prop where
  service : ∀ q x, x ∈ rho.honest → E.t_GST < T.action q →
    E.t_GST ≤ slotStartZ T (((q * T.roundSlots + 1 : Nat) : Int) - 1) →
    T.action q ≤ rho.horizon → ∀ nd,
    postClock E rho x (T.action q) = some nd → ∀ a K,
    headHolder (q * T.roundSlots + 1) a ∈ rho.honest →
    A.headAtLabel (headHolder (q * T.roundSlots + 1) a)
      (q * T.roundSlots + 1) = some K →
    Block.Preceq (R.erase (R.core nd).fg.F) K →
    Nonempty (FreshHeadService family timely T headObject E rho
      (q * T.roundSlots + 1) a K.root (T.action q) x) ∧
      TargetReceiptService bodyObject bodyErase family timely E rho K (T.action q) x

/-! P0d7a5: selected receipt and acceptance. The selected receipt `ready` is a
parameter; its handler equation is the exact step consequence in `AcceptStep_W`. -/

/-- The selected receipt event of one honest receiver. -/
structure ReceiptWitness_W where
  index : Nat
  time : Time

variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)
variable (ready : Nat → V → FGBlock (Fin n) → Time → Prop)

/-- The inserted tree and maximum height before the window J/F tests. -/
def receiptInsert_W (i : Nat) (x : V) (W : FGBlock (Fin n)) : Store (Fin n) :=
  let st := (R.core (V2.D.Run.stateBefore E rho i x)).fg
  { st with
    TF := insert W st.TF
    h_max := max st.h_max (SimplexFG.Window.derive Ef cfg K W).h }

/-- One selected event per honest receiver: prior coverage or the selected receipt. -/
structure BlockDelivery_W (W U : FGBlock (Fin n)) (a₀ d : Time) where
  selected : ∀ x, x ∈ rho.honest → ReceiptWitness_W
  witness : ∀ x (hx : x ∈ rho.honest),
    let w := selected x hx
    rho.events[w.index]?.map V2.Event.time = some w.time ∧ w.time < d ∧
    (FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho (w.index + 1) x)).fg.F ∨
      (a₀ ≤ w.time ∧ ready w.index x W w.time))

/-- The acceptance guards at the same selected events. -/
structure AcceptGuards_W (W U : FGBlock (Fin n)) (a₀ d : Time)
    (delivery : BlockDelivery_W R E rho ready W U a₀ d) : Prop where
  finCmp : ∀ x (hx : x ∈ rho.honest),
    let w := delivery.selected x hx
    ready w.index x W w.time →
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.F U ∨
      FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.F
  jPath : ∀ x (hx : x ∈ rho.honest),
    let w := delivery.selected x hx
    ready w.index x W w.time →
    ¬ FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.F →
    FGBlock.Preceq (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.J W ∨
      (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.h_j <
        (SimplexFG.Window.derive Ef cfg K W).h_j
  cap : ∀ x (hx : x ∈ rho.honest),
    let w := delivery.selected x hx
    ready w.index x W w.time →
    ¬ FGBlock.Preceq U (R.core (V2.D.Run.stateBefore E rho w.index x)).fg.F →
    (receiptInsert_W R E rho Ef cfg K w.index x W).h_max ≤
      (SimplexFG.Window.derive Ef cfg K W).h + 1

/-- The selected receipt, its guards and the carrier finality. The aggregate
execution input is split: only the schedule is read. -/
structure AcceptPrem_W (W U : FGBlock (Fin n)) (a₀ d : Time) where
  schedule : V2.D.ScheduleWellFormed E rho
  finalized : FGBlock.Preceq U (SimplexFG.Window.derive Ef cfg K W).F
  deliver : BlockDelivery_W R E rho ready W U a₀ d
  guards : AcceptGuards_W R E rho Ef cfg K ready W U a₀ d deliver
  horizon : d ≤ rho.horizon

/-- Fieldwise form of `PendingFold_W`: a real child whose rows complete one retained bit
set. The cover is the body of `FinalityCoveredByChild_W` with `FinRowNames` unfolded. -/
structure PendingFold_W (y : Nat) (U X : FGBlock (Fin n)) : Prop where
  child : X ≠ .genesis
  cover : ∃ e ∈ (SimplexFG.Window.derive Ef cfg K X.parent).W, e.j = y ∧ e.X = U ∧
    ∃ Q : Finset (Fin n), Ef.IsQuorum Q ∧ ∀ i ∈ Q,
      i ∈ e.Q ∨ ∃ row ∈ X.rows, row.signer = i ∧ row.finality_pair = some ⟨y, U.root⟩

/-- The pending pair with the selected receipts and guards. -/
structure FinalizePrem_W (y : Nat) (U X : FGBlock (Fin n)) (a₀ d : Time) where
  fold : PendingFold_W Ef cfg K y U X
  schedule : V2.D.ScheduleWellFormed E rho
  deliver : BlockDelivery_W R E rho ready X U a₀ d
  guards : AcceptGuards_W R E rho Ef cfg K ready X U a₀ d deliver
  horizon : d ≤ rho.horizon

/-- The exact selected one-step consequence: the receipt inserts `W`, applies the
window finality update, and the carrier finality is in the inserted tree. -/
def AcceptStep_W : Prop :=
  ∀ i x W t, x ∈ rho.honest → ready i x W t →
    (R.core (V2.D.Run.stateBefore E rho (i + 1) x)).fg =
      SimplexFG.Window.update_finality Ef cfg K
        { (R.core (V2.D.Run.stateBefore E rho i x)).fg with
          TF := insert W (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF } W ∧
    (SimplexFG.Window.derive Ef cfg K W).F ∈
      insert W (R.core (V2.D.Run.stateBefore E rho i x)).fg.TF

/-- Durable finality: monotone along steps and kept by restore. -/
structure FGFinalityDurableLaws : Prop where
  mono : ∀ X : FGBlock (Fin n),
    Gen.V2.Duty.MonoAlong (P := P) (fun nd => FGBlock.Preceq X (R.core nd).fg.F)
  restore : ∀ nd t, (R.core (P.restore (P.durable nd) t)).fg.F = (R.core nd).fg.F

end AvailableChain.FGCompose
end
