module
public import AvailableChainFGSAClaims.Statements.Fold

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure
open Gen.V2.Duty (faulty)
open Window (RetainedW CoveredW)

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Raw action-history input. DC: SAME named-row cut; INTENTIONAL fixed FG authentication. -/
def finHeight {n : Nat} (a : RowWire n) : Option Nat :=
  a.payload.finality_pair.map (·.height)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Raw action-history input. DC: SAME named-row cut; INTENTIONAL fixed FG authentication. -/
structure FreshPrem (q y : Nat) (X : FGBlock (Fin p.n)) where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:43–57: execution, schedule and no restart. -/
  base : BaseSet p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:948–958: every quorum has an honest row. -/
  faultQ : FaultQ p.n (faulty rho).card
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:954–956,1068–1069: strict raw-row cut after inclusion. -/
  cut : Time
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:948–958: no later than the next action. -/
  early : cut ≤ p.actionTime (q + 1)
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:954–956: raw rows of the full chain through X. -/
  rows : ChainRowsBefore p c E rho X cut
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:948–950,1054: no next-height honest row before the action. -/
  noNextRow : ∀ j x r a h t, HonestRowAt p c E rho j x r a →
    rowHeight a = some h → y + 1 ≤ h → eventTime rho j = some t →
    p.actionTime (q + 1) ≤ t
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:952–958,1068–1070: no finality row at or above y. -/
  noFinRow : ∀ j x r a h t, HonestRowAt p c E rho j x r a →
    finHeight a = some h → y ≤ h → eventTime rho j = some t →
    p.actionTime (q + 1) ≤ t

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:1060–1070,1628–1642,1769–1780.
DC-CS/W4FKChainJustification.lean:185 concludes a justification write.
DC: INTENTIONAL. FG-SA searches the ancestor path and excludes mixed crossings; there is no
DC `nj` latch (AvailableChainSimplexFG/ChainState.lean). -/
def JustifyAt (p : Params) : Prop :=
  ∀ (y : Nat) (U X : FGBlock (Fin p.n)), X ≠ .genesis → EntryAt p U y →
    FGBlock.Preceq U X.parent →
    ((heightView p X.parent).h = y → CoveredByChild p .target X U y) →
    NoMixedOnPath p X y → ∃ W, FGBlock.Preceq W X ∧ JustifiedCross p W U y

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:945–958,1061–1070. DC-CS/W4FKChainJustification.lean:185
DC: INTENTIONAL. Contract only; stage 5
supplies the fresh write. FG-SA excludes later row quorums
to obtain the fresh pending pair (FINAL 22:948–958). Q1/S1 use JustifyAt. -/
def JustifyFresh_W (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
    (U X : FGBlock (Fin p.n)), X ≠ .genesis → EntryAt p U y →
    FGBlock.Preceq U X.parent →
    ((heightView p X.parent).h = y → CoveredByChild p .target X U y) →
    NoMixedOnPath p X y → FreshPrem p c E rho q y X →
    (heightView p X).h = y + 1 ∧ (heightView p X).J = U ∧
      (heightView p X).h_j = y ∧ (Window.derive p p.K_W X).h_F < y ∧ Window.RetainedW p X y U

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002,1156–1158. The selected proposal handler is admitted
by `FGSA.parentFG`, `FGSA.blockAccepted`, and `FGSA.fgBlock`
(Model/Handlers.lean:28–64). No exact DC v2 event predicate exists.
The event is a delivery, and the FG block is the actual decoded block. -/
def Ready_W (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (t : Time) : Prop :=
  ∃ o s N P,
    rho.events[i]? = some (.deliver x o t) ∧
    N.erase = eraseFG W ∧ (toWire p o).decode = some (.block s N) ∧
    namedParentHeld (storeAt p c E rho i x) N = true ∧
    FGSA.parentFG (storeAt p c E rho i x) (eraseFG W) = some P ∧
    FGSA.blockAccepted p (storeAt p c E rho i x) s N P = true ∧
    FGSA.fgBlock P N.erase N.rows = W

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:1001–1005. The inserted tree and updated maximum, before the
J/F tests in `Window.update_finality` (Model/WindowStore.lean).
No DC event-indexed helper; this is the FG-SA model's intermediate store. -/
def receiptInsert_W (i : Nat) (x : V) (W : FGBlock (Fin p.n)) : Store (Fin p.n) :=
  let st := (storeAt p c E rho i x).fg
  { st with TF := insert W st.TF, h_max := max st.h_max ((heightView p W).h) }

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1005,1156–1161. No exact DC record: the v2 event index
selects one receipt for both delivery and guards (lead ruling 2026-09-30). -/
structure ReceiptWitness_W where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002: selected event index. -/
  index : Nat
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002: selected event time. -/
  time : Time

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002,1560–1563,1828–1830. No exact DC record;
selected events avoid independent existential delivery and guard reads. -/
structure BlockDelivery_W (W K : FGBlock (Fin p.n)) (a₀ d : Time) where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002: one selected event per honest receiver. -/
  selected : ∀ x, x ∈ rho.honest → ReceiptWitness_W
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002,1156–1158: prior coverage or actual admission.
  Both branches use the event selected above; receipt is strictly before d. -/
  witness : ∀ x (hx : x ∈ rho.honest),
    let w := selected x hx
    eventTime rho w.index = some w.time ∧ w.time < d ∧
    (FGBlock.Preceq K (storeAt p c E rho (w.index + 1) x).fg.F ∨
      (a₀ ≤ w.time ∧ Ready_W p c E rho w.index x W w.time))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1010,1156–1161. DC acceptance uses viability and a J path;
FG-SA restricts all guards to the same selected handler (FINAL 22:1001–1010). -/
structure AcceptGuards_W (W K : FGBlock (Fin p.n)) (a₀ d : Time)
    (delivery : BlockDelivery_W p c E rho W K a₀ d) : Prop where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–997,1156,1560–1562,1719: comparable finality at this handler. -/
  finCmp : ∀ x (hx : x ∈ rho.honest),
    let w := delivery.selected x hx
    Ready_W p c E rho w.index x W w.time →
    FGBlock.Preceq (storeAt p c E rho w.index x).fg.F K ∨
      FGBlock.Preceq K (storeAt p c E rho w.index x).fg.F
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:1007–1010,1159–1161,1832–1833: path or strict J improvement. -/
  jPath : ∀ x (hx : x ∈ rho.honest),
    let w := delivery.selected x hx
    Ready_W p c E rho w.index x W w.time →
    ¬ FGBlock.Preceq K (storeAt p c E rho w.index x).fg.F →
    FGBlock.Preceq (storeAt p c E rho w.index x).fg.J W ∨
      (storeAt p c E rho w.index x).fg.h_j < (Window.derive p p.K_W W).h_j
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:1001–1005,1158–1159,1993–1995: acceptance uses hmax, not lo. -/
  cap : ∀ x (hx : x ∈ rho.honest),
    let w := delivery.selected x hx
    Ready_W p c E rho w.index x W w.time →
    ¬ FGBlock.Preceq K (storeAt p c E rho w.index x).fg.F →
    (receiptInsert_W p c E rho w.index x W).h_max ≤ (heightView p W).h + 1

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:985–1015. No exact DC premise record: FG-SA bundles the
selected event with its guards and permits prior coverage (FINAL 22:995). -/
structure AcceptPrem_W (W K : FGBlock (Fin p.n)) (a₀ d : Time) where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:43–57: execution, schedule and no restart. -/
  base : BaseSet p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:994–999,1156: certificate comparison.
  The count bound; FaultX comes from `fgsa_faultX_count_rec` (P3 D40, GLY F-24).
  DC Generic/Conditions.lean:180 BelowOneThird: SAME (unit weights). -/
  faultBound : (faulty rho).card ≤ (p.n - 1) / 3
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:966,1151,1541–1547,1664: carrier finalizes K or a descendant. -/
  finalized : FGBlock.Preceq K (Window.derive p p.K_W W).F
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002: selected covered-or-admitted receipts. -/
  deliver : BlockDelivery_W p c E rho W K a₀ d
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1010: guards at those same receipts. -/
  guards : AcceptGuards_W p c E rho W K a₀ d deliver
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:60–63: deadline within the run. -/
  horizon : d ≤ rho.horizon

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:1011–1013,1162,1565–1566,1999. DC-CS/W4FKChainSecondCheckpoint.lean:43
(W4CommonFinalityAtConfirmationPin) concludes common finality at confirmation.
FG-SA uses selected receipt inputs and a strict supplied deadline,
as FINAL 22:60–63 prescribes; finalized branches use this directly. -/
def AcceptBefore_W (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (W K : FGBlock (Fin p.n)) (a₀ d : Time),
    AcceptPrem_W p c E rho W K a₀ d → ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x K d

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:981–1015,1150–1162. DC-CS/W4FKChainFinalityWrite.lean:177
is the pure fold input; event receipt is separate. Carrier slot and sync
belong to producers, because S2 D2 has a variable slot (22:1678–1682). -/
structure FinalizePrem_W (y : Nat) (K X : FGBlock (Fin p.n)) (a₀ d : Time) where
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:981–983,1150–1152: pending pair and quorum. -/
  fold : PendingFold_W p y K X
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:43–57: execution, schedule and no restart. -/
  base : BaseSet p c E rho
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:994–999,1156: certificate comparison.
  The count bound; FaultX comes from `fgsa_faultX_count_rec` (P3 D40, GLY F-24).
  DC Generic/Conditions.lean:180 BelowOneThird: SAME (unit weights). -/
  faultBound : (faulty rho).card ≤ (p.n - 1) / 3
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1002,1156–1158: the selected receipts. -/
  deliver : BlockDelivery_W p c E rho X K a₀ d
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:995–1010,1156–1161: guards at those same receipts. -/
  guards : AcceptGuards_W p c E rho X K a₀ d deliver
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:60–63: deadline within the run. -/
  horizon : d ≤ rho.horizon

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
FINAL 22:1149–1162,1543–1566. DC-CS/W4FKChainFinalityWrite.lean:177
followed by receipt acceptance. This is the exact +κ wrapper;
FinalizePrem_W itself has no slot or sync field (lead ruling 2026-09-30).
FG-SA uses the strict deadline T_q+β+Δ (FINAL 22:1154–1162). -/
def FinalizePending_W (p : Params) (ΔF : Time) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
    (K X : FGBlock (Fin p.n)), X.slot = q * p.R + kappaF p ΔF →
    FinalizePrem_W p c E rho y K X (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF q) →
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x K (kernelDeadlineW p ΔF q)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of the W interface. -/
theorem JustifyAt_def (p : Params) :
    JustifyAt p =
      (∀ (y : Nat) (U X : FGBlock (Fin p.n)), X ≠ .genesis → EntryAt p U y →
    FGBlock.Preceq U X.parent →
    ((heightView p X.parent).h = y → CoveredByChild p .target X U y) →
    NoMixedOnPath p X y → ∃ W, FGBlock.Preceq W X ∧ JustifiedCross p W U y) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of the W interface. -/
theorem JustifyFresh_W_def (p : Params) :
    JustifyFresh_W p =
      (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
    (U X : FGBlock (Fin p.n)), X ≠ .genesis → EntryAt p U y →
    FGBlock.Preceq U X.parent →
    ((heightView p X.parent).h = y → CoveredByChild p .target X U y) →
    NoMixedOnPath p X y → FreshPrem p c E rho q y X →
    (heightView p X).h = y + 1 ∧ (heightView p X).J = U ∧
      (heightView p X).h_j = y ∧ (Window.derive p p.K_W X).h_F < y ∧
      Window.RetainedW p X y U) := rfl

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of the W interface. -/
theorem Ready_W_def (i : Nat) (x : V) (W : FGBlock (Fin p.n)) (t : Time) :
    Ready_W p c E rho i x W t =
      (∃ o s N P,
    rho.events[i]? = some (.deliver x o t) ∧
    N.erase = eraseFG W ∧ (toWire p o).decode = some (.block s N) ∧
    namedParentHeld (storeAt p c E rho i x) N = true ∧
    FGSA.parentFG (storeAt p c E rho i x) (eraseFG W) = some P ∧
    FGSA.blockAccepted p (storeAt p c E rho i x) s N P = true ∧
    FGSA.fgBlock P N.erase N.rows = W) := rfl

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of the W interface. -/
theorem receiptInsert_W_def (i : Nat) (x : V) (W : FGBlock (Fin p.n)) :
    receiptInsert_W p c E rho i x W =
      (let st := (storeAt p c E rho i x).fg
  { st with TF := insert W st.TF, h_max := max st.h_max ((heightView p W).h) }) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of the W interface. -/
theorem AcceptBefore_W_def (p : Params) :
    AcceptBefore_W p =
      (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (W K : FGBlock (Fin p.n)) (a₀ d : Time),
    AcceptPrem_W p c E rho W K a₀ d → ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x K d) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME defining equation of the W interface. -/
theorem FinalizePending_W_def (p : Params) (ΔF : Time) :
    FinalizePending_W p ΔF =
      (∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
    (K X : FGBlock (Fin p.n)), X.slot = q * p.R + kappaF p ΔF →
    FinalizePrem_W p c E rho y K X (SA.proposalTime p.toParams X.slot)
      (kernelDeadlineW p ΔF q) →
    ∀ x ∈ rho.honest, AcceptsFinalBefore p c E rho x K (kernelDeadlineW p ΔF q)) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Plan item 13, blueprint 22:1256–1263. DC: INTENTIONAL actual fresh F7 rows.
The same complete row has a nonempty fresh source height and the protected pair.
Earlier emissions of this identity have smaller height. Permission is not emission. -/
def FreshFinalityRows_W (q y : Nat) (U : FGBlock (Fin p.n))
    (S : Finset (Fin p.n)) (rows : Fin p.n → RowWire p.n) : Prop :=
  S ⊆ honestSeats p c rho ∧ p.E.IsQuorum S ∧ ∀ i ∈ S,
    ∃ j C, HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q (rows i) ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
      (rows i).auth = .seat .fg i ∧ rowHeight (rows i) = some (y + 1) ∧
      FinalityNames p (rows i) y U ∧
      actionSourceFG p c E rho (rho.seatOf (.base .fg) i) q = some (some C) ∧
      (heightView p C).h = y + 1 ∧
      ∀ j' r a h, r < q →
        HonestRowAt p c E rho j' (rho.seatOf (.base .fg) i) r a →
        rowHeight a = some h → h < y + 1

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Plan item 13. DC: INTENTIONAL retained-or-covered terminal input.
S4.2b supplies retention. Stage 5 supplies carriage. No latest-J stability is assumed. -/
structure TerminalCarriagePrem_W (ΔF : Time) (q y : Nat)
    (A U X : FGBlock (Fin p.n)) where
  base : BaseSet p c E rho
  faultQ : FaultQ p.n (faulty rho).card
  deltaF : E.Δ ≤ ΔF
  carrier : ∃ wireRows, HonestCarrier p c E rho X.slot (eraseFG X) wireRows ∧
    X.rows = wireRows.filterMap RowWire.toRow?
  parent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
    FGSA.fgBlockOf st (eraseFG X).parent = some X.parent
  path : FGBlock.Preceq A X.parent
  freshHeight : (heightView p A).h = y + 1
  retainedOrCovered : RetainedW p X.parent y U ∨ CoveredW p X.parent y U
  horizon : max (p.actionTime q) E.t_GST + ΔF ≤ SA.proposalTime p.toParams X.slot ∧
    SA.proposalTime p.toParams X.slot ≤ rho.horizon
  seats : Finset (Fin p.n)
  rows : Fin p.n → RowWire p.n
  fresh : FreshFinalityRows_W p c E rho q y U seats rows
  /-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The F6/F7 producers supply the common height entry of the fresh rows at A.
  Paper: 22:1250–1254 (a continuation cannot cross d+2, so the entry is fixed below X_D)
  and 22:1276–1277 ("the same high entry"). -/
  heightEntry : ∀ i ∈ seats,
    namedEntry (rows i).payload.height_pair = some (y + 1, (heightView p A).T_h.root)
  receipt : ∀ i ∈ seats,
    HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) X.slot) (rows i)
      (max (p.actionTime q) E.t_GST + ΔF) ∧
    heldAtProposal p c E rho X.slot (rows i)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Plan item 13, blueprint 22:1274–1282. DC: INTENTIONAL both R6W arms.
Contract only. Each retained-row arm uses the same wire and exact bitmap.
Prior coverage remains a separate branch. There is no repeat emission. -/
def TerminalCarriage_W (p : Params) (ΔF : Time) : Prop :=
  ∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
    (A U X : FGBlock (Fin p.n)) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X),
    CoveredW p X.parent y U ∨
      ((∀ i ∈ h.seats,
        ValidForParent p c E rho X.slot (eraseFG X) (h.rows i) ∧
        ((heightView p X.parent).h = y + 1 ∧
          HeightMatch p c E rho X.slot (eraseFG X) (h.rows i) ∨
         ∃ row rowH, (h.rows i).toRow? = some row ∧
           rowHeight (h.rows i) = some rowH ∧
           y < rowH ∧ rowH < (heightView p X.parent).h ∧
           Window.staleUseful (FGSA.parentFoldState p X.slot X.parent) row = true ∧
           row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U)) ∧
       FinalityCoveredByChild_W p X U y)

omit [Fintype V] in
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME equation for actual fresh-row evidence. -/
theorem FreshFinalityRows_W_def (q y : Nat) (U : FGBlock (Fin p.n))
    (S : Finset (Fin p.n)) (rows : Fin p.n → RowWire p.n) :
    FreshFinalityRows_W p c E rho q y U S rows =
      (S ⊆ honestSeats p c rho ∧ p.E.IsQuorum S ∧ ∀ i ∈ S,
        ∃ j C, HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q (rows i) ∧
          RowComplete p c rho (rho.seatOf (.base .fg) i) (rows i) ∧
          (rows i).auth = .seat .fg i ∧ rowHeight (rows i) = some (y + 1) ∧
          FinalityNames p (rows i) y U ∧
          actionSourceFG p c E rho (rho.seatOf (.base .fg) i) q = some (some C) ∧
          (heightView p C).h = y + 1 ∧
          ∀ j' r a h, r < q →
            HonestRowAt p c E rho j' (rho.seatOf (.base .fg) i) r a →
            rowHeight a = some h → h < y + 1) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
DC: SAME equation for the terminal contract. -/
theorem TerminalCarriage_W_def (p : Params) (ΔF : Time) :
    TerminalCarriage_W p ΔF =
      (∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
        (A U X : FGBlock (Fin p.n)) (h : TerminalCarriagePrem_W p c E rho ΔF q y A U X),
        CoveredW p X.parent y U ∨
          ((∀ i ∈ h.seats,
            ValidForParent p c E rho X.slot (eraseFG X) (h.rows i) ∧
            ((heightView p X.parent).h = y + 1 ∧
              HeightMatch p c E rho X.slot (eraseFG X) (h.rows i) ∨
             ∃ row rowH, (h.rows i).toRow? = some row ∧
               rowHeight (h.rows i) = some rowH ∧
               y < rowH ∧ rowH < (heightView p X.parent).h ∧
               Window.staleUseful (FGSA.parentFoldState p X.slot X.parent) row = true ∧
               row.finality_pair = some ⟨y, U.root⟩ ∧ RetainedW p X.parent y U)) ∧
           FinalityCoveredByChild_W p X U y)) := rfl

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
omit [DecidableEq V] [Fintype V] in
theorem finHeight_def {n : Nat} (a : RowWire n) :
    finHeight a = a.payload.finality_pair.map (·.height) := rfl

end AvailableChain.FGSA.Run
end
