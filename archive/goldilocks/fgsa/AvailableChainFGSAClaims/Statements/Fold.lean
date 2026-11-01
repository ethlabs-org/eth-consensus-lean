module
public import AvailableChainFGSAClaims.Statements.ChannelProps
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSA.Statements.WindowEntries

@[expose] public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
open Gen.Pure
open Gen.V2.Duty (faulty)
open Window (RetainedW CoveredW)

/-- FINAL 22:612–635. No exact DC counterpart.
DC separates target and progress; P3:3952–3956 requires one discriminator.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
inductive RowKind | target | progress

/-- FINAL 22:583–635. DC-CS/W4FKChainJustification.lean:122.
Same exact signer/target pair. FINAL I7 also permits progress timeout rows.
DC: SAME: height coverage or its explicit action-history input. -/
def RowNames (p : FGSA.Params) (k : RowKind) (row : Row (Fin p.n))
    (i : Fin p.n) (y : Nat) (U : FGBlock (Fin p.n)) : Prop :=
  row.signer = i ∧ match k with
  | .target => row.height_pair = .vote y U.root false
  | .progress => ∃ timeout, row.height_pair = .vote y U.root timeout

/-- FINAL 22:43–54,1056–1059. No exact DC counterpart.
Both models enforce increasing slots. Pure FGBlock paths need this premise.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def SlotChain {n : Nat} (X : FGBlock (Fin n)) : Prop :=
  ∀ W, FGBlock.Preceq W X → W ≠ .genesis → W.parent.slot < W.slot

/-- FINAL 22:909–938,612–635. DC-CS/W4FKChainJustification.lean:185.
Same height/T_h entry fields, packaged for the FINAL ancestor-path contract.
DC: SAME: height coverage or its explicit action-history input. -/
def EntryAt (p : FGSA.Params) (U : FGBlock (Fin p.n)) (y : Nat) : Prop :=
  (heightView p U).h = y ∧ (heightView p U).T_h = U

/-- FINAL 22:1060–1070. DC-CS/W4FKChainJustification.lean:185.
Same J/h_j write, with explicit parent/child heights as FINAL F5 requires.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def JustifiedCross (p : FGSA.Params) (W U : FGBlock (Fin p.n)) (y : Nat) : Prop :=
  (heightView p W.parent).h = y ∧ (heightView p W).h = y + 1 ∧
  (heightView p W).J = U ∧ (heightView p W).h_j = y

/-- FINAL 22:1056–1070. DC-CS/ProgressQuorumCore.lean:39.
FG-SA distinguishes the non-justifying branch by h_j<y (ChainState.lean:145).
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def MixedCross (p : FGSA.Params) (W : FGBlock (Fin p.n)) (y : Nat) : Prop :=
  (heightView p W.parent).h = y ∧ (heightView p W).h = y + 1 ∧
  (heightView p W).h_j < y

/-- FINAL 22:1056–1070,1762–1780. No exact DC counterpart.
FINAL F5 excludes mixed ancestor crossings; FG-SA has no DC nj latch.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def NoMixedOnPath (p : FGSA.Params) (X : FGBlock (Fin p.n)) (y : Nat) : Prop :=
  ∀ W, FGBlock.Preceq W X.parent → ¬ MixedCross p W y

/-- FINAL 22:583–635. DC-CS/W4FKChainJustification.lean:122.
Same parent bit or exact child row; FINAL I7 also needs progress bits.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def SeatCovers (p : FGSA.Params) (k : RowKind) (X U : FGBlock (Fin p.n))
    (y : Nat) (i : Fin p.n) : Prop :=
  (match k with
   | .target   => i ∈ (heightView p X.parent).target_participation
   | .progress => i ∈ (heightView p X.parent).progress) ∨
  ∃ row ∈ X.rows, RowNames p k row i y U

/-- FINAL 22:583–635. DC-CS/W4FKChainJustification.lean:122.
Same positive quorum and per-member coverage; FG-SA uses unit-weight seats.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def CoveredByChild (p : FGSA.Params) (k : RowKind) (X U : FGBlock (Fin p.n)) (y : Nat) : Prop :=
  ∃ S : Finset (Fin p.n), p.E.q ≤ p.E.weightOf S ∧ ∀ i ∈ S, SeatCovers p k X U y i

/-- FINAL 22:612–635,1043–1049. DC-CS/W4FKChainJustification.lean:185.
DC also has ProgressQuorumCore.lean:39, but no exact combined contract.
FINAL I7 requires an ancestor witness and FG-SA has no nj latch.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def foldTrichotomy (p : FGSA.Params) (k : RowKind) : Prop :=
  ∀ (y : Nat) (U X : FGBlock (Fin p.n)), X ≠ .genesis → EntryAt p U y →
    FGBlock.Preceq U X.parent →
    ((heightView p X.parent).h = y → CoveredByChild p k X U y) →
    (k = .progress → U.slot + p.δt ≤ X.slot) →
    y + 1 ≤ (heightView p X).h ∧
    (k = .target → (∃ W, FGBlock.Preceq W X ∧ JustifiedCross p W U y) ∨
                   (∃ W, FGBlock.Preceq W X.parent ∧ MixedCross p W y))

/-- FINAL 22:612–635. DC-CS/ProgressQuorumCore.lean:39.
Same mature quorum advance. Blueprint 21:2329–2341 additionally transports
stored coverage along a constant-height path (H.9-Q).
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
def StoredProgressConsume (p : FGSA.Params) : Prop :=
  ∀ (y : Nat) (U B X : FGBlock (Fin p.n)), EntryAt p U y → FGBlock.Preceq U B.parent →
    FGBlock.Preceq B X.parent → CoveredByChild p .progress B U y →
    (heightView p X.parent).h = y → U.slot + p.δt ≤ X.slot →
    (heightView p X).h = y + 1

/-- FINAL 22:1056–1059,940–944,1523,1624–1626. DC-CS/CarrierTimeoutGate.lean:121.
DC derives a pre-maturity gate from round/delay bounds. FINAL F4 takes
the gate directly and needs all ancestors, not only the fixed +1 slot.
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
def NoMixedMaturity (p : FGSA.Params) : Prop :=
  ∀ (y : Nat) (U X : FGBlock (Fin p.n)), SlotChain X → EntryAt p U y →
    FGBlock.Preceq U X.parent → X.slot < U.slot + p.δt + 1 → NoMixedOnPath p X y

/-- FINAL 22:583–610. Exact wire height pair; no DC wire counterpart:
FG-SA uses seat-authenticated RowWire (Model/Objects.lean:88–96).
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
def NamesEntry (p : Params) (k : RowKind) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) : Prop := match k with
  | .target => a.payload.height_pair = .vote y U.root false
  | .progress => ∃ timeout, a.payload.height_pair = .vote y U.root timeout

/-- FINAL 22:946–956. Model `RowBody.height_pair`; no DC optional read helper.
The empty pair has no height (lead ruling 2026-09-30).
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
def rowHeight {n : Nat} (a : RowWire n) : Option Nat :=
  match a.payload.height_pair with
  | .empty => none
  | .vote h _ _ => some h

/-- FINAL 22:55–63. Model `V2.Event.time`; no DC optional read helper.
An index outside the event list has no time.
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
def eventTime {V In : Type} {P : V2.ProtocolSpecD In} (rho : V2.D.Run V P)
    (i : Nat) : Option Time := rho.events[i]?.map V2.Event.time

/-- FINAL 22:583–610. No DC seat-map helper: DC uses validator identities;
FG-SA uses linked seats (Model/Protocol.lean:RunLabel).
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
noncomputable def honestSeats (p : Params) {V : Type} [DecidableEq V] {In : Type}
    (c : AppCodec In) (rho : V2.D.Run V (fgsa p c)) : Finset (Fin p.n) :=
  by
    classical
    exact Finset.univ.filter (fun i => rho.seatOf (.base .fg) i ∈ rho.honest)

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem rowHeight_def {n : Nat} (a : RowWire n) :
    rowHeight a = match a.payload.height_pair with
      | .empty => none
      | .vote h _ _ => some h := rfl

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem eventTime_def {V In : Type} {P : V2.ProtocolSpecD In} (rho : V2.D.Run V P)
    (i : Nat) : eventTime rho i = rho.events[i]?.map V2.Event.time := rfl

-- equation export required by BUILD §7.2 B3a (post-freeze additive _def batch)
theorem honestSeats_def (p : Params) {V : Type} [DecidableEq V] {In : Type}
    (c : AppCodec In) (rho : V2.D.Run V (fgsa p c)) :
    honestSeats p c rho = (by
      classical
      exact Finset.univ.filter (fun i => rho.seatOf (.base .fg) i ∈ rho.honest)) := rfl

/-- FINAL 22:954–956,1068–1069. Raw occurrences only; no selected wire.
DC-CS/ProposalBridge.lean:324 uses admission before a cut. FG-SA defers
wire provenance to F1.6 `held_chain_row_origin` (lead ruling 2026-09-30).
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def ChainRowsBefore (p : Params) {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (B : FGBlock (Fin p.n)) (cut : Time) : Prop :=
  ∀ W, FGBlock.Preceq W B → ∀ row ∈ W.rows, ∃ x t,
    x ∈ rho.honest ∧ t < cut ∧
      Gen.V2.Duty.HoldsBefore E rho (fun nd => W ∈ nd.st.fg.TF) t x

/-- FINAL 22:1771–1780. No exact DC contract: FG-SA row origin and strict
pre-action cut replace a DC carrier timeout gate (DC-CS/CarrierTimeoutGate.lean:121).
DC: INTENTIONAL: height coverage or its explicit action-history input. -/
structure PreBatchPrem (p : Params) {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q y : Nat) (U X : FGBlock (Fin p.n)) where
  /-- FINAL 22:43–57: execution, linked seats, schedule and no restart. -/
  base : BaseSet p c E rho
  /-- FINAL 22:1775: each quorum has an honest row. -/
  faultQ : FaultQ p.n (faulty rho).card
  /-- FINAL 22:1771–1776: protected entry. -/
  entry : EntryAt p U y
  /-- FINAL 22:1771–1776: entry on the parent path. -/
  path : FGBlock.Preceq U X.parent
  /-- FINAL 22:1774–1778: strict raw-row cut. -/
  cut : Time
  /-- FINAL 22:1774–1778: cut no later than the action. -/
  early : cut ≤ p.actionTime q
  /-- FINAL 22:1776,954–956: raw parent-chain rows before the cut. -/
  rows : ChainRowsBefore p c E rho X.parent cut
  /-- FINAL 22:1774–1775: no earlier honest row at or above y. -/
  noRow : ∀ j x r a h t, HonestRowAt p c E rho j x r a →
    rowHeight a = some h → y ≤ h → eventTime rho j = some t → p.actionTime q ≤ t

/-- FINAL 22:1775–1780. No exact DC counterpart: pre-action row exclusion
replaces the delay gate of DC-CS/CarrierTimeoutGate.lean:121.
DC: INTENTIONAL: FG-SA height coverage has explicit chain-history inputs. -/
def NoMixedPreBatchParent (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q y : Nat) (U X : FGBlock (Fin p.n)),
    PreBatchPrem p c E rho q y U X → NoMixedOnPath p X y

/-- SO-COV height batch with one complete valid witness per quorum seat.
The binding is producer-side; TRowsReceipt, TRowsSync, TRows, HealT and fgsaDelay are exempt.
DC: INTENTIONAL earlier-or-current send-once origins; SAME height coverage. -/
structure BatchPrem (p : Params) {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (ΔF : Time) (k : RowKind) (q y : Nat) (U X : FGBlock (Fin p.n)) : Prop where
  /-- FINAL 22:43–57: execution and linked seats. -/
  base : BaseSet p c E rho
  /-- FINAL 22:593–598: honest-row quorum witness. -/
  faultQ : FaultQ p.n (faulty rho).card
  /-- Producer-side row-delay binding. -/
  deltaF : E.Δ ≤ ΔF
  /-- All-emissions receipt includes rows sent before GST. -/
  rowsReceipt : TRowsReceipt p c E rho ΔF
  /-- Receipt is before the proposal and within the finite run horizon. -/
  horizon : max (p.actionTime q) E.t_GST + ΔF ≤
      SA.proposalTime p.toParams X.slot ∧
    SA.proposalTime p.toParams X.slot ≤ rho.horizon
  /-- FINAL 22:585–598: exact rows of the honest carrier. -/
  carrier : ∃ rows, HonestCarrier p c E rho X.slot (eraseFG X) rows ∧
    X.rows = rows.filterMap RowWire.toRow?
  /-- The carrier follows cutoff q; this is not a row age limit. -/
  after : q * p.R + 2 ≤ X.slot
  /-- A quorum of honest seats has complete matching R6-valid witnesses. -/
  valid : ∃ S : Finset (Fin p.n), S ⊆ honestSeats p c rho ∧
    p.E.q ≤ p.E.weightOf S ∧ ∀ i ∈ S, ∃ j r a t,
    r ≤ q ∧ HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) r a ∧
    a.auth = .seat .fg i ∧ NamesEntry p k a y U ∧
    eventTime rho j = some t ∧ t = p.actionTime r ∧
    ValidForParent p c E rho X.slot (eraseFG X) a ∧
    HeightMatch p c E rho X.slot (eraseFG X) a
  /-- FINAL 22:583–610: matching entry. -/
  entry : EntryAt p U y
  /-- FINAL 22:583–610: entry on the parent path. -/
  path : FGBlock.Preceq U X.parent
  /-- FINAL 22:588–603: earlier matching rows occur above the entry. -/
  above : ∀ i ∈ honestSeats p c rho, ∀ W, FGBlock.Preceq W X.parent →
    (∃ row ∈ W.rows, RowNames p k row i y U) → FGBlock.Preceq U W.parent

/-- SO-COV height coverage from the same complete witness.
DC: SAME parent-or-child coverage; INTENTIONAL receipt and R6 premises. -/
def BatchCoverage (p : Params) (ΔF : Time) (k : RowKind) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (q y : Nat) (U X : FGBlock (Fin p.n)),
    BatchPrem p c E rho ΔF k q y U X →
    (heightView p X.parent).h = y → CoveredByChild p k X U y

/-- DC: SAME defining equation through the W height view. -/
theorem JustifiedCross_def (p : FGSA.Params) (W U : FGBlock (Fin p.n)) (y : Nat) :
    JustifiedCross p W U y =
      ((heightView p W.parent).h = y ∧ (heightView p W).h = y + 1 ∧
  (heightView p W).J = U ∧ (heightView p W).h_j = y) := rfl

/-- DC: SAME defining equation through the W height view. -/
theorem MixedCross_def (p : FGSA.Params) (W : FGBlock (Fin p.n)) (y : Nat) :
    MixedCross p W y =
      ((heightView p W.parent).h = y ∧ (heightView p W).h = y + 1 ∧
  (heightView p W).h_j < y) := rfl

/-- DC: SAME defining equation through the W height view. -/
theorem foldTrichotomy_def (p : FGSA.Params) (k : RowKind) :
    foldTrichotomy p k =
      (∀ (y : Nat) (U X : FGBlock (Fin p.n)), X ≠ .genesis → EntryAt p U y →
    FGBlock.Preceq U X.parent →
    ((heightView p X.parent).h = y → CoveredByChild p k X U y) →
    (k = .progress → U.slot + p.δt ≤ X.slot) →
    y + 1 ≤ (heightView p X).h ∧
    (k = .target → (∃ W, FGBlock.Preceq W X ∧ JustifiedCross p W U y) ∨
                   (∃ W, FGBlock.Preceq W X.parent ∧ MixedCross p W y))) := rfl

/-- DC: SAME defining equation through the W height view. -/
theorem StoredProgressConsume_def (p : FGSA.Params) :
    StoredProgressConsume p =
      (∀ (y : Nat) (U B X : FGBlock (Fin p.n)), EntryAt p U y → FGBlock.Preceq U B.parent →
    FGBlock.Preceq B X.parent → CoveredByChild p .progress B U y →
    (heightView p X.parent).h = y → U.slot + p.δt ≤ X.slot →
    (heightView p X).h = y + 1) := rfl

/-- DC: SAME exact signer and finality payload; INTENTIONAL fixed FG wire. -/
def FinRowNames (p : Params) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) : Prop :=
  row.signer = i ∧ row.finality_pair = some ⟨y, U.root⟩

/-- Plan item 1; blueprint 22 I6–I7. DC: INTENTIONAL exact retained key.
Parent bits and exact child rows cover a quorum before finality selection. -/
def FinalityCoveredByChild_W (p : Params) (X U : FGBlock (Fin p.n)) (y : Nat) : Prop :=
  ∃ e ∈ (Window.derive p p.K_W X.parent).W, e.j = y ∧ e.X = U ∧
    ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧ ∀ i ∈ Q,
      i ∈ e.Q ∨ ∃ row ∈ X.rows,
        FinRowNames p row i y U

/-- DC: SAME finality payload test on the complete signed row. -/
def FinalityNames (p : Params) (a : RowWire p.n) (y : Nat)
    (U : FGBlock (Fin p.n)) : Prop :=
  a.payload.finality_pair = some ⟨y, U.root⟩

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- Plan item 2, ruling m5. DC: INTENTIONAL exact-action quorum and W history.
This is a local producer input, with complete actual emissions. -/
structure FinalityBatchPrem_W (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin p.n)) : Prop where
  base : BaseSet p c E rho
  faultQ : FaultQ p.n (faulty rho).card
  deltaF : E.Δ ≤ ΔF
  rowsReceipt : TRowsReceipt p c E rho ΔF
  carrier : ∃ rows, HonestCarrier p c E rho X.slot (eraseFG X) rows ∧
    X.rows = rows.filterMap RowWire.toRow?
  after : q * p.R + kappaF p ΔF ≤ X.slot
  horizon : max (p.actionTime q) E.t_GST + ΔF ≤ SA.proposalTime p.toParams X.slot ∧
    SA.proposalTime p.toParams X.slot ≤ rho.horizon
  parent : ∃ st, proposalStateAt p c E rho X.slot = some st ∧
    FGSA.fgBlockOf st (eraseFG X).parent = some X.parent
  birth : ∃ B, FGBlock.Preceq B X.parent ∧
    KitFG.JustificationBirth p.E (Window.certificateHeight p p.K_W) B y U
  retainedOrCovered : RetainedW p X.parent y U ∨ CoveredW p X.parent y U
  batch : ∃ S : Finset (Fin p.n), S ⊆ honestSeats p c rho ∧ p.E.IsQuorum S ∧
    ∀ i ∈ S, ∃ j a,
      HonestRowAt p c E rho j (rho.seatOf (.base .fg) i) q a ∧
      RowComplete p c rho (rho.seatOf (.base .fg) i) a ∧
      a.auth = .seat .fg i ∧ FinalityNames p a y U ∧
      HeldBefore p c E rho (V2.D.proposerOf rho (fgsaInterface p c) X.slot) a
        (max (p.actionTime q) E.t_GST + ΔF) ∧
      heldAtProposal p c E rho X.slot a ∧
      (RetainedW p X.parent y U →
        Window.rowValidW (FGSA.parentFoldState p X.slot X.parent) a = true ∧
        ValidForParent p c E rho X.slot (eraseFG X) a)

/-- Plan item 3. DC: INTENTIONAL separate prior coverage and retained bitmap.
Contract only. Stage 5 supplies R7 and exact-row history. -/
def FinalityBatchCoverage_W (p : Params) (ΔF : Time) : Prop :=
  ∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
    (U X : FGBlock (Fin p.n)), FinalityBatchPrem_W p c E rho ΔF q y U X →
      CoveredW p X.parent y U ∨ FinalityCoveredByChild_W p X U y

/-- Plan item 4. DC: INTENTIONAL prefix consumption, with a real child. -/
structure PendingFold_W (p : Params) (y : Nat) (U X : FGBlock (Fin p.n)) : Prop where
  child : X ≠ .genesis
  cover : FinalityCoveredByChild_W p X U y

/-- DC: SAME defining equation for the exact entry bitmap. -/
theorem FinalityCoveredByChild_W_def (p : Params) (X U : FGBlock (Fin p.n)) (y : Nat) :
    FinalityCoveredByChild_W p X U y =
      (∃ e ∈ (Window.derive p p.K_W X.parent).W, e.j = y ∧ e.X = U ∧
        ∃ Q : Finset (Fin p.n), p.E.IsQuorum Q ∧ ∀ i ∈ Q,
          i ∈ e.Q ∨ ∃ row ∈ X.rows, FinRowNames p row i y U) := rfl

/-- DC: SAME exact decoded row equation. -/
theorem FinRowNames_def (p : Params) (row : Row (Fin p.n)) (i : Fin p.n)
    (y : Nat) (U : FGBlock (Fin p.n)) :
    FinRowNames p row i y U =
      (row.signer = i ∧ row.finality_pair = some ⟨y, U.root⟩) := rfl

/-- DC: SAME exact signed row equation. -/
theorem FinalityNames_def (p : Params) (a : RowWire p.n) (y : Nat) (U : FGBlock (Fin p.n)) :
    FinalityNames p a y U = (a.payload.finality_pair = some ⟨y, U.root⟩) := rfl

/-- DC: SAME equation for the statement-only batch contract. -/
theorem FinalityBatchCoverage_W_def (p : Params) (ΔF : Time) :
    FinalityBatchCoverage_W p ΔF =
      (∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (q y : Nat)
        (U X : FGBlock (Fin p.n)), FinalityBatchPrem_W p c E rho ΔF q y U X →
          CoveredW p X.parent y U ∨ FinalityCoveredByChild_W p X U y) := rfl

end AvailableChain.FGSA.Run
end
