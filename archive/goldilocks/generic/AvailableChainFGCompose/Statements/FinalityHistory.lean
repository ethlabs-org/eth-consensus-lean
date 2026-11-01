module
public import AvailableChainFGCompose.Statements.ResetCut -- shake: keep (Channels reads)

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}

/-- Full signed payload reads, with exact equations for a decoded row. -/
structure FGHistoryWireReads (S : FGSafetyReads P n Wire) where
  heightPair : Wire → NamedHeightPair
  finalityPair : Wire → Option FinalityPair
  signer : Wire → Option (Fin n)
  decode_height : ∀ a u, S.decode a = some u → heightPair a = u.height_pair
  decode_finality : ∀ a u, S.decode a = some u → finalityPair a = u.finality_pair
  decode_signer : ∀ a u, S.decode a = some u → signer a = some u.signer

def historyRowHeight (S : FGSafetyReads P n Wire) (D : FGHistoryWireReads S)
    (a : Wire) : Option Nat := match D.heightPair a with
  | .empty => none
  | .vote h _ _ => some h

def historyFinHeight (S : FGSafetyReads P n Wire) (D : FGHistoryWireReads S)
    (a : Wire) : Option Nat := (D.finalityPair a).map (·.height)

noncomputable def historyFaulty (S : FGSafetyReads P n Wire) (rho : V2.D.Run V P) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => safetyHolder S rho i ∉ rho.honest)

def eventTime (rho : V2.D.Run V P) (i : Nat) : Option Time :=
  rho.events[i]?.map V2.Event.time

variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (T : FGTiming)

/-- The same-node delivery, full wire, and earlier emission are retained. -/
def RawHistoryOrigin (D : FGHistoryWireReads S) : Prop :=
  ∀ i x B, HeldAt R E rho i x B → ∀ u ∈ chainRows B,
    ∃ a r, S.decode a = some u ∧ D.signer a = some u.signer ∧
      ∃ k o t, k < i ∧ rho.events[k]? = some (.deliver x o t) ∧
        ∀ z, RowSigner S rho D.signer a z → z ∈ rho.honest →
          HonestRowBefore S E rho T i z r a ∧ T.action r ≤ t

def EntryAt (H : FGHeightView (Fin n)) (U : FGBlock (Fin n)) (y : Nat) : Prop :=
  (H U).h = y ∧ (H U).T_h = U

def JustifiedCross (H : FGHeightView (Fin n)) (W U : FGBlock (Fin n))
    (y : Nat) : Prop :=
  (H W.parent).h = y ∧ (H W).h = y + 1 ∧ (H W).J = U ∧ (H W).h_j = y

def MixedCross (H : FGHeightView (Fin n)) (W : FGBlock (Fin n)) (y : Nat) : Prop :=
  (H W.parent).h = y ∧ (H W).h = y + 1 ∧ (H W).h_j < y

def NoMixedOnPath (H : FGHeightView (Fin n)) (X : FGBlock (Fin n)) (y : Nat) : Prop :=
  ∀ W, FGBlock.Preceq W X.parent → ¬ MixedCross H W y

/-- The target quorum has the exact parent bit or exact child row for each seat. -/
def TargetCoveredByChild (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (X U : FGBlock (Fin n)) (y : Nat) : Prop :=
  ∃ Q : Finset (Fin n), Ef.q ≤ Ef.weightOf Q ∧ ∀ i ∈ Q,
    i ∈ (H X.parent).target_participation ∨
      ∃ row ∈ X.rows, row.signer = i ∧ row.height_pair = .vote y U.root false

/-- The exact fold consequence supplied by a target-height producer. -/
def TargetJustification (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n)) : Prop :=
  ∀ y U X, X ≠ .genesis → EntryAt H U y → FGBlock.Preceq U X.parent →
    ((H X.parent).h = y → TargetCoveredByChild Ef H X U y) →
    NoMixedOnPath H X y → ∃ C, FGBlock.Preceq C X ∧ JustifiedCross H C U y

structure PreBatchPrem (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
    (H : FGHeightView (Fin n)) (q y : Nat) (U X : FGBlock (Fin n)) where
  schedule : V2.D.ScheduleWellFormed E rho
  fault_weight : Ef.weightOf (historyFaulty S rho) < Ef.q
  entry : EntryAt H U y
  path : FGBlock.Preceq U X.parent
  cut : Time
  early : cut ≤ T.action q
  rows : ChainRowsBefore R E rho X.parent cut
  noRow : ∀ j x r a h t, HonestRowAt S E rho T j x r a →
    historyRowHeight S D a = some h → y ≤ h → eventTime rho j = some t → T.action q ≤ t

structure FreshPrem (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
    (q y : Nat) (X : FGBlock (Fin n)) where
  schedule : V2.D.ScheduleWellFormed E rho
  fault_weight : Ef.weightOf (historyFaulty S rho) < Ef.q
  cut : Time
  early : cut ≤ T.action (q + 1)
  rows : ChainRowsBefore R E rho X cut
  noNextRow : ∀ j x r a h t, HonestRowAt S E rho T j x r a →
    historyRowHeight S D a = some h → y + 1 ≤ h →
      eventTime rho j = some t → T.action (q + 1) ≤ t
  noFinRow : ∀ j x r a h t, HonestRowAt S E rho T j x r a →
    historyFinHeight S D a = some h → y ≤ h →
      eventTime rho j = some t → T.action (q + 1) ≤ t

end AvailableChain.FGCompose
end
