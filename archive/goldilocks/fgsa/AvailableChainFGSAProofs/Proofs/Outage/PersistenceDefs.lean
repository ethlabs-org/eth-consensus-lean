module
public import AvailableChainFGSAClaims.Statements.Channels

public import AvailableChainFGSARun.Statements.Roots

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §3.2. Class (iii).
DC: INTENTIONAL; all earlier honest action sources, including sleeping ticks. -/
structure OutageSourceHistory (B : Block) (i : Nat) : Prop where
  history : ∀ k x r C, k < i → x ∈ rho.honest →
    rho.events[k]? = some (.tick x (p.actionTime r)) →
    actionSource p c E rho x r = some (some C) → Block.Compatible C B

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
O-INDUCT plan §3.2. Class (iii). DC: INTENTIONAL; defining equation. -/
theorem OutageSourceHistory_def (B : Block) (i : Nat) :
    OutageSourceHistory p c E rho B i =
      (∀ k x r C, k < i → x ∈ rho.honest →
        rho.events[k]? = some (.tick x (p.actionTime r)) →
        actionSource p c E rho x r = some (some C) → Block.Compatible C B) := by
  apply propext
  exact ⟨fun h => h.history, fun h => ⟨h⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. Blueprint 03 §8.3; O-INDUCT plan §3.2. Class (iii).
DC: INTENTIONAL; compatibility of names is a derived history view. -/
structure OutageNamedHistory (β : FGBlock (Fin p.n)) (i : Nat) : Prop where
  history : ∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
    HonestRowBefore p c E rho i y r a →
    namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
    RootBlockInRun p c E rho (eraseFG e) →
    FGBlock.Preceq e β ∨ FGBlock.Preceq β e

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. O-INDUCT plan §3.2. Class (iii). DC: INTENTIONAL; defining equation. -/
theorem OutageNamedHistory_def (β : FGBlock (Fin p.n)) (i : Nat) :
    OutageNamedHistory p c E rho β i =
      (∀ y r (a : RowWire p.n) (e : FGBlock (Fin p.n)),
        HonestRowBefore p c E rho i y r a →
        namedEntry a.payload.height_pair = some ((heightView p e).h, e.root) →
    RootBlockInRun p c E rho (eraseFG e) →
        FGBlock.Preceq e β ∨ FGBlock.Preceq β e) := by
  apply propext
  exact ⟨fun h => h.history, fun h => ⟨h⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.2; O-INDUCT plan §3.3. Class (iii).
DC: INTENTIONAL; the selected row form avoids a repeated lease lookup.
CStoreInv.leaseKeys gives the equivalent leaseOf read. -/
structure OutageProtection (B : Block) (j : Slot) (st : State p.n) : Prop where
  cover : Block.Preceq B st.base.stableRecord
  protect : Block.Preceq B (eraseFG st.fg.F) ∨
    ∃ dl, (B, SA.releaseThreshold p.toParams, dl) ∈ st.base.obligations ∧
      SA.gateTime p.toParams j + L p ≤ dl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
O-INDUCT plan §3.3. Class (iii). DC: INTENTIONAL; defining equation. -/
theorem OutageProtection_def (B : Block) (j : Slot) (st : State p.n) :
    OutageProtection p B j st =
      (Block.Preceq B st.base.stableRecord ∧
        (Block.Preceq B (eraseFG st.fg.F) ∨
          ∃ dl, (B, SA.releaseThreshold p.toParams, dl) ∈ st.base.obligations ∧
            SA.gateTime p.toParams j + L p ≤ dl)) := by
  apply propext
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 03 §8.3; O-INDUCT plan §3.2. Class (iii).
DC: INTENTIONAL; actual honest HEADs and proposal parents after the cut. -/
structure OutageDutyHistory (B : Block) (j : Slot) (i : Nat) : Prop where
  history : ∀ k y t o, k < i → y ∈ rho.honest → SA.gateTime p.toParams j ≤ t →
    rho.events[k]? = some (.tick y t) → o ∈ V2.D.Run.emitsAt E rho k →
    (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
    (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
O-INDUCT plan §3.2. Class (iii). DC: INTENTIONAL; defining equation. -/
theorem OutageDutyHistory_def (B : Block) (j : Slot) (i : Nat) :
    OutageDutyHistory p c E rho B j i =
      (∀ k y t o, k < i → y ∈ rho.honest → SA.gateTime p.toParams j ≤ t →
        rho.events[k]? = some (.tick y t) → o ∈ V2.D.Run.emitsAt E rho k →
        (∀ H, HeadTargetAtEmission p c E rho y o t H → Block.Preceq B H) ∧
        (∀ N, o.payload = .proposal N → Block.Preceq B N.parent.erase)) := by
  apply propext
  exact ⟨fun h => h.history, fun h => ⟨h⟩⟩

end AvailableChain.FGSA.Run
end
