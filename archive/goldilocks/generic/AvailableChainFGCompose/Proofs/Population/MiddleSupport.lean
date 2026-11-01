module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

/-- Construct the batch from actual matching rows and exact parent-read effects. -/
theorem kmid_batchPrem_holder {Body : Type} (cfg : FGConfig) (K : Nat)
    (height : FGHeightLaws Ef O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (decodeProposal : P.Object → Option (Slot × Body))
    (bodyErase : Body → Block) (bodyRows : Body → List Wire)
    (blockWireRows : P.State → List Wire)
    (parentFG : P.State → Block → Option (FGBlock (Fin n)))
    (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
    (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)
    (valid : Wire → Bool) (ΔF : Time)
    (hs : V2.D.ScheduleWellFormed E rho)
    (hweight : Ef.weightOf (historyFaulty S rho) < Ef.q)
    (linked : Function.Injective (safetyHolder S rho))
    (Q : Finset (Fin n)) (honestQ : ∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest)
    (quorum : Ef.q ≤ Ef.weightOf Q)
    (deltaF : E.Δ ≤ ΔF) (receipt : TRowsReceipt R S E rho T blockWireRows ΔF)
    (q y : Nat) (U X : FGBlock (Fin n))
    (horizon : max (T.action q) E.t_GST + ΔF ≤ T.proposal X.slot ∧
      T.proposal X.slot ≤ rho.horizon)
    (carrier : ∃ rows, HonestCarrier E rho I
      (kernelCarrier decodeProposal bodyErase bodyRows) X.slot (R.erase X) rows ∧
      X.rows = rows.filterMap S.decode)
    (nd : P.State) (hnd : proposalStateAt E rho I X.slot = some nd)
    (lookup : parentFG nd (R.erase X).parent = some X.parent)
    (hparTF : X.parent ∈ (R.core nd).fg.TF)
    (closed : ∀ B ∈ (R.core nd).fg.TF, B.parent ∈ (R.core nd).fg.TF)
    (roots : ViewRootInj (R.core nd).fg.TF)
    (validRows : ∀ W ∈ (R.core nd).fg.TF, ∀ row ∈ W.rows,
      SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K W.parent) row = true)
    (parentEq : parentHeight nd X.slot X.parent =
      ((O.height X.parent).h, (O.height X.parent).T_h.root))
    (matchValid : ∀ a, valid a = true →
      namedEntry (D.heightPair a) = some (parentHeight nd X.slot X.parent) →
      validFor nd X.slot X.parent a = true)
    (after : q * T.roundSlots + 2 ≤ X.slot) (entry : EntryAt O.height U y)
    (path : FGBlock.Preceq U X.parent) (hpar : (O.height X.parent).h = y)
    (rows : ∀ i ∈ Q, ∃ j r a,
      r ≤ q ∧ HonestRowAt S E rho T j (safetyHolder S rho i) r a ∧
      RowComplete S rho D.signer valid (safetyHolder S rho i) a ∧
      NamesEntry (pair := D.heightPair) .target a y U) :
    BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
      parentFG parentHeight validFor ΔF .target q y U X := by
  classical
  have hT : (O.height X.parent).T_h = U :=
    ((height.entry_plateau path (entry.1.trans hpar.symm)).symm.trans entry.2)
  refine ⟨hs, hweight, deltaF, receipt, horizon, carrier, after, ?_, entry, path, ?_⟩
  · refine ⟨Q, honestQ, quorum, ?_⟩
    intro i hi
    obtain ⟨j, r, a, hr, ha, hcomp, hnames⟩ := rows i hi
    obtain ⟨i', hauth, hseat⟩ := hcomp.2
    obtain rfl := linked hseat
    have hmatch : namedEntry (D.heightPair a) = some (parentHeight nd X.slot X.parent) := by
      rw [parentEq, hpar, hT]
      change D.heightPair a = .vote y U.root false at hnames
      rw [hnames]
      rfl
    exact ⟨j, r, a, T.action r, hr, ha, hauth, hnames, kmid_event_time S T E rho ha,
      rfl, ⟨nd, X.parent, hnd, lookup, matchValid a hcomp.1 hmatch⟩,
      ⟨nd, X.parent, hnd, lookup, hmatch⟩⟩
  · intro i _ W hW hrow
    exact kmid_rows_above_entry R O Ef cfg K height height_eq nd closed roots validRows
      .target y U X.parent hparTF hpar path i W hW hrow

end AvailableChain.FGCompose
end
