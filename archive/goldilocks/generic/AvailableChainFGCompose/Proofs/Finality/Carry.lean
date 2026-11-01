module
public import AvailableChainFGCompose.Proofs.Finality.Batch
public import AvailableChainKitFG.WindowValidity -- shake: keep (r6w validity route for carriage)
public import AvailableChainKitFG.WindowHeightBridge -- shake: keep (P0d7a4 test bridge)

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (T : FGTiming) (E : Generic.Env V) (rho : V2.D.Run V P)
variable (I : V2.D.Interface P) (D : FGHistoryWireReads S)
variable (Ef : Electorate (Fin n)) (cfg : FGConfig) (K : Nat)
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire) (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)


/-- Both validity arms preserve the exact row before selected carriage is applied. -/
theorem terminalCarriage_general_W
    (hsel : TRowsSelect R S E rho T I carrier chainWireRows blockWireRows parentFG validFor)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (H : FGHeightView (Fin n)) (height : FGHeightLaws Ef H)
    (height_eq : H = KitFG.Window.certificateHeight Ef cfg K)
    (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
    (parentHeight_eq : ∀ nd s B, parentHeight nd s B = ((H B).h, (H B).T_h.root))
    (validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((S.decode a).isSome && ((S.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState Ef cfg K B s))).getD false))
    (q y sourceH : Nat) (A U X : FGBlock (Fin n)) (hbelow : y < sourceH)
    (carrierRows : ∃ wireRows, HonestCarrier E rho I carrier X.slot (R.erase X) wireRows ∧
      X.rows = wireRows.filterMap S.decode)
    (parent : ∃ nd, proposalStateAt E rho I X.slot = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent)
    (valid : ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) X.parent →
      ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true)
    (path : FGBlock.Preceq A X.parent) (sourceHeight : (H A).h = sourceH)
    (retainedOrCovered : KitFG.Window.RetainedW Ef cfg K X.parent y U ∨
      KitFG.Window.CoveredW Ef cfg K X.parent y U)
    (seats : Finset (Fin n)) (rows : Fin n → Wire) (quorum : Ef.IsQuorum seats)
    (emitted : ∀ i ∈ seats, ∃ j,
      HonestRowAt S E rho T j (safetyHolder S rho i) q (rows i) ∧
      D.signer (rows i) = some i ∧ historyRowHeight S D (rows i) = some sourceH ∧
      FinalityNames S D (rows i) y U)
    (heightEntry : ∀ i ∈ seats,
      namedEntry (D.heightPair (rows i)) = some (sourceH, (H A).T_h.root))
    (held : ∀ i ∈ seats, heldAtProposal R E rho I blockWireRows X.slot (rows i)) :
    KitFG.Window.CoveredW Ef cfg K X.parent y U ∨
      ((∀ i ∈ seats,
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) (rows i) ∧
        ((H X.parent).h = sourceH ∧
          HeightMatch E rho I (fun a => namedEntry (D.heightPair a)) parentFG parentHeight
            X.slot (R.erase X) (rows i) ∨
         ∃ row rowH, S.decode (rows i) = some row ∧
           historyRowHeight S D (rows i) = some rowH ∧
           y < rowH ∧ rowH < (H X.parent).h ∧
           SimplexFG.Window.staleUseful (KitFG.Window.parentState Ef cfg K X.parent X.slot)
             row = true ∧ row.finality_pair = some ⟨y, U.root⟩ ∧
           KitFG.Window.RetainedW Ef cfg K X.parent y U)) ∧
       FinalityCoveredByChild_W Ef cfg K X U y) := by
  rcases retainedOrCovered with hret | hcovered
  · obtain ⟨e, he, hej, heX⟩ := hret
    obtain ⟨wireRows, hc, hrows⟩ := carrierRows
    obtain ⟨nd, hnd, hpar⟩ := parent
    have hbound : sourceH ≤ (H X.parent).h := sourceHeight ▸ height.h_mono path
    have hparentHeight : (KitFG.Window.parentState Ef cfg K X.parent X.slot).h =
        (H X.parent).h := by rw [height_eq]; rfl
    have hparentEntry : (KitFG.Window.parentState Ef cfg K X.parent X.slot).T_h =
        (H X.parent).T_h := by rw [height_eq]; rfl
    have result : ∀ i ∈ seats,
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) (rows i) ∧
        ((H X.parent).h = sourceH ∧
          HeightMatch E rho I (fun a => namedEntry (D.heightPair a)) parentFG parentHeight
            X.slot (R.erase X) (rows i) ∨
         ∃ row rowH, S.decode (rows i) = some row ∧
           historyRowHeight S D (rows i) = some rowH ∧
           y < rowH ∧ rowH < (H X.parent).h ∧
           SimplexFG.Window.staleUseful (KitFG.Window.parentState Ef cfg K X.parent X.slot)
             row = true ∧ row.finality_pair = some ⟨y, U.root⟩ ∧
           KitFG.Window.RetainedW Ef cfg K X.parent y U) := by
      intro i hi
      obtain ⟨j, _, hauth, hh, hn⟩ := emitted i hi
      obtain ⟨row, hd⟩ := decode (rows i) i hauth
      have hp := D.decode_height (rows i) row hd
      have hf : row.finality_pair = some ⟨y, U.root⟩ :=
        (D.decode_finality (rows i) row hd).symm.trans hn
      have hvalid_r6w : SimplexFG.Window.r6w
          (KitFG.Window.parentState Ef cfg K X.parent X.slot) row = true →
          ValidForParent E rho I parentFG validFor X.slot (R.erase X) (rows i) := by
        intro hv
        refine ⟨nd, X.parent, hnd, hpar, ?_⟩
        rw [validFor_eq, hd]
        exact hv
      by_cases hsame : (H X.parent).h = sourceH
      · have hentry := height.entry_plateau path (sourceHeight.trans hsame.symm)
        have hm : namedEntry row.height_pair =
            some ((KitFG.Window.parentState Ef cfg K X.parent X.slot).h,
              (KitFG.Window.parentState Ef cfg K X.parent X.slot).T_h.root) := by
          rw [← hp, hparentHeight, hparentEntry, hsame, ← hentry]
          exact heightEntry i hi
        have matchRow : SimplexFG.Window.heightMatch
            (KitFG.Window.parentState Ef cfg K X.parent X.slot) row = true := by
          rw [SimplexFG.Window.heightMatch_def]
          cases hr : row.height_pair with
          | empty => rw [hr] at hm; cases hm
          | vote h B timeout =>
            rw [hr] at hm
            have keys := Prod.mk.inj (Option.some.inj hm)
            simp only [NamedHeightPair.matchesEntry, keys.1, keys.2, and_self, decide_true]
        refine ⟨hvalid_r6w ?_, Or.inl ⟨hsame, nd, X.parent, hnd, hpar, ?_⟩⟩
        · simp only [SimplexFG.Window.r6w_def, matchRow, Bool.true_or]
        · rw [parentHeight_eq, hsame, ← hentry]
          exact heightEntry i hi
      · have crossed : sourceH < (H X.parent).h := Nat.lt_of_le_of_ne hbound (Ne.symm hsame)
        have wm : SimplexFG.Window.windowMatch
            (KitFG.Window.parentState Ef cfg K X.parent X.slot) row = true := by
          rw [SimplexFG.Window.windowMatch_def, List.any_eq_true]
          exact ⟨e, he, by simp only [hej, heX, hf, decide_true]⟩
        have useful : SimplexFG.Window.staleUseful
            (KitFG.Window.parentState Ef cfg K X.parent X.slot) row = true := by
          delta historyRowHeight at hh
          rw [hp] at hh
          rw [SimplexFG.Window.staleUseful_def, hf]
          cases hr : row.height_pair with
          | empty => rw [hr] at hh; cases hh
          | vote h B timeout =>
            rw [hr] at hh
            have hh := Option.some.inj hh
            simp only [hh, hparentHeight, hbelow, crossed, and_self, decide_true, wm,
              Bool.true_and]
        refine ⟨hvalid_r6w ?_, Or.inr ⟨row, sourceH, hd, ?_, hbelow, crossed,
          useful, hf, e, he, hej, heX⟩⟩
        · simp only [SimplexFG.Window.r6w_def, useful, Bool.or_true]
        · exact (emitted i hi).choose_spec.2.2.1
    right
    refine ⟨result, e, he, hej, heX, seats, quorum, ?_⟩
    intro i hi
    obtain ⟨j, ha, hauth, _, hn⟩ := emitted i hi
    exact finalityRow_bit_or_carried_W R S T E rho I D Ef cfg K carrier chainWireRows
      blockWireRows parentFG validFor hsel hne hK decode occurrence X U y wireRows hc
      hrows ⟨nd, hnd, hpar⟩ valid e he hej heX i j q (rows i) ha hauth hn
      (result i hi).1 (held i hi)
  · exact Or.inl hcovered


/-- Specialize general carriage to the actual fresh finality rows. -/
theorem terminalCarriage_W_of_tRowsSelect
    (hsel : TRowsSelect R S E rho T I carrier chainWireRows blockWireRows parentFG validFor)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (O : FGObservationReads R) (height : FGHeightLaws Ef O.height)
    (height_eq : O.height = KitFG.Window.certificateHeight Ef cfg K)
    (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
    (parentHeight_eq : ∀ nd s B, parentHeight nd s B = ((O.height B).h, (O.height B).T_h.root))
    (validFor_eq : ∀ nd s B a, validFor nd s B a =
      ((S.decode a).isSome && ((S.decode a).map
        (SimplexFG.Window.r6w (KitFG.Window.parentState Ef cfg K B s))).getD false))
    (validWire : Wire → Bool) (ΔF : Time) (q y : Nat) (A U X : FGBlock (Fin n))
    (h : TerminalCarriagePrem_W R S O T E rho I D Ef cfg K validWire
      carrier blockWireRows parentFG ΔF q y A U X)
    (valid : ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) X.parent →
      ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true) :
    KitFG.Window.CoveredW Ef cfg K X.parent y U ∨
      ((∀ i ∈ h.seats,
        ValidForParent E rho I parentFG validFor X.slot (R.erase X) (h.rows i) ∧
        ((O.height X.parent).h = y + 1 ∧
          HeightMatch E rho I (fun a => namedEntry (D.heightPair a)) parentFG parentHeight
            X.slot (R.erase X) (h.rows i) ∨
         ∃ row rowH, S.decode (h.rows i) = some row ∧
           historyRowHeight S D (h.rows i) = some rowH ∧
           y < rowH ∧ rowH < (O.height X.parent).h ∧
           SimplexFG.Window.staleUseful (KitFG.Window.parentState Ef cfg K X.parent X.slot)
             row = true ∧ row.finality_pair = some ⟨y, U.root⟩ ∧
           KitFG.Window.RetainedW Ef cfg K X.parent y U)) ∧
       FinalityCoveredByChild_W Ef cfg K X U y) := by
  obtain ⟨_, hquorum, hfresh⟩ := h.fresh
  apply terminalCarriage_general_W R S T E rho I D Ef cfg K carrier chainWireRows
    blockWireRows parentFG validFor hsel hne hK decode occurrence O.height height height_eq
    parentHeight parentHeight_eq validFor_eq q y (y + 1) A U X (Nat.lt_succ_self y)
    h.carrier h.parent valid h.path h.freshHeight h.retainedOrCovered h.seats h.rows hquorum
  · intro i hi
    obtain ⟨j, C, ha, _, hauth, hheight, hn, _, _, _⟩ := hfresh i hi
    exact ⟨j, ha, hauth, hheight, hn⟩
  · exact h.heightEntry
  · intro i hi
    exact (h.receipt i hi).2

end AvailableChain.FGCompose
end
