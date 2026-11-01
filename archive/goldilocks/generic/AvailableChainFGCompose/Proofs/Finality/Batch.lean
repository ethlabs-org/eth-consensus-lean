module
public import AvailableChainFGCompose.Statements.FinalityRows
public import AvailableChainKitFG.WindowRetention

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

/-- Selection either carries this exact signed row or retains its exact parent effect. -/
theorem finalityRow_bit_or_carried_W
    (hsel : TRowsSelect R S E rho T I carrier chainWireRows blockWireRows parentFG validFor)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (X U : FGBlock (Fin n)) (y : Nat) (wireRows : List Wire)
    (hc : HonestCarrier E rho I carrier X.slot (R.erase X) wireRows)
    (hrows : X.rows = wireRows.filterMap S.decode)
    (hparent : ∃ nd, proposalStateAt E rho I X.slot = some nd ∧
      parentFG nd (R.erase X).parent = some X.parent)
    (valid : ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) X.parent →
      ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true)
    (e : SimplexFG.Window.Entry (Fin n))
    (he : e ∈ (SimplexFG.Window.derive Ef cfg K X.parent).W)
    (hej : e.j = y) (heX : e.X = U) (i : Fin n) (j r : Nat) (a : Wire)
    (ha : HonestRowAt S E rho T j (safetyHolder S rho i) r a)
    (hauth : D.signer a = some i) (hnames : FinalityNames S D a y U)
    (hvalid : ValidForParent E rho I parentFG validFor X.slot (R.erase X) a)
    (hheld : heldAtProposal R E rho I blockWireRows X.slot a) :
    i ∈ e.Q ∨ ∃ row ∈ X.rows, FinRowNames row i y U := by
  obtain ⟨u, hu⟩ := decode a i hauth
  have hi : u.signer = i := Option.some.inj ((D.decode_signer a u hu).symm.trans hauth)
  have hp : u.finality_pair = some ⟨y, U.root⟩ :=
    (D.decode_finality a u hu).symm.trans hnames
  rcases hsel X.slot (R.erase X) wireRows j _ r a hc ha hvalid hheld with hcarry | hchain
  · exact Or.inr ⟨u, hrows ▸ List.mem_filterMap.mpr ⟨a, hcarry, hu⟩, hi, hp⟩
  · obtain ⟨nd, hnd, hchain⟩ := hchain
    obtain ⟨par, hpar, hlookup⟩ := hparent
    have hh := Option.some.inj (hpar.symm.trans hnd)
    subst par
    obtain ⟨W, hW, hm⟩ := occurrence X.slot (R.erase X) X.parent nd a u
      hnd hlookup hchain hu
    left
    cases W with
    | genesis => exact (List.not_mem_nil hm).elim
    | node B s root body rs =>
      rw [← hi]
      exact KitFG.Window.window_exact_row_no_missing_effect Ef cfg K hne hK
        X.parent y U e he hej heX valid B s root body rs hW u hm hp


/-- The retained case is derived seat by seat from selection and exact row effects. -/
theorem finalityBatchCoverage_W_of_tRowsSelect
    (hsel : TRowsSelect R S E rho T I carrier chainWireRows blockWireRows parentFG validFor)
    (hne : ¬ Ef.IsQuorum ∅) (hK : 2 ≤ K)
    (decode : ∀ a i, D.signer a = some i → ∃ u, S.decode a = some u)
    (occurrence : ∀ s (Q : Block) H nd a u,
      proposalStateAt E rho I s = some nd → parentFG nd Q.parent = some H →
      a ∈ chainWireRows nd Q.parent → S.decode a = some u →
      ∃ W, FGBlock.Preceq W H ∧ u ∈ W.rows)
    (rowValid : SimplexFG.Window.State (Fin n) → Wire → Bool) (validWire : Wire → Bool)
    (ΔF : Time) (q y : Nat) (U X : FGBlock (Fin n))
    (h : FinalityBatchPrem_W R S T E rho I D Ef cfg K validWire
      carrier blockWireRows parentFG validFor rowValid ΔF q y U X)
    (valid : ∀ B s root body rs, FGBlock.Preceq (.node B s root body rs) X.parent →
      ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧
        SimplexFG.Window.r6w (SimplexFG.Window.derive Ef cfg K B) a = true) :
    KitFG.Window.CoveredW Ef cfg K X.parent y U ∨
      FinalityCoveredByChild_W Ef cfg K X U y := by
  rcases h.retainedOrCovered with hret | hcovered
  · obtain ⟨e, he, hej, heX⟩ := hret
    obtain ⟨wireRows, hc, hrows⟩ := h.carrier
    obtain ⟨seats, _, hquorum, hseat⟩ := h.batch
    right
    refine ⟨e, he, hej, heX, seats, hquorum, ?_⟩
    intro i hi
    obtain ⟨j, a, ha, _, hauth, hnames, _, hheld, hvalid⟩ := hseat i hi
    exact finalityRow_bit_or_carried_W R S T E rho I D Ef cfg K carrier
      chainWireRows blockWireRows parentFG validFor hsel hne hK decode occurrence
      X U y wireRows hc hrows h.parent valid e he hej heX i j q a
      ha hauth hnames (hvalid ⟨e, he, hej, heX⟩).2 hheld
  · exact Or.inl hcovered

end AvailableChain.FGCompose
end
