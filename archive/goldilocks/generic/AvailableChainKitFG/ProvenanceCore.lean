module
public import AvailableChainKitFG.ProvenanceCoreDef
public import AvailableChainKitFG.Provenance
public import AvailableChainKitFG.CertificateCoreDef -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- An emitted height pair names the entry of its source projection. -/
theorem provenance_entry_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (hH : FGHeightLaws E H)
    (Λ : Record) (C : FGBlock V) (fp : Option FinalityPair)
    (h : Height) (T : BlockId) (t : Bool)
    (hemit : height_pair Λ (some ((H C).h, (H C).T_h.root)) fp = .vote h T t) :
    h = (H C).h ∧ T = (H C).T_h.root ∧ FGBlock.Preceq (H C).T_h C := by
  have hf := height_pair_vote_fields hemit
  injection hf with hf'
  injection hf' with h1 h2
  exact ⟨h1.symm, h2.symm, hH.entry_preceq C⟩

/-- Finality emission needs the guard at the supplied head and its target QC. -/
theorem provenance_finalityRow_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hH : FGHeightLaws E H)
    (Λ : Record) (Hd : FGBlock V) (p : FinalityPair)
    (hemit : finality_pair Λ (certificateHeadFields H f Hd) = some p) :
    p.height = (H Hd).h_j ∧ p.target = (H Hd).J.root ∧
      (f Hd).h_F < p.height ∧ TargetQCAt E Hd p.height (H Hd).J := by
  unfold finality_pair certificateHeadFields at hemit
  dsimp only at hemit
  split at hemit
  · rename_i hg
    cases hemit
    have hnz : (H Hd).h_j ≠ 0 := Nat.ne_zero_of_lt hg.1
    exact ⟨rfl, rfl, hg.1, hH.justification_certificate Hd hnz⟩
  · cases hemit

/-- The emission premise applies to the released pair. It permits suppression
and finality stripping and does not assert equality with a `createRow` call. -/
theorem provenance_finalityQC_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hH : FGHeightLaws E H)
    (faulty : Finset V) (hcap : E.weightOf faulty < E.q)
    (rows : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q) (p : FinalityPair)
    (hrows : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some p)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some p →
      ∃ Λ Hd, finality_pair Λ (certificateHeadFields H f Hd) = some p) :
    ∃ Hd, p.height = (H Hd).h_j ∧ p.target = (H Hd).J.root ∧
      TargetQCAt E Hd p.height (H Hd).J := by
  classical
  let matching := rows.filter (fun a => a.finality_pair = some p)
  have hw : ∀ i ∈ Q, ∃ a ∈ matching, a.signer = i := by
    intro i hi
    obtain ⟨a, ha, hai, hp⟩ := hrows i hi
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hp⟩, hai⟩
  obtain ⟨a, ha, haf⟩ := provenance_honestRow E faulty hcap matching Q hQ hw
  obtain ⟨harows, hp⟩ := Finset.mem_filter.mp ha
  obtain ⟨Λ, Hd, hem⟩ := hemit a harows haf hp
  obtain ⟨h1, h2, _, hqc⟩ := provenance_finalityRow_of_heightLaws E H f hH Λ Hd p hem
  exact ⟨Hd, h1, h2, hqc⟩

/-- The birth witness can precede the finalizing block's parent. -/
theorem provenance_finality_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D : FGBlock V) (hnz : (f D).h_F ≠ 0) :
    ∃ C, FGBlock.Preceq C D ∧ (H C).J = (f D).F ∧ (H C).h_j = (f D).h_F := by
  obtain ⟨C, W, hCW, hWD, hb, _, _, _⟩ := hc.finality_origin D hnz
  exact ⟨C, preceq_trans hCW.1 hWD, hb.2.2.2.2.1, hb.2.2.2.1⟩

end AvailableChain.KitFG
end
