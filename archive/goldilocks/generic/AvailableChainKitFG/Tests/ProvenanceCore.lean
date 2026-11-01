module
public import AvailableChainKitFG.ProvenanceCore
public import AvailableChainKitFG.CertificateSimplex -- shake: keep (instance checks in examples)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.ProvenanceCore

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- The existing honest-row statement needs no concrete fold or client.
omit [DecidableEq V] [RowCodec V] in
theorem provenance_generic_honest_row_test (E : Electorate V) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (rows : Finset (Row V)) (Q : Finset V)
    (hQ : E.IsQuorum Q) (hw : ∀ i ∈ Q, ∃ a ∈ rows, a.signer = i) :
    ∃ a ∈ rows, a.signer ∉ faulty :=
  provenance_honestRow E faulty hcap rows Q hQ hw

-- A released pair at or below current finality cannot satisfy emission.
theorem provenance_stale_emission_rejected_test (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (Λ : Record) (Hd : FGBlock V) (p : FinalityPair) (hstale : p.height ≤ (f Hd).h_F) :
    finality_pair Λ (certificateHeadFields H f Hd) ≠ some p := by
  intro hemit
  have h := (provenance_finalityRow_of_heightLaws E H f hc.height Λ Hd p hemit).2.2.1
  exact (Nat.not_lt_of_ge hstale) h

-- Use the bundle and the explicit released-pair premise for QC provenance.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hc : FGChainCertificate E H f r)
    (faulty : Finset V) (hcap : E.weightOf faulty < E.q)
    (rows : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q) (p : FinalityPair)
    (hw : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some p)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some p →
      ∃ Λ Hd, finality_pair Λ (certificateHeadFields H f Hd) = some p) :
    ∃ Hd, p.height = (H Hd).h_j ∧ p.target = (H Hd).J.root ∧
      TargetQCAt E Hd p.height (H Hd).J :=
  provenance_finalityQC_of_heightLaws E H f hc.laws.height faulty hcap rows Q hQ p hw hemit

private def pcFinalOne : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

-- The same pair is emitted at B1 and rejected after it has finalized.
private theorem provenance_stale_head_fixture_test :
    finality_pair Record.initial
        (certificateHeadFields (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) B1) =
      some ⟨1, genesisRoot⟩ ∧
    finality_pair Record.initial
        (certificateHeadFields (simplexHeightView E4 cfg1)
          (simplexFinalityView E4 cfg1) pcFinalOne) = none := by decide

-- Genesis at height zero cannot stand for the emitted height-one key.
example : finality_pair Record.initial
    (certificateHeadFields (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) B1) ≠
      some ⟨0, genesisRoot⟩ := by decide

-- A prior timeout also prevents finality emission.
example : finality_pair (Record.initial.with_timeout 1)
    (certificateHeadFields (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) B1) =
      none := by decide

-- The field-level entry companion accepts the projected source directly.
example : (1 : Height) = (simplexHeightView E4 cfg1 .genesis).h ∧
    genesisRoot = (simplexHeightView E4 cfg1 .genesis).T_h.root ∧
    FGBlock.Preceq (simplexHeightView E4 cfg1 .genesis).T_h .genesis :=
  provenance_entry_of_heightLaws E4 _ (simplexHeightLaws E4 cfg1)
    Record.initial .genesis none 1 genesisRoot false (by decide)

-- Instance check: provenance_entry_of_heightLaws.
example (E : Electorate V) (cfg : FGConfig)
    (Λ : Record) (C : FGBlock V) (fp : Option FinalityPair)
    (h : Height) (T : BlockId) (t : Bool)
    (hemit : height_pair Λ (some ((derive E cfg C).h, (derive E cfg C).T_h.root)) fp =
      .vote h T t) :
    h = (derive E cfg C).h ∧ T = (derive E cfg C).T_h.root ∧
      FGBlock.Preceq (derive E cfg C).T_h C :=
  provenance_entry_of_heightLaws E _ (simplexHeightLaws E cfg) Λ C fp h T t hemit

-- Instance check: provenance_finalityRow_of_heightLaws.
example (E : Electorate V) (cfg : FGConfig)
    (Λ : Record) (Hd : FGBlock V) (p : FinalityPair)
    (hemit : finality_pair Λ (HeadFields.ofBlock E cfg Hd) = some p) :
    p.height = (derive E cfg Hd).h_j ∧ p.target = (derive E cfg Hd).J.root ∧
      (derive E cfg Hd).h_F < p.height ∧
      TargetQCAt E Hd p.height (derive E cfg Hd).J :=
  provenance_finalityRow_of_heightLaws E _ (simplexFinalityView E cfg) (simplexHeightLaws E cfg)
    Λ Hd p hemit

-- Instance check: provenance_finalityQC_of_heightLaws.
example (E : Electorate V) (cfg : FGConfig)
    (faulty : Finset V) (hcap : E.weightOf faulty < E.q)
    (rows : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q) (p : FinalityPair)
    (hrows : ∀ j ∈ Q, ∃ a ∈ rows, a.signer = j ∧ a.finality_pair = some p)
    (hemit : ∀ a ∈ rows, a.signer ∉ faulty → a.finality_pair = some p →
      ∃ Λ Hd, finality_pair Λ (HeadFields.ofBlock E cfg Hd) = some p) :
    ∃ Hd, p.height = (derive E cfg Hd).h_j ∧ p.target = (derive E cfg Hd).J.root ∧
      TargetQCAt E Hd p.height (derive E cfg Hd).J :=
  provenance_finalityQC_of_heightLaws E _ (simplexFinalityView E cfg) (simplexHeightLaws E cfg)
    faulty hcap rows Q hQ p hrows hemit

-- Instance check: provenance_finality_of_certificate.
example (E : Electorate V) (cfg : FGConfig)
    (D : FGBlock V) (hnz : (derive E cfg D).h_F ≠ 0) :
    ∃ C, FGBlock.Preceq C D ∧ (derive E cfg C).J = (derive E cfg D).F ∧
      (derive E cfg C).h_j = (derive E cfg D).h_F :=
  provenance_finality_of_certificate E _ _ (simplexCertificateLaws E cfg) D hnz

-- A concrete QC consists of the three released finality rows of pcFinalOne.
private theorem provenance_concrete_finalityQC_test :
    ∃ Hd : FGBlock (Fin 4),
      (1 : Height) = (simplexHeightView E4 cfg1 Hd).h_j ∧
      genesisRoot = (simplexHeightView E4 cfg1 Hd).J.root ∧
      TargetQCAt E4 Hd 1 (simplexHeightView E4 cfg1 Hd).J := by
  apply provenance_finalityQC_of_heightLaws E4 (simplexHeightView E4 cfg1)
    (simplexFinalityView E4 cfg1) (simplexHeightLaws E4 cfg1)
    ∅ (by decide) pcFinalOne.rows.toFinset {0, 1, 2} (by change 3 ≤ 3; decide) ⟨1, genesisRoot⟩
  · decide
  · intro _ _ _ _
    exact ⟨Record.initial, B1, by decide⟩

#print axioms provenance_concrete_finalityQC_test
#print axioms provenance_honestRow
#print axioms provenance_generic_honest_row_test
#print axioms provenance_stale_emission_rejected_test
#print axioms provenance_stale_head_fixture_test

#print axioms certificateHeadFields_def
#print axioms provenance_entry_of_heightLaws
#print axioms provenance_finalityRow_of_heightLaws
#print axioms provenance_finalityQC_of_heightLaws
#print axioms provenance_finality_of_certificate

end AvailableChain.KitFG.Tests.ProvenanceCore
end
