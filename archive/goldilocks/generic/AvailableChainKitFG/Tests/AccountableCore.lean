module
public import AvailableChainKitFG.AccountableCore
public import AvailableChainKitFG.CertificateSimplex -- shake: keep (instance checks in examples)

public section

/-! ROOT-DIGEST W3: safety tests use roots on the compared chains. -/

namespace AvailableChain.KitFG.Tests.AccountableCore

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- The complete chain certificate supplies the shared safety core.
theorem accountable_certificate_bundle_test (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (r : FGSelectionView V)
    (hc : FGChainCertificate E H f r) (B₁ B₂ : FGBlock V) (hroots : RootInjectiveOn B₁ B₂) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (f B₁).F (f B₂).F = true :=
  slashableWeight_or_finalized_compatible_of_certificate E H f hc.laws B₁ B₂ hroots

-- The safety argument needs no selection, retention, capacity, or timing premise.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hh : (f B).h_F < (H W).h) (hfork : ¬ FGBlock.Preceq (f B).F W) :
    HasE1WeightBetween E (chainRows B) (chainRows W) :=
  (e1Weight_or_finalized_preceq_of_certificate E H f hc B W hroots hh).resolve_right hfork

-- Unequal justified blocks at one height give slashable evidence.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (B₁ B₂ : FGBlock V) (hroots : RootInjectiveOn B₁ B₂)
    (hh : (H B₁).h_j = (H B₂).h_j) (hne : (H B₁).J ≠ (H B₂).J) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) :=
  (slashableWeight_or_justified_eq_of_certificate E H f hc B₁ B₂ hroots hh).resolve_right hne

-- The exact finality QC remains available when before has no retained entry.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hc : FGChainCertificate E H f r)
    (B : FGBlock V) (_hempty : r.before B = []) (hnz : (f B).h_F ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q,
      ∃ a ∈ chainRows B, a.signer = i ∧
        a.finality_pair = some ⟨(f B).h_F, (f B).F.root⟩ := by
  obtain ⟨_, _, rfl, Q, hQ, hw⟩ := finality_certificate_of_certificate E H f hc.laws B hnz
  refine ⟨Q, hQ, fun i hi => ?_⟩
  obtain ⟨carrier, a, hcarrier, ha, hai, hpair⟩ := hw i hi
  exact ⟨a, mem_chainRows_of_carrier hcarrier ha, hai, hpair⟩

-- The zero-finality case gives genesis ancestry directly.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (B W : FGBlock V) (hz : (f B).h_F = 0) :
    FGBlock.Preceq (f B).F W := by
  rw [hc.finalized_zero B hz]
  exact genesis_preceq W

-- The concrete corollaries use the LF2 instance and keep the concrete chain types.
example (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  slashableWeight_or_finalized_preceq_of_certificate E _ _ (simplexCertificateLaws E cfg) B W hroots
      hh

example (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V) (hroots : RootInjectiveOn B₁ B₂) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true :=
  slashableWeight_or_finalized_compatible_of_certificate E _ _ (simplexCertificateLaws E cfg) B₁ B₂
      hroots

-- Both certificate keys for genesis reach the shared records.
example : (simplexFinalityView E4 cfg1 .genesis).h_F = 0 ∧
    (simplexHeightView E4 cfg1 B1).h_j = 1 := by decide

-- Instance check: justification_certificate_rows_of_heightLaws.
example
    (E : Electorate V) (cfg : FGConfig) (D : FGBlock V)
    (hnz : (derive E cfg D).h_j ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ a ∈ chainRows D, a.signer = i ∧
      a.height_pair = .vote (derive E cfg D).h_j (derive E cfg D).J.root false :=
  justification_certificate_rows_of_heightLaws E _ (simplexCertificateLaws E cfg).height D hnz

-- Instance check: slashableWeight_or_justified_eq_of_certificate.
example
    (E : Electorate V) (cfg : FGConfig) (B₁ B₂ : FGBlock V) (hroots : RootInjectiveOn B₁ B₂)
    (hh : (derive E cfg B₁).h_j = (derive E cfg B₂).h_j) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      (derive E cfg B₁).J = (derive E cfg B₂).J :=
  slashableWeight_or_justified_eq_of_certificate E _ _ (simplexCertificateLaws E cfg) B₁ B₂ hroots
      hh

-- Instance check: e1Weight_or_finalized_preceq_of_certificate.
example
    (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasE1WeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  e1Weight_or_finalized_preceq_of_certificate E _ _ (simplexCertificateLaws E cfg) B W hroots hh

-- Instance check: slashableWeight_or_finalized_preceq_of_certificate.
example
    (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hh : (derive E cfg B).h_F < (derive E cfg W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (derive E cfg B).F W :=
  slashableWeight_or_finalized_preceq_of_certificate E _ _ (simplexCertificateLaws E cfg) B W hroots
      hh

-- Instance check: e1Weight_or_finalized_compatible_of_le_of_certificate.
example
    (E : Electorate V) (cfg : FGConfig)
    (B₁ B₂ : FGBlock V) (hroots : RootInjectiveOn B₁ B₂)
    (hle : (derive E cfg B₁).h_F ≤ (derive E cfg B₂).h_F) :
    HasE1WeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true :=
  e1Weight_or_finalized_compatible_of_le_of_certificate E _ _
    (simplexCertificateLaws E cfg) B₁ B₂ hroots hle

-- Instance check: slashableWeight_or_finalized_compatible_of_certificate.
example
    (E : Electorate V) (cfg : FGConfig)
    (B₁ B₂ : FGBlock V) (hroots : RootInjectiveOn B₁ B₂) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (derive E cfg B₁).F (derive E cfg B₂).F = true :=
  slashableWeight_or_finalized_compatible_of_certificate E _ _
    (simplexCertificateLaws E cfg) B₁ B₂ hroots

#print axioms accountable_certificate_bundle_test
#print axioms finalized_preceq_chain_of_certificate
#print axioms finalized_below_height_of_certificate
#print axioms finality_certificate_of_certificate
#print axioms justification_certificate_rows_of_heightLaws
#print axioms slashableWeight_or_justified_eq_of_certificate
#print axioms e1Weight_or_finalized_preceq_of_certificate
#print axioms slashableWeight_or_finalized_preceq_of_certificate
#print axioms e1Weight_or_finalized_compatible_of_le_of_certificate
#print axioms slashableWeight_or_finalized_compatible_of_certificate

end AvailableChain.KitFG.Tests.AccountableCore
end
