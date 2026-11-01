module
public import AvailableChainKitFG.Accountable
public import AvailableChainKitFG.CertificateCoreDef

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Finality is on the carrier chain, by the record's anchor order. -/
theorem finalized_preceq_chain_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B : FGBlock V) : FGBlock.Preceq (f B).F B :=
  preceq_trans (hc.finalized_preceq_justified B)
    (preceq_trans (hc.height.justified_preceq_entry B) (hc.height.entry_preceq B))

/-- A finalized height is below the carrier's current height. -/
theorem finalized_below_height_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B : FGBlock V) : (f B).h_F < (H B).h :=
  Nat.lt_of_le_of_lt (hc.heights_ordered B) (hc.height.justified_below_height B)

/-- Extract the exact historical QC. No current bit set or selection list is read. -/
theorem finality_certificate_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D : FGBlock V) (hnz : (f D).h_F ≠ 0) :
    ∃ F : FGBlock V, FGBlock.Preceq F D ∧ F = (f D).F ∧
      ∃ Q : Finset V, E.IsQuorum Q ∧
        ∀ i ∈ Q, ∃ carrier : FGBlock V, ∃ a : Row V,
          FGBlock.Preceq carrier D ∧ a ∈ carrier.rows ∧ a.signer = i ∧
          a.finality_pair = some ⟨(f D).h_F, F.root⟩ := by
  obtain ⟨C, W, _, hWD, _, _, _, Q, hQ, hw⟩ := hc.finality_origin D hnz
  refine ⟨(f D).F, finalized_preceq_chain_of_certificate E H f hc D, rfl, Q, hQ, ?_⟩
  intro i hi
  obtain ⟨carrier, a, _, hcarrier, ha, hai, hpair⟩ := hw i hi
  exact ⟨carrier, a, preceq_trans hcarrier hWD, ha, hai, hpair⟩

/-- Height-law form of `justification_certificate_rows`. -/
theorem justification_certificate_rows_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (hH : FGHeightLaws E H) (D : FGBlock V)
    (hnz : (H D).h_j ≠ 0) :
    ∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q, ∃ a ∈ chainRows D, a.signer = i ∧
      a.height_pair = .vote (H D).h_j (H D).J.root false := by
  obtain ⟨Q, hQ, hw⟩ := hH.justification_certificate D hnz
  refine ⟨Q, hQ, fun i hi => ?_⟩
  obtain ⟨carrier, a, hc, ha, hai, hpa⟩ := hw i hi
  exact ⟨a, mem_chainRows_of_carrier hc ha, hai, hpa⟩

/-- Shared record form of `slashableWeight_or_justified_eq`. -/
theorem slashableWeight_or_justified_eq_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f) (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂)
    (hh : (H B₁).h_j = (H B₂).h_j) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      (H B₁).J = (H B₂).J := by
  by_cases hz : (H B₁).h_j = 0
  · refine Or.inr ?_
    rw [hc.justified_zero B₁ hz,
      hc.justified_zero B₂ (hh.symm.trans hz)]
  · by_cases hr : (H B₁).J.root = (H B₂).J.root
    · exact Or.inr (hroot _ _ (Or.inl (preceq_trans (hc.height.justified_preceq_entry B₁)
      (hc.height.entry_preceq B₁))) (Or.inr (preceq_trans (hc.height.justified_preceq_entry B₂)
      (hc.height.entry_preceq B₂))) hr)
    · obtain ⟨Q₁, hQ₁, hw₁⟩ :=
        justification_certificate_rows_of_heightLaws E H hc.height B₁ hz
      obtain ⟨Q₂, hQ₂, hw₂⟩ :=
        justification_certificate_rows_of_heightLaws E H hc.height B₂ (hh ▸ hz)
      rw [← hh] at hw₂
      exact Or.inl (uniqueJust_slashable E hr hQ₁ hQ₂ hw₁ hw₂)

/-- Shared record form of `e1Weight_or_finalized_preceq`. -/
theorem e1Weight_or_finalized_preceq_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hh : (f B).h_F < (H W).h) :
    HasE1WeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (f B).F W := by
  by_cases hz : (f B).h_F = 0
  · refine Or.inr ?_
    rw [hc.finalized_zero B hz]
    exact genesis_preceq W
  · obtain ⟨F, -, rfl, Qf, hQf, hwf⟩ := finality_certificate_of_certificate E H f hc B hz
    obtain ⟨X, hXW, -, Qc, hQc, hwc⟩ :=
      hc.height.height_crossing W _ (Nat.one_le_iff_ne_zero.mpr hz) hh
    by_cases hr : X.root = (f B).F.root
    · refine Or.inr ?_
      rw [← hroot _ _ (Or.inr hXW) (Or.inl (finalized_preceq_chain_of_certificate E H f hc B)) hr]
      exact hXW
    · refine Or.inl ⟨Qf ∩ Qc, quorum_intersection E hQf hQc, fun i hi => ?_⟩
      obtain ⟨hf, hc⟩ := Finset.mem_inter.mp hi
      obtain ⟨cB, b, hcB, hb, hbi, hbf⟩ := hwf i hf
      obtain ⟨cW, a, hcW, ha, hai, ham⟩ := hwc i hc
      exact ⟨b, mem_chainRows_of_carrier hcB hb, a, mem_chainRows_of_carrier hcW ha, hbi, hai,
        e1Slashable_of_matchesEntry b a _ X.root _ (hbi.trans hai.symm) hbf ham hr⟩

/-- Shared record form of `slashableWeight_or_finalized_preceq`. -/
theorem slashableWeight_or_finalized_preceq_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f) (B W : FGBlock V)
    (hroot : RootInjectiveOn B W)
    (hh : (f B).h_F < (H W).h) :
    HasSlashableWeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (f B).F W :=
  (e1Weight_or_finalized_preceq_of_certificate E H f hc B W hroot hh).imp
    hasSlashableWeightBetween_of_hasE1WeightBetween id

/-- Shared record form of `e1Weight_or_finalized_compatible_of_le`. -/
theorem e1Weight_or_finalized_compatible_of_le_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂)
    (hle : (f B₁).h_F ≤ (f B₂).h_F) :
    HasE1WeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (f B₁).F (f B₂).F = true := by
  have hlt : (f B₁).h_F < (H B₂).h :=
    Nat.lt_of_le_of_lt hle (finalized_below_height_of_certificate E H f hc B₂)
  rcases e1Weight_or_finalized_preceq_of_certificate E H f hc B₁ B₂ hroot hlt with hev | hF
  · exact Or.inl hev
  · exact Or.inr (compatible_of_preceq_common hF
      (finalized_preceq_chain_of_certificate E H f hc B₂))

/-- Shared record form of `slashableWeight_or_finalized_compatible`. -/
theorem slashableWeight_or_finalized_compatible_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B₁ B₂ : FGBlock V)
    (hroot : RootInjectiveOn B₁ B₂) :
    HasSlashableWeightBetween E (chainRows B₁) (chainRows B₂) ∨
      FGBlock.compatible (f B₁).F (f B₂).F = true := by
  rcases Nat.le_total (f B₁).h_F (f B₂).h_F with hle | hle
  · exact (e1Weight_or_finalized_compatible_of_le_of_certificate E H f hc B₁ B₂ hroot hle).imp
      hasSlashableWeightBetween_of_hasE1WeightBetween id
  · rcases e1Weight_or_finalized_compatible_of_le_of_certificate E H f hc B₂ B₁ hroot.symm hle
    with hev | hc
    · exact Or.inl (hasSlashableWeightBetween_of_hasE1WeightBetween_swap hev)
    · exact Or.inr ((compatible_comm _ _).trans hc)

omit [Fintype V] [RowCodec V] in
/-- [ROOT-DIGEST W1; DC Ancestry] A proper ancestor is below the parent. -/
theorem preceq_parent_of_ne {A B : FGBlock V} (h : FGBlock.Preceq A B) (hne : A ≠ B) :
    FGBlock.Preceq A B.parent := by
  cases B with
  | genesis => exact h
  | node p s r x rs =>
    change FGBlock.Preceq A p
    exact preceq_parent_of_preceq_node h hne

omit [Fintype V] [RowCodec V] in
/-- [ROOT-DIGEST W1; DC Ancestry] Parent preserves ancestry. -/
theorem parent_preceq_parent {A B : FGBlock V} (h : FGBlock.Preceq A B) :
    FGBlock.Preceq A.parent B.parent := by
  by_cases he : A = B
  · subst A
    exact preceq_refl _
  · have hp : FGBlock.Preceq A.parent A := by
      cases A with
      | genesis => exact preceq_refl _
      | node p s r x rs => exact preceq_parent_node p s r x rs
    exact preceq_trans hp (preceq_parent_of_ne h he)

/-- [ROOT-DIGEST W1; DC FinalityComparison] A finalized target is below the parent. -/
theorem finalized_preceq_parent_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B : FGBlock V) : FGBlock.Preceq (f B).F B.parent := by
  by_cases hz : (f B).h_F = 0
  · rw [hc.finalized_zero B hz]
    exact genesis_preceq _
  · obtain ⟨C, D, hCD, hDB, hbirth, _⟩ := hc.finality_origin B hz
    rw [← hbirth.2.2.1]
    exact preceq_trans (hc.height.entry_preceq C.parent)
      (parent_preceq_parent (preceq_trans hCD.1 hDB))

/-- [ROOT-DIGEST W1; DC FinalityComparison] Only target equality uses parent roots.
The evidence pools contain all rows of both full chains. -/
theorem e1Weight_or_finalized_preceq_of_parent_roots (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B W : FGBlock V) (hr : RootInjectiveOn B.parent W.parent)
    (hh : (f B).h_F < (H W).h) :
    HasE1WeightBetween E (chainRows B) (chainRows W) ∨
      FGBlock.Preceq (f B).F W := by
  by_cases hz : (f B).h_F = 0
  · refine Or.inr ?_
    rw [hc.finalized_zero B hz]
    exact genesis_preceq W
  · obtain ⟨F, -, rfl, Qf, hQf, hwf⟩ := finality_certificate_of_certificate E H f hc B hz
    obtain ⟨X, hXW, hXh, Qc, hQc, hwc⟩ :=
      hc.height.height_crossing W _ (Nat.one_le_iff_ne_zero.mpr hz) hh
    by_cases he : X.root = (f B).F.root
    · have hXparent : FGBlock.Preceq X W.parent :=
        preceq_parent_of_ne hXW (fun h => hh.ne (hXh.symm.trans (congrArg (fun B => (H B).h) h)))
      have heq := hr X (f B).F (Or.inr hXparent)
        (Or.inl (finalized_preceq_parent_of_certificate E H f hc B)) he
      exact Or.inr (heq ▸ hXW)
    · refine Or.inl ⟨Qf ∩ Qc, quorum_intersection E hQf hQc, fun i hi => ?_⟩
      obtain ⟨hf, hcross⟩ := Finset.mem_inter.mp hi
      obtain ⟨cB, b, hcB, hb, hbi, hbf⟩ := hwf i hf
      obtain ⟨cW, a, hcW, ha, hai, ham⟩ := hwc i hcross
      exact ⟨b, mem_chainRows_of_carrier hcB hb, a, mem_chainRows_of_carrier hcW ha, hbi, hai,
        e1Slashable_of_matchesEntry b a _ X.root _ (hbi.trans hai.symm) hbf ham he⟩

/-- [ROOT-DIGEST W1; DC WholeRunFinalitySafety] Parent-chain collision freedom suffices. -/
theorem slashableWeight_or_finalized_compatible_of_parent_roots
    (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (K W : FGBlock V)
    (hr : RootInjectiveOn K.parent W.parent) :
    HasSlashableWeightBetween E (chainRows K) (chainRows W) ∨
      FGBlock.compatible (f K).F (f W).F = true := by
  rcases Nat.le_total (f K).h_F (f W).h_F with hle | hle
  · rcases e1Weight_or_finalized_preceq_of_parent_roots E H f hc K W hr
      (hle.trans_lt (finalized_below_height_of_certificate E H f hc W)) with he | hp
    · exact Or.inl (hasSlashableWeightBetween_of_hasE1WeightBetween he)
    · exact Or.inr (compatible_of_preceq_common hp
        (finalized_preceq_chain_of_certificate E H f hc W))
  · rcases e1Weight_or_finalized_preceq_of_parent_roots E H f hc W K hr.symm
      (hle.trans_lt (finalized_below_height_of_certificate E H f hc K)) with he | hp
    · exact Or.inl (hasSlashableWeightBetween_of_hasE1WeightBetween_swap he)
    · exact Or.inr ((compatible_comm _ _).trans (compatible_of_preceq_common hp
        (finalized_preceq_chain_of_certificate E H f hc K)))

end AvailableChain.KitFG
end
