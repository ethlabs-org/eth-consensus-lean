module
public import AvailableChainKitFG.AccountableCore
public import AvailableChainKitFG.CrossingNoFinal

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Height-law form of `exists_crossing_quorum_ne_justified`. -/
theorem exists_crossing_quorum_ne_justified_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (hH : FGHeightLaws E H) (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hJ : (H B).h_j ≠ 0)
    (hW : (H B).h_j < (H W).h)
    (hnot : ¬ FGBlock.Preceq (H B).J W) :
    ∃ X : FGBlock V, X.root ≠ (H B).J.root ∧ ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (H B).h_j X.root = true := by
  obtain ⟨X, hXW, -, Q, hQ, hw⟩ :=
    hH.height_crossing W _ (Nat.one_le_iff_ne_zero.mpr hJ) hW
  refine ⟨X, fun hr => hnot ?_, Q, hQ, fun i hi => ?_⟩
  · rw [← hroot _ _ (Or.inr hXW) (Or.inl (preceq_trans (hH.justified_preceq_entry B)
    (hH.entry_preceq B))) hr]
    exact hXW
  · obtain ⟨carrier, b, hc, hb, hbi, hm⟩ := hw i hi
    exact ⟨b, mem_chainRows_of_carrier hc hb, hbi, hm⟩

/-- Height-law form of `e1Weight_of_finalityQC_not_preceq`. -/
theorem e1Weight_of_finalityQC_not_preceq_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (hH : FGHeightLaws E H) (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hJ : (H B).h_j ≠ 0)
    (hW : (H B).h_j < (H W).h)
    (hnot : ¬ FGBlock.Preceq (H B).J W)
    (A : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q)
    (hfin : ∀ i ∈ Q, ∃ a ∈ A, a.signer = i ∧
      a.finality_pair = some ⟨(H B).h_j, (H B).J.root⟩) :
    HasE1WeightBetween E A (chainRows W) := by
  obtain ⟨X, hne, Qc, hQc, hwc⟩ :=
    exists_crossing_quorum_ne_justified_of_heightLaws E H hH B W hroot hJ hW hnot
  refine ⟨Q ∩ Qc, quorum_intersection E hQ hQc, fun i hi => ?_⟩
  obtain ⟨hf, hc⟩ := Finset.mem_inter.mp hi
  obtain ⟨f, hfA, hfi, hfp⟩ := hfin i hf
  obtain ⟨b, hbW, hbi, hm⟩ := hwc i hc
  exact ⟨f, hfA, b, hbW, hfi, hbi,
    e1Slashable_of_matchesEntry f b _ X.root _ (hfi.trans hbi.symm) hfp hm hne⟩

/-- Shared certificate form of `slashableWeight_of_finalized_crossing`. -/
theorem slashableWeight_of_finalized_crossing_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (B W D : FGBlock V) (hroot : RootInjectiveOn B W)
    (hJ : (H B).h_j ≠ 0)
    (hW : (H B).h_j < (H W).h)
    (hnot : ¬ FGBlock.Preceq (H B).J W)
    (hfin : (f D).F = (H B).J)
    (hfinH : (f D).h_F = (H B).h_j) :
    HasSlashableWeightBetween E (chainRows W) (chainRows D) := by
  have hnz : (f D).h_F ≠ 0 := hfinH ▸ hJ
  obtain ⟨F, -, rfl, Q, hQ, hw⟩ := finality_certificate_of_certificate E H f hc D hnz
  refine hasSlashableWeightBetween_of_hasE1WeightBetween_swap
    (e1Weight_of_finalityQC_not_preceq_of_heightLaws E H hc.height B W hroot hJ hW hnot
      (chainRows D) Q hQ fun i hi => ?_)
  obtain ⟨carrier, a, hcarrier, ha, hai, hap⟩ := hw i hi
  rw [hfinH, hfin] at hap
  exact ⟨a, mem_chainRows_of_carrier hcarrier ha, hai, hap⟩

/-- I4 uses the finalized pair directly, without a latest-justification block. -/
theorem slashableWeight_of_finalized_pair_crossing_of_certificate (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (hc : FGCertificateLaws E H f)
    (D W : FGBlock V) (hroot : RootInjectiveOn D W) (hnz : (f D).h_F ≠ 0)
    (hW : (f D).h_F < (H W).h) (hnot : ¬ FGBlock.Preceq (f D).F W) :
    HasSlashableWeightBetween E (chainRows W) (chainRows D) := by
  have _ := hnz
  exact hasSlashableWeightBetween_of_hasE1WeightBetween_swap
    ((e1Weight_or_finalized_preceq_of_certificate E H f hc D W hroot hW).resolve_right hnot)

/-- Height-law form of `exists_honest_timeout_of_crossing`. -/
theorem exists_honest_timeout_of_crossing_of_heightLaws (E : Electorate V)
    (H : FGHeightView V) (hH : FGHeightLaws E H) (faulty : Finset V)
    (B W : FGBlock V) (hroot : RootInjectiveOn B W)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hJ : (H B).h_j ≠ 0)
    (hW : (H B).h_j < (H W).h)
    (hnot : ¬ FGBlock.Preceq (H B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (H B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair = .vote (H B).h_j (H B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧ b.height_pair = .vote (H B).h_j X true) := by
  obtain ⟨Qj, hQj, hwj⟩ := justification_certificate_rows_of_heightLaws E H hH B hJ
  obtain ⟨X, hne, Qc, hQc, hwc⟩ :=
    exists_crossing_quorum_ne_justified_of_heightLaws E H hH B W hroot hJ hW hnot
  obtain ⟨i, hi, hif⟩ := honest_in_intersection E faulty hQj hQc hcap
  obtain ⟨hij, hic⟩ := Finset.mem_inter.mp hi
  obtain ⟨a, haB, hai, hap⟩ := hwj i hij
  obtain ⟨b, hbW, hbi, hm⟩ := hwc i hic
  refine ⟨i, hif, X.root, hne, ⟨a, haB, hai, hap⟩, b, hbW, hbi, ?_⟩
  cases hbp : b.height_pair with
  | empty => simp [hbp, NamedHeightPair.matchesEntry] at hm
  | vote k T t =>
      simp only [hbp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      cases t with
      | true => rfl
      | false =>
          exfalso
          refine hhonest a haB b hbW (hai ▸ hif) ?_
          have h2 : e2Slashable a b = true := by
            simp [e2Slashable, sameSigner, e2Fields, hap, hbp, hai, hbi, Ne.symm hne]
          change slashable a b = true
          simp only [slashable, h2, Bool.or_true]

/-- The bridge supplies the timeout-maturity behavior absent from `FGHeightLaws`. -/
theorem crossing_maturity_of_heightBridge
    (E : Electorate V) (cfg : FGConfig)
    (H : FGHeightView V) (hb : HeightBridge E cfg H)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (hup : (H P).h < (H (.node P s r_s x rs)).h) :
    (∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ a ∈ chainRows (.node P s r_s x rs),
        a.signer = i ∧
        a.height_pair = .vote (H P).h (H P).T_h.root false) ∨
      (H P).T_h.slot + cfg.timeoutDelay ≤ s := by
  rw [hb P, hb (.node P s r_s x rs)] at hup
  rw [hb P]
  exact crossing_maturity E cfg P s r_s x rs hup

end AvailableChain.KitFG
end
