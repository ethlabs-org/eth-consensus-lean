module
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.CrossingCore
public import AvailableChainKitFG.CertificateSimplex -- shake: keep (instance checks in examples)
public import AvailableChainKitFG.SelectionCore -- shake: keep (private pruning tests)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.CrossingCore

open AvailableChain.SimplexFG
/-- ROOT-DIGEST W3: use a closed finite table for both ancestor chains. -/
theorem finite_chain_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y)
    (A B : FGBlock V) (hA : A ∈ T) (hB : B ∈ T) : RootInjectiveOn A B := by
  intro X Y hX hY hr
  have mem : ∀ Z, (FGBlock.Preceq Z A ∨ FGBlock.Preceq Z B) → Z ∈ T := by
    intro Z hZ
    rcases hZ with hZ | hZ
    · exact ancestor_closed_of_parent_closed T hcl A hA Z hZ
    · exact ancestor_closed_of_parent_closed T hcl B hB Z hZ
  exact hinj X (mem X hX) Y (mem Y hY) hr

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- An older entry uses its birth block, with both parts of the key fixed.
theorem crossing_birth_key_test (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (r : FGSelectionView V)
    (hc : FGChainCertificate E H f r) (C W : FGBlock V) (hroots : RootInjectiveOn C W) (j : Height)
        (X : FGBlock V)
    (hb : JustificationBirth E H C j X) (hj : j ≠ 0) (hW : j < (H W).h)
    (hnot : ¬ FGBlock.Preceq X W) :
    ∃ Y : FGBlock V, Y.root ≠ X.root ∧ ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry j Y.root = true := by
  obtain ⟨_, _, _, hhj, hJ, _, _⟩ := hb
  have h := exists_crossing_quorum_ne_justified_of_heightLaws E H hc.laws.height C W hroots
    (hhj ▸ hj) (hhj ▸ hW) (hJ ▸ hnot)
  simpa only [hhj, hJ] using h

-- The selected QC comes from before, although pruning removes it.
theorem crossing_selected_before_test (E : Electorate V)
    (H : FGHeightView V) (f : FGFinalityView V) (r : FGSelectionView V)
    (hc : FGChainCertificate E H f r) (B : FGBlock V) (e : FGCertEntry V)
    (hB : B ≠ .genesis) (he : r.chosen B = some e) :
    e ∈ r.before B ∧ E.IsQuorum e.Q ∧ e ∉ r.afterPrune B := by
  obtain ⟨hmem, hq, _⟩ := hc.selection.greatest B e he
  have hf : f B = ⟨e.X, e.j⟩ := by
    simpa only [he] using hc.selection.write B hB
  refine ⟨hmem, hq, ?_⟩
  rw [hc.selection.prune B]
  simp only [List.mem_filter, decide_eq_true_eq, hf, lt_self_iff_false, and_false,
    not_false_eq_true]

-- A lower entry has coverage without any quorum premise for its own signer set.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hc : FGChainCertificate E H f r)
    (B X : FGBlock V) (j : Height)
    (he : (⟨j, X, ∅⟩ : FGCertEntry V) ∈ r.before B) (hj : j ≤ (f B).h_F) :
    FGBlock.Preceq X (f B).F ∧ j ≤ (f B).h_F :=
  ⟨hc.selection.pruned_covered B _ he hj, hj⟩

private def cxTargetTwo : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [⟨0, .vote 2 B1.root false, none⟩,
    ⟨1, .vote 2 B1.root false, none⟩, ⟨2, .vote 2 B1.root false, none⟩]

private def cxFinalTwo : FGBlock (Fin 4) :=
  .node cxTargetTwo 3 ⟨101⟩ 0 [⟨0, .empty, some ⟨2, B1.root⟩⟩,
    ⟨1, .empty, some ⟨2, B1.root⟩⟩, ⟨2, .empty, some ⟨2, B1.root⟩⟩]

-- The two entries have target births. Only the higher pair has finality rows.
example : JustificationBirth E4 (simplexHeightView E4 cfg1) B1 1 .genesis ∧
    JustificationBirth E4 (simplexHeightView E4 cfg1) cxTargetTwo 2 B1 := by
  constructor
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    exact (simplexCertificateLaws E4 cfg1).height.justification_certificate B1 (by decide)
  · refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
    exact (simplexCertificateLaws E4 cfg1).height.justification_certificate cxTargetTwo (by decide)

-- The list fixture models finality pruning, before capacity eviction.
-- Both keys are removed and covered. The lower signer set is not a QC.
set_option maxRecDepth 2048 in
private theorem crossing_pruned_without_own_quorum_test :
    let before : List (FGCertEntry (Fin 4)) := [⟨1, .genesis, ∅⟩, ⟨2, B1, {0, 1, 2}⟩]
    let f := simplexFinalityView E4 cfg1 cxFinalTwo
    (pruneCertEntries f.h_F before).length = 0 ∧
      FGBlock.Preceq .genesis f.F ∧ 1 ≤ f.h_F ∧ ¬ E4.IsQuorum ∅ := by
  refine ⟨by simp only [pruneCertEntries_def]; decide, genesis_preceq _, by decide, ?_⟩
  change ¬ (3 ≤ 0)
  decide

-- Coverage does not create a certificate for the removed height-1 pair.
private theorem crossing_pruned_no_finality_certificate_test (C : FGBlock (Fin 4)) :
    ¬ FinalityQCAfter E4 C cxFinalTwo 1 .genesis := by
  intro h
  obtain ⟨Q, hQ, hw⟩ := h
  obtain ⟨i, hi, _⟩ := honest_in_quorum E4 ∅ hQ (by decide)
  obtain ⟨carrier, a, _, hcarrier, ha, _, hp⟩ := hw i hi
  have hmem := mem_chainRows_of_carrier hcarrier ha
  have hnone : ∀ b ∈ chainRows cxFinalTwo,
      b.finality_pair ≠ some ⟨1, (FGBlock.genesis : FGBlock (Fin 4)).root⟩ := by decide
  exact hnone a hmem hp

-- A capacity drop can remove an entry above F. Neither coverage fact follows.
private theorem crossing_eviction_no_coverage_test :
    let e : FGCertEntry (Fin 4) := ⟨2, B1, ∅⟩
    let f := simplexFinalityView E4 cfg1 cxTargetTwo
    let afterPrune := pruneCertEntries f.h_F [e]
    afterPrune.length = 1 ∧ (afterPrune.drop 1).length = 0 ∧
      ¬ FGBlock.Preceq e.X f.F ∧ ¬ e.j ≤ f.h_F := by
  simp only [pruneCertEntries_def]
  decide

-- The bridge supplies maturity while the finality projection stays arbitrary.
example (E : Electorate V) (cfg : FGConfig) (H : FGHeightView V)
    (hb : HeightBridge E cfg H) (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row
        V))
    (hup : (H P).h < (H (.node P s r_s x rs)).h) :
    (∃ Q : Finset V, E.IsQuorum Q ∧ ∀ i ∈ Q,
      ∃ a ∈ chainRows (.node P s r_s x rs), a.signer = i ∧
        a.height_pair = .vote (H P).h (H P).T_h.root false) ∨
      (H P).T_h.slot + cfg.timeoutDelay ≤ s :=
  crossing_maturity_of_heightBridge E cfg H hb P s r_s x rs hup

-- Instance check: exists_crossing_quorum_ne_justified_of_heightLaws.
example
    (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W) :
    ∃ X : FGBlock V, X.root ≠ (derive E cfg B).J.root ∧ ∃ Q : Finset V, E.IsQuorum Q ∧
      ∀ i ∈ Q, ∃ b ∈ chainRows W, b.signer = i ∧
        b.height_pair.matchesEntry (derive E cfg B).h_j X.root = true :=
  exists_crossing_quorum_ne_justified_of_heightLaws E _ (simplexHeightLaws E cfg)
    B W hroots hJ hW hnot

-- Instance check: e1Weight_of_finalityQC_not_preceq_of_heightLaws.
example
    (E : Electorate V) (cfg : FGConfig) (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (A : Finset (Row V)) (Q : Finset V) (hQ : E.IsQuorum Q)
    (hfin : ∀ i ∈ Q, ∃ a ∈ A, a.signer = i ∧
      a.finality_pair = some ⟨(derive E cfg B).h_j, (derive E cfg B).J.root⟩) :
    HasE1WeightBetween E A (chainRows W) :=
  e1Weight_of_finalityQC_not_preceq_of_heightLaws E _ (simplexHeightLaws E cfg)
    B W hroots hJ hW hnot A Q hQ hfin

-- Instance check: slashableWeight_of_finalized_crossing_of_certificate.
example
    (E : Electorate V) (cfg : FGConfig)
    (B W D : FGBlock V) (hroots : RootInjectiveOn B W)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (hfin : (derive E cfg D).F = (derive E cfg B).J)
    (hfinH : (derive E cfg D).h_F = (derive E cfg B).h_j) :
    HasSlashableWeightBetween E (chainRows W) (chainRows D) :=
  slashableWeight_of_finalized_crossing_of_certificate E _ _ (simplexCertificateLaws E cfg)
    B W D hroots hJ hW hnot hfin hfinH

-- Instance check: exists_honest_timeout_of_crossing_of_heightLaws.
example
    (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (B W : FGBlock V) (hroots : RootInjectiveOn B W)
    (hcap : E.weightOf faulty + E.totalWeight < 2 * E.q)
    (hJ : (derive E cfg B).h_j ≠ 0)
    (hW : (derive E cfg B).h_j < (derive E cfg W).h)
    (hnot : ¬ FGBlock.Preceq (derive E cfg B).J W)
    (hhonest : ∀ a ∈ chainRows B, ∀ b ∈ chainRows W, a.signer ∉ faulty → ¬ Slashable a b) :
    ∃ i, i ∉ faulty ∧ ∃ X : BlockId, X ≠ (derive E cfg B).J.root ∧
      (∃ a ∈ chainRows B, a.signer = i ∧
        a.height_pair = .vote (derive E cfg B).h_j (derive E cfg B).J.root false) ∧
      (∃ b ∈ chainRows W, b.signer = i ∧ b.height_pair = .vote (derive E cfg B).h_j X true) :=
  exists_honest_timeout_of_crossing_of_heightLaws E _ (simplexHeightLaws E cfg)
    faulty B W hroots hcap hJ hW hnot hhonest

private def cxForkOne : FGBlock (Fin 4) :=
  .node .genesis 1 ⟨102⟩ 1 [⟨0, .vote 1 genesisRoot false, none⟩,
    ⟨1, .vote 1 genesisRoot false, none⟩, ⟨2, .vote 1 genesisRoot false, none⟩]

private def cxForkTwo : FGBlock (Fin 4) :=
  .node cxForkOne 2 ⟨103⟩ 0 [⟨0, .vote 2 cxForkOne.root false, none⟩,
    ⟨1, .vote 2 cxForkOne.root false, none⟩, ⟨2, .vote 2 cxForkOne.root false, none⟩]

-- All three crossing premises hold on this fork at the same time.
set_option maxRecDepth 4096 in
private theorem crossing_fork_premises_test :
    (simplexHeightView E4 cfg1 cxTargetTwo).h_j ≠ 0 ∧
      (simplexHeightView E4 cfg1 cxTargetTwo).h_j <
        (simplexHeightView E4 cfg1 cxForkTwo).h ∧
      ¬ FGBlock.Preceq (simplexHeightView E4 cfg1 cxTargetTwo).J cxForkTwo := by decide

private theorem crossing_fork_quorum_test :
    ∃ X : FGBlock (Fin 4), X.root ≠ (simplexHeightView E4 cfg1 cxTargetTwo).J.root ∧
      ∃ Q : Finset (Fin 4), E4.IsQuorum Q ∧ ∀ i ∈ Q, ∃ b ∈ chainRows cxForkTwo,
        b.signer = i ∧ b.height_pair.matchesEntry
          (simplexHeightView E4 cfg1 cxTargetTwo).h_j X.root = true :=
  exists_crossing_quorum_ne_justified_of_heightLaws E4 _ (simplexHeightLaws E4 cfg1)
    cxTargetTwo cxForkTwo
    (finite_chain_roots {.genesis, B1, cxTargetTwo, cxForkOne, cxForkTwo}
      (by decide +kernel) (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel))
    crossing_fork_premises_test.1 crossing_fork_premises_test.2.1
    crossing_fork_premises_test.2.2

#print axioms crossing_fork_premises_test
#print axioms crossing_fork_quorum_test
#print axioms slashableWeight_of_finalized_pair_crossing_of_certificate
#print axioms crossing_birth_key_test
#print axioms crossing_selected_before_test
#print axioms crossing_pruned_without_own_quorum_test
#print axioms crossing_pruned_no_finality_certificate_test
#print axioms crossing_eviction_no_coverage_test

#print axioms exists_crossing_quorum_ne_justified_of_heightLaws
#print axioms e1Weight_of_finalityQC_not_preceq_of_heightLaws
#print axioms slashableWeight_of_finalized_crossing_of_certificate
#print axioms exists_honest_timeout_of_crossing_of_heightLaws
#print axioms crossing_maturity_of_heightBridge

end AvailableChain.KitFG.Tests.CrossingCore
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.KitFG.Tests.CrossingCore.finite_chain_roots
