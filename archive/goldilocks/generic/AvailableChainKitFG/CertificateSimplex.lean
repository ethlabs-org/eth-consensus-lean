module
public import AvailableChainKitFG.CertificateSimplexDef
public import AvailableChainKitFG.HeightLaws
public import AvailableChainKitFG.RowBits

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [Fintype V] [RowCodec V] in
private theorem simplex_strict_node {C p : FGBlock V} (s : Slot) (r_s : BlockId) (x : Nat)
    (rs : List (Row V)) (hp : FGBlock.Preceq C p) :
    StrictPrefix C (.node p s r_s x rs) := by
  refine ⟨preceq_node_of_preceq s r_s x rs hp, ?_⟩
  intro he
  have hcycle := preceq_antisymm (he ▸ hp) (preceq_parent_node p s r_s x rs)
  have hs := congrArg sizeOf hcycle
  simp only [FGBlock.node.sizeOf_spec] at hs
  omega

/-- Finality height and block both increase along a chain. -/
theorem simplex_finalized_mono (E : Electorate V) (cfg : FGConfig)
    {A B : FGBlock V} (hAB : FGBlock.Preceq A B) :
    (derive E cfg A).h_F ≤ (derive E cfg B).h_F ∧
      FGBlock.Preceq (derive E cfg A).F (derive E cfg B).F := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact ⟨le_rfl, preceq_refl _⟩
  | node p s r_s x rs ih =>
      by_cases he : A = .node p s r_s x rs
      · subst A
        exact ⟨le_rfl, preceq_refl _⟩
      obtain ⟨hh, hF⟩ := ih (preceq_parent_of_preceq_node hAB he)
      obtain ⟨_, _, _, hJ, hj, hF', hf⟩ :=
        foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      rw [derive_node]
      rcases finality_pair_cases E cfg
          (foldRows (derive E cfg p) (.node p s r_s x rs) rs) with h | h
      · rw [h.1, h.2, hF', hf]
        exact ⟨hh, hF⟩
      · rw [h.1, h.2.1, hJ, hj]
        exact ⟨hh.trans (heights_ordered E cfg p),
          preceq_trans hF (derive_F_preceq_J E cfg p)⟩

private theorem simplex_interval_fold (E : Electorate V) (cfg : FGConfig)
    (p : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) (C : FGBlock V)
    (hCp : FGBlock.Preceq C p)
    (hw : ∀ i ∈ (derive E cfg p).finalize, ∃ carrier a,
      StrictPrefix C carrier ∧ FGBlock.Preceq carrier p ∧
      a ∈ carrier.rows ∧ a.signer = i ∧
      a.finality_pair = some ⟨(derive E cfg p).h_j, (derive E cfg p).J.root⟩) :
    ∀ i ∈ (foldRows (derive E cfg p) (.node p s r_s x rs) rs).finalize,
      ∃ carrier a, StrictPrefix C carrier ∧ FGBlock.Preceq carrier (.node p s r_s x rs) ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨(derive E cfg p).h_j, (derive E cfg p).J.root⟩ := by
  intro i hi
  rcases (bit_fold_iff .finality rs { derive E cfg p with s := s } i).1 hi with
      hold | ⟨a, ha, hai, hm⟩
  · obtain ⟨carrier, a, hC, hp, ha, hai, hm⟩ := hw i hold
    exact ⟨carrier, a, hC, preceq_node_of_preceq s r_s x rs hp, ha, hai, hm⟩
  · exact ⟨.node p s r_s x rs, a, simplex_strict_node s r_s x rs hCp,
      preceq_refl _, ha, hai, hm.2⟩

/-- The latest positive justification has a birth. Its finality bits come
from rows carried strictly after that birth, including bits kept after finality. -/
theorem simplex_justification_birth_interval (E : Electorate V) (cfg : FGConfig)
    (B : FGBlock V) (hnz : (derive E cfg B).h_j ≠ 0) :
    ∃ C, FGBlock.Preceq C B ∧
      JustificationBirth E (simplexHeightView E cfg) C
        (derive E cfg B).h_j (derive E cfg B).J ∧
      ∀ i ∈ (derive E cfg B).finalize, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨(derive E cfg B).h_j, (derive E cfg B).J.root⟩ := by
  induction B with
  | genesis => exact (hnz rfl).elim
  | node p s r_s x rs ih =>
      let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
      obtain ⟨_, hh, hT, hJ, hj, _, _⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
      by_cases ht : (afterFin E σ).targetQuorum E = true
      · have hnew : derive E cfg (.node p s r_s x rs) =
            advance_height { afterFin E σ with
              J := (afterFin E σ).T_h, h_j := (afterFin E σ).h, finalize := ∅ } := by
          rw [derive_node, process_height_events_eq, ite_eq_left ht]
        have hjnew : (derive E cfg (.node p s r_s x rs)).h_j = (derive E cfg p).h := by
          rw [hnew]; exact (afterFin_h E σ).trans hh
        have hJnew : (derive E cfg (.node p s r_s x rs)).J = (derive E cfg p).T_h := by
          rw [hnew]; exact (afterFin_T_h E σ).trans hT
        refine ⟨.node p s r_s x rs, preceq_refl _, ?_, ?_⟩
        · refine ⟨by simp, hjnew.symm, hJnew.symm, rfl, rfl, ?_, ?_⟩
          · change (derive E cfg (.node p s r_s x rs)).h = _
            rw [hnew]
            rfl
          · exact justification_certificate E cfg (.node p s r_s x rs) hnz
        · intro i hi
          rw [hnew] at hi
          exact (Finset.notMem_empty i hi).elim
      · have hkeep :
            (derive E cfg (.node p s r_s x rs)).h_j = (derive E cfg p).h_j ∧
            (derive E cfg (.node p s r_s x rs)).J = (derive E cfg p).J ∧
            (derive E cfg (.node p s r_s x rs)).finalize = σ.finalize := by
          rw [derive_node, process_height_events_eq, ite_eq_right ht]
          split_ifs <;>
            exact ⟨(afterFin_h_j E σ).trans hj, (afterFin_J E σ).trans hJ,
              afterFin_finalize E σ⟩
        obtain ⟨C, hCp, hb, hw⟩ := ih (hkeep.1 ▸ hnz)
        refine ⟨C, preceq_node_of_preceq s r_s x rs hCp, ?_, ?_⟩
        · rwa [hkeep.1, hkeep.2.1]
        · rw [hkeep.1, hkeep.2.1, hkeep.2.2]
          exact simplex_interval_fold E cfg p s r_s x rs C hCp hw

/-- Each pending entry before finality has an earlier birth and interval rows. -/
theorem simplex_prefinal_entry_origin (E : Electorate V) (cfg : FGConfig)
    (B : FGBlock V) (e : FGCertEntry V)
    (he : e ∈ (simplexSelectionView E cfg).before B) :
    ∃ C, StrictPrefix C B ∧
      JustificationBirth E (simplexHeightView E cfg) C e.j e.X ∧
      ∀ i ∈ e.Q, ∃ carrier a,
        StrictPrefix C carrier ∧ FGBlock.Preceq carrier B ∧
        a ∈ carrier.rows ∧ a.signer = i ∧
        a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  cases B with
  | genesis => exact (List.not_mem_nil he).elim
  | node p s r_s x rs =>
      let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
      change e ∈ simplexPending σ at he
      rw [simplexPending_def] at he
      split_ifs at he with hpend
      · obtain rfl := List.mem_singleton.mp he
        obtain ⟨_, _, _, hJ, hj, _, hf⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
        have hnz : (derive E cfg p).h_j ≠ 0 := by
          exact Nat.ne_of_gt ((Nat.zero_le _).trans_lt (hf ▸ hpend.trans_eq hj))
        obtain ⟨C, hCp, hb, hw⟩ := simplex_justification_birth_interval E cfg p hnz
        refine ⟨C, simplex_strict_node s r_s x rs hCp, ?_, ?_⟩
        · change JustificationBirth E (simplexHeightView E cfg) C σ.h_j σ.J
          rwa [show σ.h_j = _ from hj, show σ.J = _ from hJ]
        · simpa only [show σ.h_j = _ from hj, show σ.J = _ from hJ] using
            simplex_interval_fold E cfg p s r_s x rs C hCp hw
      · exact (List.not_mem_nil he).elim

/-- Finality names the selected pair's birth and the block that first wrote it. -/
theorem simplex_finality_origin (E : Electorate V) (cfg : FGConfig)
    (B : FGBlock V) (hnz : (simplexFinalityView E cfg B).h_F ≠ 0) :
    ∃ C D, StrictPrefix C D ∧ FGBlock.Preceq D B ∧
      JustificationBirth E (simplexHeightView E cfg) C
        (simplexFinalityView E cfg B).h_F (simplexFinalityView E cfg B).F ∧
      (simplexFinalityView E cfg D.parent).h_F < (simplexFinalityView E cfg D).h_F ∧
      simplexFinalityView E cfg D = simplexFinalityView E cfg B ∧
      FinalityQCAfter E C D
        (simplexFinalityView E cfg B).h_F (simplexFinalityView E cfg B).F := by
  induction B with
  | genesis => exact (hnz rfl).elim
  | node p s r_s x rs ih =>
      let B := FGBlock.node p s r_s x rs
      let σ := foldRows (derive E cfg p) B rs
      obtain ⟨_, _, _, hJ, hj, hF, hf⟩ := foldRows_fields (derive E cfg p) B rs
      rcases finality_pair_cases E cfg σ with h | h
      · have hp : simplexFinalityView E cfg B = simplexFinalityView E cfg p := by
          change (⟨(derive E cfg B).F, (derive E cfg B).h_F⟩ : FGFinality V) = _
          rw [derive_node, h.1, h.2, hF, hf]
          rfl
        rw [hp] at hnz ⊢
        obtain ⟨C, D, hCD, hDp, hb, hinc, heq, hw⟩ := ih hnz
        exact ⟨C, D, hCD, preceq_node_of_preceq s r_s x rs hDp, hb, hinc, heq, hw⟩
      · have hp : simplexFinalityView E cfg B = ⟨σ.J, σ.h_j⟩ := by
          change (⟨(derive E cfg B).F, (derive E cfg B).h_F⟩ : FGFinality V) = _
          rw [derive_node, h.1, h.2.1]
        have hpend := lt_of_finalityReady E h.2.2
        have he : (⟨σ.h_j, σ.J, σ.finalize⟩ : FGCertEntry V) ∈
            (simplexSelectionView E cfg).before B := by
          change _ ∈ simplexPending σ
          rw [simplexPending_def, ite_eq_left hpend]
          exact List.mem_singleton_self _
        obtain ⟨C, hCB, hb, hw⟩ := simplex_prefinal_entry_origin E cfg B _ he
        refine ⟨C, B, hCB, preceq_refl _, ?_, ?_, rfl, ?_⟩
        · change JustificationBirth E (simplexHeightView E cfg) C
            (simplexFinalityView E cfg B).h_F (simplexFinalityView E cfg B).F
          rw [hp]
          exact hb
        · rw [hp]
          change (derive E cfg p).h_F < σ.h_j
          exact hf ▸ hpend
        · rw [hp]
          exact ⟨σ.finalize, isQuorum_of_finalityReady E h.2.2, hw⟩

/-- The certificate laws follow from the existing SimplexFG proofs. -/
theorem simplexCertificateLaws (E : Electorate V) (cfg : FGConfig) :
    FGCertificateLaws E (simplexHeightView E cfg) (simplexFinalityView E cfg) where
  height := simplexHeightLaws E cfg
  initial := rfl
  justified_zero := justified_zero_is_genesis E cfg
  finalized_zero := finalized_zero_is_genesis E cfg
  finalized_preceq_justified := derive_F_preceq_J E cfg
  heights_ordered := heights_ordered E cfg
  finalized_mono := simplex_finalized_mono E cfg
  finality_origin := simplex_finality_origin E cfg

/-- The pending singleton gives the selection laws at the three phase boundaries. -/
theorem simplexSelectionLaws (E : Electorate V) (cfg : FGConfig) :
    FGSelectionLaws E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (simplexSelectionView E cfg) where
  initial := ⟨rfl, rfl, rfl⟩
  ordered := by
    intro B
    cases B with
    | genesis => exact List.Pairwise.nil
    | node p s r_s x rs =>
        change (simplexPending _).Pairwise _
        rw [simplexPending_def]
        split_ifs <;> simp
  bounds := by
    intro B e he
    cases B with
    | genesis => exact (List.not_mem_nil he).elim
    | node p s r_s x rs =>
        let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
        change e ∈ simplexPending σ at he
        rw [simplexPending_def] at he
        split_ifs at he with hpend
        · obtain rfl := List.mem_singleton.mp he
          obtain ⟨_, _, _, hJ, hj, _, hf⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs)
            rs
          change (derive E cfg p).h_F < σ.h_j ∧ σ.h_j ≤ (derive E cfg p).h_j ∧
            FGBlock.Preceq (derive E cfg p).F σ.J ∧ FGBlock.Preceq σ.J (derive E cfg p).J
          have hpend' : (derive E cfg p).h_F < (derive E cfg p).h_j :=
            hf ▸ hpend.trans_eq hj
          rw [hj, hJ]
          exact ⟨hpend', le_rfl, derive_F_preceq_J E cfg p, preceq_refl _⟩
        · exact (List.not_mem_nil he).elim
  entry_origin := simplex_prefinal_entry_origin E cfg
  none_iff := by
    intro B
    cases B with
    | genesis =>
        change (none : Option (FGCertEntry V)) = none ↔
          ∀ e ∈ ([] : List (FGCertEntry V)), ¬ E.IsQuorum e.Q
        simp
    | node p s r_s x rs =>
        let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
        change (if finalityReady E σ then some _ else none) = none ↔
          ∀ e ∈ simplexPending σ, ¬ E.IsQuorum e.Q
        by_cases hr : finalityReady E σ = true
        · rw [ite_eq_left hr]
          constructor
          · intro h; cases h
          · intro h
            have he : (⟨σ.h_j, σ.J, σ.finalize⟩ : FGCertEntry V) ∈ simplexPending σ := by
              rw [simplexPending_def, ite_eq_left (lt_of_finalityReady E hr)]
              exact List.mem_singleton_self _
            exact (h _ he (isQuorum_of_finalityReady E hr)).elim
        · rw [ite_eq_right hr]
          constructor
          · intro _ e he hq
            rw [simplexPending_def] at he
            split_ifs at he with hp
            · obtain rfl := List.mem_singleton.mp he
              apply hr
              change (decide (σ.h_F < σ.h_j) && decide (E.q ≤ E.weightOf σ.finalize)) = true
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨hp, hq⟩
            · exact (List.not_mem_nil he).elim
          · intro _; rfl
  greatest := by
    intro B e he
    cases B with
    | genesis => cases he
    | node p s r_s x rs =>
        let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
        change (if finalityReady E σ then some _ else none) = some e at he
        split_ifs at he with hready
        · obtain rfl := Option.some.inj he
          change _ ∈ simplexPending σ ∧ E.IsQuorum σ.finalize ∧
            ∀ d ∈ simplexPending σ, E.IsQuorum d.Q → d.j ≤ σ.h_j
          rw [simplexPending_def, ite_eq_left (lt_of_finalityReady E hready)]
          exact ⟨List.mem_singleton_self _, isQuorum_of_finalityReady E hready,
            fun d hd _ => (List.mem_singleton.mp hd) ▸ le_rfl⟩
  write := by
    intro B hn
    cases B with
    | genesis => exact (hn rfl).elim
    | node p s r_s x rs =>
        let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
        obtain ⟨_, _, _, _, _, hF, hf⟩ := foldRows_fields (derive E cfg p) (.node p s r_s x rs) rs
        change (⟨(derive E cfg (.node p s r_s x rs)).F,
          (derive E cfg (.node p s r_s x rs)).h_F⟩ : FGFinality V) =
          match (if finalityReady E σ then
            some (⟨σ.h_j, σ.J, σ.finalize⟩ : FGCertEntry V) else none) with
          | none => _
          | some e => _
        rw [derive_node, (process_height_events_F E cfg σ).1,
          (process_height_events_F E cfg σ).2, afterFin_F, afterFin_h_F]
        split_ifs
        · rfl
        · exact congrArg₂ FGFinality.mk hF hf
  prune := by
    intro B
    cases B with
    | genesis => rfl
    | node p s r_s x rs =>
        let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
        change simplexPending (afterFin E σ) =
          (simplexPending σ).filter (fun e => decide ((derive E cfg (.node p s r_s x rs)).h_F <
            e.j))
        rw [derive_node, (process_height_events_F E cfg σ).2]
        simp only [simplexPending_def, afterFin_h_j, afterFin_J, afterFin_finalize, afterFin_h_F]
        by_cases hr : finalityReady E σ = true
        · have hp := lt_of_finalityReady E hr
          simp only [hr, ite_true, hp, Nat.lt_irrefl, ite_false, List.filter_cons,
            decide_false, Bool.false_eq_true, List.filter_nil]
        · simp only [hr]
          split_ifs with hp <;> simp_all
  pruned_covered := by
    intro B e he hle
    cases B with
    | genesis => exact (List.not_mem_nil he).elim
    | node p s r_s x rs =>
        let σ := foldRows (derive E cfg p) (.node p s r_s x rs) rs
        change e ∈ simplexPending σ at he
        rw [simplexPending_def] at he
        split_ifs at he with hpend
        · obtain rfl := List.mem_singleton.mp he
          change σ.h_j ≤ (derive E cfg (.node p s r_s x rs)).h_F at hle
          change FGBlock.Preceq σ.J (derive E cfg (.node p s r_s x rs)).F
          rw [derive_node, (process_height_events_F E cfg σ).2, afterFin_h_F] at hle
          rw [derive_node, (process_height_events_F E cfg σ).1, afterFin_F]
          split_ifs with hr
          · exact preceq_refl _
          · rw [ite_eq_right hr] at hle
            exact (Nat.not_le_of_lt hpend hle).elim
        · exact (List.not_mem_nil he).elim

/-- Assemble the two SimplexFG records without an additional induction. -/
theorem simplexChainCertificate (E : Electorate V) (cfg : FGConfig) :
    FGChainCertificate E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (simplexSelectionView E cfg) :=
  ⟨simplexCertificateLaws E cfg, simplexSelectionLaws E cfg⟩

end AvailableChain.KitFG
end
