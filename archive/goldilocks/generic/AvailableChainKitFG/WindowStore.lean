module
public import AvailableChainSimplexFG.WindowStore
public import AvailableChainKitFG.WindowInvariant
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.StoreSafety
public import AvailableChainKitFG.WindowSelection

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding derive acceptViable update_finality on_block
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

variable (E : Electorate V) (cfg : FGConfig) (K : Nat)

private theorem store_window_height_eq (hK : 2 ≤ K) (B : FGBlock V) :
    (derive E cfg K B).h = (SimplexFG.derive E cfg B).h :=
  congrArg FGHeight.h (windowHeightBridge E cfg K hK B)

private theorem store_window_J_eq (hK : 2 ≤ K) (B : FGBlock V) :
    (derive E cfg K B).J = (SimplexFG.derive E cfg B).J :=
  congrArg FGHeight.J (windowHeightBridge E cfg K hK B)

private theorem store_window_hj_eq (hK : 2 ≤ K) (B : FGBlock V) :
    (derive E cfg K B).h_j = (SimplexFG.derive E cfg B).h_j :=
  congrArg FGHeight.h_j (windowHeightBridge E cfg K hK B)

/-- The acceptance filter agrees because it reads only height. -/
theorem acceptViable_eq (hK : 2 ≤ K) (st : SimplexFG.Store V) :
    acceptViable E cfg K st = SimplexFG.acceptViable E cfg st := by
  simp only [acceptViable_def, SimplexFG.acceptViable, store_window_height_eq E cfg K hK, ← hOf_eq]

/-- A finality update keeps the supplied tree. -/
theorem window_update_finality_TF
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (update_finality E cfg K st B).TF = st.TF := by
  rw [update_finality_def]
  dsimp only
  split_ifs <;> rfl

/-- A finality update takes the maximum of the stored and derived heights. -/
theorem window_update_finality_h_max
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (update_finality E cfg K st B).h_max = max st.h_max ((derive E cfg K B).h) := by
  rw [update_finality_def]
  dsimp only
  split_ifs <;> rfl

/-- A finality update selects the compatible greater justification pair. -/
theorem window_update_finality_pair
    (st : SimplexFG.Store V) (B : FGBlock V) :
    ((update_finality E cfg K st B).h_j, (update_finality E cfg K st B).J) =
      if FGBlock.Preceq st.F (derive E cfg K B).J ∧
          lexKey (st.h_j, st.J) < lexKey ((derive E cfg K B).h_j, (derive E cfg K B).J)
        then ((derive E cfg K B).h_j, (derive E cfg K B).J) else (st.h_j, st.J) := by
  rw [update_finality_def]
  dsimp only
  by_cases hc : FGBlock.Preceq st.F (derive E cfg K B).J ∧
      lexKey (st.h_j, st.J) < lexKey ((derive E cfg K B).h_j, (derive E cfg K B).J)
  · have hb : (FGBlock.preceq st.F (derive E cfg K B).J && decide (lexKey (st.h_j, st.J) <
        lexKey ((derive E cfg K B).h_j, (derive E cfg K B).J))) = true := by
      simpa [FGBlock.Preceq] using hc
    rw [ite_eq_left hc, ite_eq_left hb]
    split_ifs <;> rfl
  · have hb : ¬ (FGBlock.preceq st.F (derive E cfg K B).J && decide (lexKey (st.h_j, st.J) <
        lexKey ((derive E cfg K B).h_j, (derive E cfg K B).J))) = true := by
      simpa [FGBlock.Preceq] using hc
    rw [ite_eq_right hc, ite_eq_right hb]
    split_ifs <;> rfl

/-- A finality update keeps F or accepts a stored compatible derived finalization. -/
theorem window_update_finality_F_cases
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (update_finality E cfg K st B).F = st.F ∨
      (FGBlock.Preceq st.F (derive E cfg K B).F ∧ (derive E cfg K B).F ∈ st.TF ∧
        FGBlock.Preceq (derive E cfg K B).F (update_finality E cfg K st B).J ∧
        (update_finality E cfg K st B).F = (derive E cfg K B).F) := by
  rw [update_finality_def]
  dsimp only
  split_ifs with h1 h2 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hF, -⟩, hJ⟩, hV⟩ := h2
    exact Or.inr ⟨hF, (Finset.mem_filter.1 hV).1, hJ, rfl⟩
  · exact Or.inl rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hF, -⟩, hJ⟩, hV⟩ := h2
    exact Or.inr ⟨hF, (Finset.mem_filter.1 hV).1, hJ, rfl⟩
  · exact Or.inl rfl

private theorem store_window_update_finality_F_mono
    (st : SimplexFG.Store V) (B : FGBlock V) :
    FGBlock.Preceq st.F (update_finality E cfg K st B).F := by
  rcases window_update_finality_F_cases E cfg K st B with h | ⟨hF, -, -, h⟩
  · rw [h]
    exact preceq_refl _
  · rw [h]
    exact hF

/-- One update from the same input has the same maximum height. -/
theorem update_finality_h_max_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (update_finality E cfg K st B).h_max = (SimplexFG.update_finality E cfg st B).h_max := by
  rw [window_update_finality_h_max, KitFG.update_finality_h_max, store_window_height_eq E cfg K
    hK, hOf]

private theorem store_window_update_pair_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    ((update_finality E cfg K st B).h_j, (update_finality E cfg K st B).J) =
      ((SimplexFG.update_finality E cfg st B).h_j,
        (SimplexFG.update_finality E cfg st B).J) := by
  rw [window_update_finality_pair, KitFG.update_finality_pair, store_window_J_eq E cfg K hK,
    store_window_hj_eq E cfg K hK]

/-- One update from the same input has the same selected justification. -/
theorem update_finality_J_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (update_finality E cfg K st B).J = (SimplexFG.update_finality E cfg st B).J :=
  congrArg Prod.snd (store_window_update_pair_eq E cfg K hK st B)

/-- One update from the same input has the same justification height. -/
theorem update_finality_h_j_eq (hK : 2 ≤ K)
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (update_finality E cfg K st B).h_j = (SimplexFG.update_finality E cfg st B).h_j :=
  congrArg Prod.fst (store_window_update_pair_eq E cfg K hK st B)

/-- The refusal tests and tree insertion agree for one step. -/
theorem on_block_TF_eq
    (st : SimplexFG.Store V) (B : FGBlock V) :
    (on_block E cfg K st B).TF = (SimplexFG.on_block E cfg st B).TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [on_block_def, ite_eq_left hc, KitFG.on_block_of_refused E cfg st B hc]
  · rw [on_block_def, ite_eq_right hc, KitFG.on_block_of_accepted E cfg st B hc,
      window_update_finality_TF, KitFG.update_finality_TF]

private theorem store_window_pair_iff (hK : 2 ≤ K) (st : SimplexFG.Store V)
    (hinj : ViewRootInj st.TF)
    (hne : ∃ C ∈ st.TF, FGBlock.Preceq st.F (SimplexFG.derive E cfg C).J) :
    ((∃ C ∈ st.TF, FGBlock.Preceq st.F (projectHeight (derive E cfg K C)).J ∧
      st.h_j = (projectHeight (derive E cfg K C)).h_j ∧
      st.J = (projectHeight (derive E cfg K C)).J) ∧
    (∀ B ∈ st.TF, FGBlock.Preceq st.F (projectHeight (derive E cfg K B)).J →
      lexKey ((projectHeight (derive E cfg K B)).h_j, (projectHeight (derive E cfg K B)).J) ≤
        lexKey (st.h_j, st.J))) ↔ (st.h_j, st.J) = lexMax E cfg st.F st.TF := by
  simp only [projectHeight_def, store_window_J_eq E cfg K hK, store_window_hj_eq E cfg K hK]
  constructor
  · rintro ⟨⟨C, hC, hFC, hh, hJ⟩, hm⟩
    rw [lexMax_eq_of_greatest E cfg st.F st.TF hinj C hC hFC]
    · exact Prod.ext hh hJ
    · simpa only [← hh, ← hJ] using hm
  · intro hp
    obtain ⟨C, hC, hFC, heq, hm⟩ := lexMax_spec E cfg st.F st.TF hinj hne
    have hpair := hp.trans heq
    exact ⟨⟨C, hC, hFC, (Prod.mk.inj hpair).1, (Prod.mk.inj hpair).2⟩,
      fun B hB hFB => hpair ▸ hm B hB hFB⟩

/-- Genesis satisfies every window store field. -/
theorem windowStoreInvariant_init :
    FGStoreInvariant (fun B => projectHeight (derive E cfg K B)) (certificateFinality E cfg K)
      SimplexFG.Store.init := by
  refine ⟨?_, Finset.mem_singleton_self _, Finset.mem_singleton_self _, ?_, ?_,
    preceq_refl _, .genesis, Finset.mem_singleton_self _, rfl⟩
  · intro B hB
    simp only [SimplexFG.Store.init, Finset.mem_singleton] at hB ⊢
    rw [hB]
    rfl
  · change 1 = ({FGBlock.genesis} : Finset (FGBlock V)).sup
      (fun B => (projectHeight (derive E cfg K B)).h) ⊔ 1
    rw [Finset.sup_singleton]
    rfl
  · constructor
    · exact ⟨.genesis, Finset.mem_singleton_self _, preceq_refl _, rfl, rfl⟩
    · intro B hB _
      have hb : B = .genesis := Finset.mem_singleton.mp hB
      subst B
      exact le_refl _

/-- Insertion and the three cache steps preserve the structural invariant. -/
theorem windowStoreInvariant_accept (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K)
    (st : SimplexFG.Store V) (B : FGBlock V)
    (h : FGStoreInvariant (fun B => projectHeight (derive E cfg K B))
      (certificateFinality E cfg K) st) (hpar : B.parent ∈ st.TF)
    (hroots : StoreStepRoots st B) :
    FGStoreInvariant (fun B => projectHeight (derive E cfg K B)) (certificateFinality E cfg K)
      (update_finality E cfg K { st with TF := insert B st.TF } B) := by
  have hTF := window_update_finality_TF E cfg K { st with TF := insert B st.TF } B
  have hsub : st.TF ⊆ insert B st.TF := Finset.subset_insert B st.TF
  obtain ⟨D, hD, hDF⟩ := h.Fcar
  have hne : ∃ C ∈ st.TF, FGBlock.Preceq st.F (SimplexFG.derive E cfg C).J := by
    refine ⟨D, hD, ?_⟩
    rw [← store_window_J_eq E cfg K hK, ← hDF]
    exact window_F_preceq_J E cfg K hne hK D
  have hp := (store_window_pair_iff E cfg K hK st (viewRootInj_mono hroots hsub) hne).mp h.pair
  have hpairJ : ((update_finality E cfg K { st with TF := insert B st.TF } B).h_j,
      (update_finality E cfg K { st with TF := insert B st.TF } B).J) =
      lexMax E cfg st.F (insert B st.TF) := by
    rw [window_update_finality_pair, store_window_hj_eq E cfg K hK, store_window_J_eq E cfg K hK,
      lexMax_insert E cfg st.F st.TF B hroots hne, ← hp]
  have hFJ : FGBlock.Preceq st.F
      (update_finality E cfg K { st with TF := insert B st.TF } B).J := by
    have hj := window_update_finality_pair E cfg K { st with TF := insert B st.TF } B
    dsimp only at hj
    split_ifs at hj with hc
    · rw [(Prod.mk.inj hj).2]
      exact hc.1
    · rw [(Prod.mk.inj hj).2]
      exact h.FJ
  have hne' : ∃ C ∈ insert B st.TF,
      FGBlock.Preceq st.F (SimplexFG.derive E cfg C).J :=
    hne.imp (fun _ hc => ⟨hsub hc.1, hc.2⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTF]
    intro C hC
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact hsub hpar
    · exact hsub (h.closed C hC)
  · rw [hTF]
    exact hsub h.gen
  · rw [hTF]
    rcases window_update_finality_F_cases E cfg K { st with TF := insert B st.TF } B with
      hF | ⟨_, hmem, _, hF⟩
    · rw [hF]
      exact hsub h.Fmem
    · rw [hF]
      exact hmem
  · have hm : st.h_max = frontier E cfg st.TF := by
      simpa only [projectHeight_def, store_window_height_eq E cfg K hK, SimplexFG.frontier, ←
        hOf_eq]
        using h.hmax
    simpa only [hTF, projectHeight_def, store_window_height_eq E cfg K hK, SimplexFG.frontier, ←
      hOf_eq] using
      (show (update_finality E cfg K { st with TF := insert B st.TF } B).h_max =
        frontier E cfg (insert B st.TF) by
          rw [window_update_finality_h_max, store_window_height_eq E cfg K hK,
            frontier_insert, ← hm]
          rfl)
  · have hnew : ∃ C ∈ (update_finality E cfg K { st with TF := insert B st.TF } B).TF,
        FGBlock.Preceq (update_finality E cfg K { st with TF := insert B st.TF } B).F
          (SimplexFG.derive E cfg C).J := by
      obtain ⟨C, hC, _, heq, _⟩ := lexMax_spec E cfg st.F _ hroots hne'
      refine ⟨C, hTF ▸ hC, ?_⟩
      have hj := (Prod.mk.inj (hpairJ.trans heq)).2
      rw [← hj]
      rcases window_update_finality_F_cases E cfg K { st with TF := insert B st.TF } B with
        hF | ⟨_, _, hJ, hF⟩
      · rw [hF]
        exact hFJ
      · rw [hF]
        exact hJ
    apply (store_window_pair_iff E cfg K hK _ (hTF.symm ▸ hroots) hnew).mpr
    rw [hTF]
    rcases window_update_finality_F_cases E cfg K { st with TF := insert B st.TF } B with
      hF | ⟨hadv, _, hJ, hF⟩
    · rw [hF]
      exact hpairJ
    · rw [hF, hpairJ]
      apply (lexMax_of_advance E cfg st.F _ _ hroots hne' hadv ?_).symm
      rw [← hpairJ]
      exact hJ
  · rcases window_update_finality_F_cases E cfg K { st with TF := insert B st.TF } B with
      hF | ⟨_, _, hJ, hF⟩
    · rw [hF]
      exact hFJ
    · rw [hF]
      exact hJ
  · rw [hTF]
    rcases window_update_finality_F_cases E cfg K { st with TF := insert B st.TF } B with
      hF | ⟨_, _, _, hF⟩
    · rw [hF]
      exact ⟨D, hsub hD, hDF⟩
    · rw [hF]
      exact ⟨B, Finset.mem_insert_self B st.TF, rfl⟩

theorem window_on_block_of_refused (st : SimplexFG.Store V) (B : FGBlock V)
    (hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot) :
    on_block E cfg K st B = st := by
  rw [on_block_def]
  rw [ite_eq_left hc]

theorem window_on_block_of_accepted (st : SimplexFG.Store V) (B : FGBlock V)
    (hc : ¬ (B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot)) :
    on_block E cfg K st B = update_finality E cfg K { st with TF := insert B st.TF } B := by
  rw [on_block_def]
  rw [ite_eq_right hc]

theorem window_on_block_F_mono
    (st : SimplexFG.Store V) (B : FGBlock V) :
    FGBlock.Preceq st.F (on_block E cfg K st B).F := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [window_on_block_of_refused E cfg K st B hc]
    exact preceq_refl _
  · rw [window_on_block_of_accepted E cfg K st B hc]
    exact store_window_update_finality_F_mono E cfg K { st with TF := insert B st.TF } B

theorem windowStoreInvariant_on_block (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K)
    (st : SimplexFG.Store V) (B : FGBlock V)
    (h : FGStoreInvariant (fun B => projectHeight (derive E cfg K B))
      (certificateFinality E cfg K) st) (hroots : StoreStepRoots st B) :
    FGStoreInvariant (fun B => projectHeight (derive E cfg K B)) (certificateFinality E cfg K)
      (on_block E cfg K st B) := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [window_on_block_of_refused E cfg K st B hc]
    exact h
  · rw [window_on_block_of_accepted E cfg K st B hc]
    simp only [not_or, not_not, Bool.not_eq_false] at hc
    obtain ⟨-, hpar, -, -⟩ := hc
    exact windowStoreInvariant_accept E cfg K hne hK st B h hpar hroots

theorem window_on_block_TF_subset
    (st : SimplexFG.Store V) (B : FGBlock V) :
    st.TF ⊆ (on_block E cfg K st B).TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [window_on_block_of_refused E cfg K st B hc]
  · rw [window_on_block_of_accepted E cfg K st B hc, window_update_finality_TF]
    exact Finset.subset_insert B st.TF

/-- Window store safety uses its structural invariant as the good-state predicate. -/
theorem windowStoreSafety (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) :
    FGStoreSafety E (fun B => projectHeight (derive E cfg K B)) (certificateFinality E cfg K)
      (id : SimplexFG.Store V → SimplexFG.Store V)
      (fun _ B => (projectHeight (derive E cfg K B), certificateFinality E cfg K B))
      SimplexFG.Store.init (on_block E cfg K)
      (FGStoreInvariant (fun B => projectHeight (derive E cfg K B)) (certificateFinality E cfg K))
        StoreStepRoots :=
  FGStoreSafety.of_certificate E _ _ (windowCertificateLaws E cfg K hne hK)
    id _ SimplexFG.Store.init (on_block E cfg K)
    (FGStoreInvariant (fun B => projectHeight (derive E cfg K B)) (certificateFinality E cfg K))
      StoreStepRoots
    (windowStoreInvariant_init E cfg K) (fun _ hi => hi)
    (windowStoreInvariant_on_block E cfg K hne hK)
    (fun st B _ => window_on_block_TF_subset E cfg K st B)
    (fun st B _ => window_on_block_F_mono E cfg K st B) (fun _ _ _ _ => rfl)

end AvailableChain.KitFG.Window
end
