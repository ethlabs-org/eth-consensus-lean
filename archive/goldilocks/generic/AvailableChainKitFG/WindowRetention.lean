module
public import AvailableChainKitFG.WindowLiveness

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Latest justification height keeps its value or increases at a target crossing. -/
theorem window_hj_mono (E : Electorate V) (cfg : FGConfig) (K : Nat) (_hne : ¬ E.IsQuorum ∅) (hK :
      2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B) :
    (derive E cfg K A).h_j ≤ (derive E cfg K B).h_j := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact Nat.le_refl _
  | node P s r_s x rs ih =>
      by_cases hA : A = .node P s r_s x rs
      · subst A
        exact Nat.le_refl _
      · apply (ih (preceq_parent_of_preceq_node hAB hA)).trans
        rcases window_latest_pair_kept E cfg K P s r_s x rs with h | h
        · exact h.1.ge
        · rw [h.1]
          exact Nat.le_of_lt ((windowHeightLaws E cfg K hK).justified_below_height P)

private theorem b3Retention_retentionHeight_count (E : Electorate V) (cfg : FGConfig) (K : Nat)
      (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K)
    (B : FGBlock V) (y : Nat) (S : Finset Nat)
    (cover : ∀ d ∈ (derive E cfg K B).W, y < d.j → d.j ∈ S) :
    ((derive E cfg K B).W.filter (fun d => decide (y < d.j))).length ≤ S.card := by
  let xs := (derive E cfg K B).W.filter (fun d => decide (y < d.j))
  have ord : (xs.map Entry.j).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact ((window_ordered E cfg K hne hK B).filter _).imp (fun h => h.1)
  have sub : (xs.map Entry.j).toFinset ⊆ S := by
    intro j hj
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    obtain ⟨hd, hy⟩ := List.mem_filter.mp hd
    exact cover d hd (of_decide_eq_true hy)
  have count := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup ord.nodup, List.length_map] at count
  exact count

/-- [plan item 12] Finality below the key and a latest height below y + K
keep the key and all its bits. The step bounds follow by monotonicity. -/
theorem window_retained_of_scalar (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (A P : FGBlock V) (hAP : FGBlock.Preceq A P)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (above : (derive E cfg K P).h_F < e.j)
    (near : (derive E cfg K P).h_j < e.j + K) :
    ∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have small : (derive E cfg K P).h_j - e.j < K :=
    Nat.sub_lt_left_of_lt_add
      (((window_bounds E cfg K hne hK A e he).2.1).trans (window_hj_mono E cfg K hne hK A P hAP))
      near
  apply window_retained_along E cfg K hne hK A P hAP e he
  intro R s r_s x rs _ hBP
  refine ⟨(window_hF_mono E cfg K hne hK _ _ hBP).trans_lt above, ?_⟩
  have bound := b3Retention_retentionHeight_count E cfg K hne hK (.node R s r_s x rs) e.j
    (Finset.Ioc e.j (derive E cfg K P).h_j) (fun d hd hy =>
      Finset.mem_Ioc.mpr ⟨hy, ((window_bounds E cfg K hne hK _ d hd).2.1).trans
        (window_hj_mono E cfg K hne hK _ _ hBP)⟩)
  rw [Nat.card_Ioc] at bound
  exact bound.trans_lt small

/-- A key remains with all its bits, or finality covers it, when the latest
justification height is less than its height plus K. -/
theorem window_retained_or_covered (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (A P : FGBlock V) (hAP : FGBlock.Preceq A P)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (near : (derive E cfg K P).h_j < e.j + K) :
    (∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q) ∨
      (e.j ≤ (derive E cfg K P).h_F ∧ FGBlock.Preceq e.X (derive E cfg K P).F) := by
  rcases window_entry_history E cfg K hne hK A P hAP e he with retained | covered | evicted
  · exact Or.inl retained
  · exact Or.inr covered.2
  · obtain ⟨_, _, _, R, s, r_s, x, rs, _, hBP, _, _, full, C, _, _, newer⟩ := evicted
    have small : (derive E cfg K P).h_j - e.j < K :=
      Nat.sub_lt_left_of_lt_add
        (((window_bounds E cfg K hne hK A e he).2.1).trans (window_hj_mono E cfg K hne hK A P
      hAP)) near
    have bound := b3Retention_retentionHeight_count E cfg K hne hK (.node R s r_s x rs) e.j
      (Finset.Ioc e.j (derive E cfg K P).h_j) (fun d hd hy =>
        Finset.mem_Ioc.mpr ⟨hy, ((window_bounds E cfg K hne hK _ d hd).2.1).trans
          (window_hj_mono E cfg K hne hK _ _ hBP)⟩)
    have allNewer : ((derive E cfg K (.node R s r_s x rs)).W.filter
        (fun d => decide (e.j < d.j))) = (derive E cfg K (.node R s r_s x rs)).W := by
      apply List.filter_eq_self.mpr
      exact fun d hd => decide_eq_true (newer d hd).1
    rw [allNewer, full, Nat.card_Ioc] at bound
    exact (Nat.not_lt_of_ge bound small).elim

private theorem b3Retention_retentionBirth_entry (E : Electorate V) (cfg : FGConfig) (K : Nat)
      (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K)
    (C : FGBlock V) (j : Nat) (X : FGBlock V)
    (birth : JustificationBirth E (certificateHeight E cfg K) C j X) :
    (Entry.mk j X ∅) ∈ (derive E cfg K C).W := by
  cases C with
  | genesis => exact (birth.1 rfl).elim
  | node P s r_s x rs =>
      have hp : (derive E cfg K P).h = j := birth.2.1
      have hcj : (derive E cfg K (.node P s r_s x rs)).h_j = j := birth.2.2.2.1
      have hcX : (derive E cfg K (.node P s r_s x rs)).J = X := birth.2.2.2.2.1
      have ht : targetQuorum E
          (finalizeWindow E (certificateFolded E cfg K (.node P s r_s x rs))) = true := by
        rcases window_latest_pair_kept E cfg K P s r_s x rs with kept | crossed
        · have below := (windowHeightLaws E cfg K hK).justified_below_height P
          change (derive E cfg K P).h_j < (derive E cfg K P).h at below
          rw [← kept.1, hcj, hp] at below
          exact (Nat.lt_irrefl j below).elim
        · exact crossed.2.2
      have latest : (derive E cfg K (.node P s r_s x rs)).h_j =
          (finalizeWindow E (certificateFolded E cfg K (.node P s r_s x rs))).h ∧
          (derive E cfg K (.node P s r_s x rs)).J =
          (finalizeWindow E (certificateFolded E cfg K (.node P s r_s x rs))).T_h := by
        change (process_height_events E cfg K
            (certificateFolded E cfg K (.node P s r_s x rs))).h_j = _ ∧
          (process_height_events E cfg K
            (certificateFolded E cfg K (.node P s r_s x rs))).J = _
        rw [process_height_events_def, ite_eq_left ht]
        exact ⟨rfl, rfl⟩
      have hj := latest.1.symm.trans hcj
      have hX := latest.2.symm.trans hcX
      obtain ⟨_, older, appended, _, _⟩ := window_target_appended_newest E cfg K hne hK P s r_s x
        rs ht
      rw [hj, hX] at appended
      rw [appended]
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- [bp 01:161–173] R3 and R6W place each exact row after the key's birth.
Retention then preserves the row's bit through B. -/
theorem window_exact_row_no_missing_effect (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (B : FGBlock V) (y : Nat) (U : FGBlock V)
    (d : Entry V) (hd : d ∈ (derive E cfg K B).W)
    (hj : d.j = y) (hX : d.X = U)
    (valid : ∀ P s r_s x rs, FGBlock.Preceq (.node P s r_s x rs) B → ∀ a ∈ rs,
      (match a.height_pair with
        | .empty => false
        | .vote h _ _ => decide (1 ≤ h) &&
            (a.finality_pair.map (fun fp => decide (fp.height < h))).getD true) = true ∧ r6w
      (derive E cfg K P) a = true)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (hCB : FGBlock.Preceq (.node P s r_s x rs) B)
    (a : Row V) (ha : a ∈ rs)
    (hpair : a.finality_pair = some ⟨y, U.root⟩) : a.signer ∈ d.Q := by
  obtain ⟨hr3, hr6⟩ := valid P s r_s x rs hCB a ha
  have below : y < (derive E cfg K P).h := by
    cases hp : a.height_pair with
    | empty =>
        rw [hp] at hr3
        change false = true at hr3
        contradiction
    | vote h T t =>
        rw [hp, hpair] at hr3
        change (decide (1 ≤ h) && decide (y < h)) = true at hr3
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hr3
        have hf := hr3.2
        rw [r6w_def] at hr6
        simp only [Bool.or_eq_true] at hr6
        rcases hr6 with hm | hs
        · have hm' : h = (derive E cfg K P).h := by
            simp only [heightMatch_def, hp, NamedHeightPair.matchesEntry,
              decide_eq_true_eq] at hm
            exact hm.1
          exact hm' ▸ hf
        · have hs' : h < (derive E cfg K P).h := by
            simp only [staleUseful_def, hp, hpair, Bool.and_eq_true,
              decide_eq_true_eq] at hs
            exact hs.1.2
          exact hf.trans hs'
  obtain ⟨C, hC, birth, _⟩ := window_entry_origin E cfg K hK B d hd
  have hCP : FGBlock.Preceq C P := by
    cases C with
    | genesis => exact (birth.1 rfl).elim
    | node R t r_t z rows =>
        have hb : (derive E cfg K R).h = y := birth.2.1.trans hj
        have ne : FGBlock.node P s r_s x rs ≠ .node R t r_t z rows := by
          intro eq
          have ep : P = R := (FGBlock.node.inj eq).1
          rw [ep, hb] at below
          exact (Nat.lt_irrefl y) below
        rcases preceq_total_of_common hCB hC with before | after
        · have hPR := preceq_trans (preceq_parent_node P s r_s x rs)
            (preceq_parent_of_preceq_node before ne)
          have hm := (windowHeightLaws E cfg K hK).h_mono hPR
          change (derive E cfg K P).h ≤ (derive E cfg K R).h at hm
          rw [hb] at hm
          exact (Nat.not_lt_of_ge hm below).elim
        · exact preceq_parent_of_preceq_node after (Ne.symm ne)
  have born := b3Retention_retentionBirth_entry E cfg K hne hK C d.j d.X birth
  have hPB := preceq_trans (preceq_parent_node P s r_s x rs) hCB
  obtain ⟨e, he, hej, heX, _, _⟩ := window_retained_bits_mono E cfg K hne hK C P B
    hCP hPB ⟨d.j, d.X, ∅⟩ d born hd rfl rfl
  obtain ⟨c, hc, hcj, hcX, _, _⟩ := window_retained_bits_mono E cfg K hne hK P
    (.node P s r_s x rs) B (preceq_parent_node P s r_s x rs) hCB e d he hd hej.symm heX.symm
  have bit := window_bit_add_of_row E cfg K hne hK P s r_s x rs e c he hc hcj hcX a ha
    (by simpa only [hej, heX, hj, hX] using hpair)
  exact window_bit_retained E cfg K hne hK (.node P s r_s x rs) B hCB c d hc hd
    (hcj.trans hej) (hcX.trans heX) bit

/-- [plan item 12] A finite set covers all births with certificate height
above the protected key up to P. Fewer than K such births prevents eviction.
The set may overestimate the births; no gap in certificate heights is required. -/
theorem window_retained_of_few_births (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (A P : FGBlock V) (hAP : FGBlock.Preceq A P)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (above : (derive E cfg K P).h_F < e.j)
    (births : Finset (FGBlock V)) (few : births.card < K)
    (cover : ∀ C j X, FGBlock.Preceq C P → e.j < j →
      JustificationBirth E (certificateHeight E cfg K) C j X → C ∈ births) :
    ∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  apply window_retained_along E cfg K hne hK A P hAP e he
  intro R s r_s x rs _ hBP
  refine ⟨(window_hF_mono E cfg K hne hK _ _ hBP).trans_lt above, ?_⟩
  apply lt_of_le_of_lt (b3Retention_retentionHeight_count E cfg K hne hK (.node R s r_s x rs) e.j
    (births.image (fun C => (derive E cfg K C).h_j)) ?_)
    ((Finset.card_image_le).trans_lt few)
  intro d hd hy
  obtain ⟨C, hC, hb, _⟩ := window_entry_origin E cfg K hK _ d hd
  exact Finset.mem_image.mpr ⟨C, cover C d.j d.X (preceq_trans hC hBP) hy hb,
    hb.2.2.2.1⟩

/-- [bp 22:1265–1272] A latest retained height survives at most one later
birth while finality stays below it. This is a fold fact with explicit bounds. -/
theorem window_retained_fresh_one_newer (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (A P : FGBlock V) (hAP : FGBlock.Preceq A P)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (latest : e.j = (derive E cfg K A).h_j)
    (above : (derive E cfg K P).h_F < e.j)
    (births : Finset (FGBlock V)) (one : births.card ≤ 1)
    (cover : ∀ C j X, StrictPrefix A C → FGBlock.Preceq C P →
      JustificationBirth E (certificateHeight E cfg K) C j X → C ∈ births) :
    ∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  apply window_retained_of_few_births E cfg K hne hK A P hAP e he above births (by omega)
  intro C j X hCP hj hb
  have hAC : StrictPrefix A C := by
    have hcj : (derive E cfg K C).h_j = j := hb.2.2.2.1
    rcases preceq_total_of_common hAP hCP with h | h
    · refine ⟨h, ?_⟩
      intro eq
      rw [latest, eq, hcj] at hj
      exact (Nat.lt_irrefl j) hj
    · have hm := window_hj_mono E cfg K hne hK C A h
      rw [hcj, ← latest] at hm
      exact (Nat.not_lt_of_ge hm hj).elim
  exact cover C j X hAC hCP hb

end AvailableChain.KitFG.Window
end
