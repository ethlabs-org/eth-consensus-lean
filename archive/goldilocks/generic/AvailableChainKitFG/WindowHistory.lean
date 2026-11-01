module
public import AvailableChainKitFG.WindowCertificates

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [DecidableEq V] [RowCodec V] in
private theorem b3History_final_fields (E : Electorate V) (_cfg : FGConfig) (w : State V) :
    (finalizeWindow E w).h = w.h ∧
    (finalizeWindow E w).T_h = w.T_h ∧
    (finalizeWindow E w).h_j = w.h_j ∧
    (finalizeWindow E w).J = w.J ∧
    (finalizeWindow E w).W =
      w.W.filter (fun e => decide ((finalizeWindow E w).h_F < e.j)) := by
  rw [finalizeWindow_def]
  cases greatestReady E w <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [RowCodec V] in
private theorem b3History_events_finality (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : State
      V) :
    (process_height_events E cfg K w).F = (finalizeWindow E w).F ∧
    (process_height_events E cfg K w).h_F = (finalizeWindow E w).h_F := by
  rw [process_height_events_def]
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- Every nonzero finalized pair was born on this chain, including pairs
whose older entries have already left the window. -/
theorem window_final_birth (E : Electorate V) (cfg : FGConfig) (K : Nat) (_hne : ¬ E.IsQuorum ∅)
      (hK : 2 ≤ K)
    (B : FGBlock V) (hnz : (derive E cfg K B).h_F ≠ 0) :
    ∃ C, FGBlock.Preceq C B ∧ JustificationBirth E (certificateHeight E cfg K)
      C (derive E cfg K B).h_F (derive E cfg K B).F := by
  induction B with
  | genesis => exact (hnz rfl).elim
  | node P s r_s x rs ih =>
      let B := FGBlock.node P s r_s x rs
      let w := certificateFolded E cfg K B
      have ff := window_fold_fields rs { derive E cfg K P with s := s }
      have ef := b3History_events_finality E cfg K w
      change (derive E cfg K B).F = _ ∧ (derive E cfg K B).h_F = _ at ef
      rw [ef.2] at hnz
      rw [ef.1, ef.2]
      cases hg : greatestReady E w with
      | none =>
          have hF : (finalizeWindow E w).F = (derive E cfg K P).F := by
            rw [finalizeWindow_def, hg]; exact ff.2.2.2.2.2.2
          have hh : (finalizeWindow E w).h_F = (derive E cfg K P).h_F := by
            rw [finalizeWindow_def, hg]; exact ff.2.2.2.2.2.1
          rw [hh, hF]
          obtain ⟨C, hc, hb⟩ := ih (hh ▸ hnz)
          exact ⟨C, preceq_node_of_preceq s r_s x rs hc, hb⟩
      | some d =>
          obtain ⟨C, hc, hb, _⟩ := window_prefinal_entry_origin E cfg K hK B d
            ((window_greatest_spec E w).1 d hg).1
          refine ⟨C, hc.1, ?_⟩
          simpa only [finalizeWindow_def, hg] using hb

private theorem b3History_birth_geometry (E : Electorate V) (cfg : FGConfig) (K : Nat) (_hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    {C X : FGBlock V} {j : Height}
    (hb : JustificationBirth E (certificateHeight E cfg K) C j X) :
    FGBlock.Preceq X C ∧ (certificateHeight E cfg K X).h = j ∧
      (certificateHeight E cfg K X).T_h = X := by
  have laws : FGHeightLaws E (certificateHeight E cfg K) := windowHeightLaws E cfg K hK
  refine ⟨?_, ?_, ?_⟩
  · rw [← hb.2.2.1]
    apply preceq_trans (laws.entry_preceq C.parent)
    cases C with
    | genesis => exact preceq_refl _
    | node P s r_s x rs => exact preceq_parent_node P s r_s x rs
  · rw [← hb.2.2.1, laws.entry_same_height, hb.2.1]
  · rw [← hb.2.2.1, laws.entry_idem]

private theorem b3History_birth_order (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    {B C D X Y : FGBlock V} {j k : Height}
    (hC : FGBlock.Preceq C B) (hD : FGBlock.Preceq D B)
    (hbC : JustificationBirth E (certificateHeight E cfg K) C j X)
    (hbD : JustificationBirth E (certificateHeight E cfg K) D k Y)
    (hjk : j ≤ k) : FGBlock.Preceq X Y := by
  have c := b3History_birth_geometry E cfg K hne hK hbC
  have d := b3History_birth_geometry E cfg K hne hK hbD
  rcases preceq_total_of_common (preceq_trans c.1 hC) (preceq_trans d.1 hD) with h | h
  · exact h
  · have laws : FGHeightLaws E (certificateHeight E cfg K) := windowHeightLaws E cfg K hK
    have hm := laws.h_mono h
    have heq : (certificateHeight E cfg K Y).h = (certificateHeight E cfg K X).h := by
      change (certificateHeight E cfg K Y).h ≤ (certificateHeight E cfg K X).h at hm
      rw [d.2.1, c.2.1] at hm ⊢
      exact Nat.le_antisymm hm hjk
    have ht := laws.entry_plateau h heq
    change (certificateHeight E cfg K Y).T_h = (certificateHeight E cfg K X).T_h at ht
    rw [c.2.2, d.2.2] at ht
    rw [ht]
    exact preceq_refl _

/-- [bp §3.1; bp 22 I7] Every old key at or below finality is covered, even if
capacity removed it earlier. Birth order supplies the ancestry claim. -/
theorem window_le_hF_covered (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
      (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (hle : e.j ≤ (derive E cfg K B).h_F) : FGBlock.Preceq e.X (derive E cfg K B).F := by
  have hb := window_bounds E cfg K hne hK A e he
  have hnz : (derive E cfg K B).h_F ≠ 0 := Nat.ne_of_gt ((Nat.zero_lt_of_lt hb.1).trans_le hle)
  obtain ⟨C, hc, hbirth, _⟩ := window_entry_origin E cfg K hK A e he
  obtain ⟨D, hd, hfinal⟩ := window_final_birth E cfg K hne hK B hnz
  exact b3History_birth_order E cfg K hne hK (preceq_trans hc hAB) hd hbirth hfinal hle

/-- [bp §3.1; bp 22 I7] The absent-key form of `window_le_hF_covered`. Absence is
not used; the form matches the COVERED case of `window_entry_history`. -/
theorem window_absent_le_hF_covered (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (gone : ¬ ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X)
    (hle : e.j ≤ (derive E cfg K B).h_F) : FGBlock.Preceq e.X (derive E cfg K B).F := by
  have _absent := gone
  exact window_le_hF_covered E cfg K hne hK A B hAB e he hle

/-- At B an absent key that is not covered is strictly above finality.
This does not assert that it stays uncovered at later blocks. -/
theorem window_evicted_above_hF (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
      ∅) (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (gone : ¬ ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X)
    (uncovered : ¬ (e.j ≤ (derive E cfg K B).h_F ∧ FGBlock.Preceq e.X (derive E cfg K B).F)) :
    (derive E cfg K B).h_F < e.j := by
  by_contra h
  have hle := Nat.le_of_not_gt h
  exact uncovered ⟨hle, window_absent_le_hF_covered E cfg K hne hK A B hAB e he gone hle⟩

/-- [bp §3.1] Retention at both ends forbids a gap and preserves all bits. -/
theorem window_retained_bits_mono (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (A B C : FGBlock V) (hAB : FGBlock.Preceq A B) (hBC : FGBlock.Preceq B C)
    (e d : Entry V) (he : e ∈ (derive E cfg K A).W) (hd : d ∈ (derive E cfg K C).W)
    (hj : d.j = e.j) (hX : d.X = e.X) :
    ∃ b ∈ (derive E cfg K B).W, b.j = e.j ∧ b.X = e.X ∧ e.Q ⊆ b.Q ∧ b.Q ⊆ d.Q := by
  have present : ∃ b ∈ (derive E cfg K B).W, b.j = e.j ∧ b.X = e.X := by
    by_contra gone
    exact window_no_reentry E cfg K hne hK A B C hAB hBC e he gone ⟨d, hd, hj, hX⟩
  obtain ⟨b, hb, hbj, hbX⟩ := present
  exact ⟨b, hb, hbj, hbX,
    window_bit_retained E cfg K hne hK A B hAB e b he hb hbj.symm hbX.symm,
    window_bit_retained E cfg K hne hK B C hBC b d hb hd (hbj.trans hj.symm) (hbX.trans hX.symm)⟩

/-- [spec 605–607] A step keeps the latest pair unless it crosses a target
quorum. Pruning does not clear the pair; a capacity append writes a new pair. -/
theorem window_latest_pair_kept (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) :
    let B := FGBlock.node P s r_s x rs
    let w := certificateFolded E cfg K B
    ((derive E cfg K B).h_j = (derive E cfg K P).h_j ∧
      (derive E cfg K B).J = (derive E cfg K P).J ∧
      targetQuorum E (finalizeWindow E w) = false) ∨
    ((derive E cfg K B).h_j = (derive E cfg K P).h ∧
      (derive E cfg K B).J = (derive E cfg K P).T_h ∧
      targetQuorum E (finalizeWindow E w) = true) := by
  dsimp only
  have ff := window_fold_fields rs { derive E cfg K P with s := s }
  have fin := b3History_final_fields E cfg (certificateFolded E cfg K (.node P s r_s x rs))
  simp only [derive_def E cfg K (.node P s r_s x rs), transition_def, process_height_events_def]
  split_ifs with ht
  · exact Or.inr ⟨fin.1.trans ff.2.1, fin.2.1.trans ff.2.2.1, ht⟩
  · exact Or.inl ⟨fin.2.2.1.trans ff.2.2.2.1, fin.2.2.2.1.trans ff.2.2.2.2.1,
      Bool.eq_false_iff.mpr ht⟩
  · exact Or.inl ⟨fin.2.2.1.trans ff.2.2.2.1, fin.2.2.2.1.trans ff.2.2.2.2.1,
      Bool.eq_false_iff.mpr ht⟩

omit [Fintype V] [RowCodec V] in
private theorem b3History_drop_oldest (K : Nat) (xs : List (Entry V))
    (new e : Entry V) (hcap : xs.length ≤ K)
    (hord : (xs ++ [new]).Pairwise (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X))
    (he : e ∈ xs) (gone : e ∉ (xs ++ [new]).drop ((xs ++ [new]).length - K)) :
    ((xs ++ [new]).drop ((xs ++ [new]).length - K)).length = K ∧
    ∀ d ∈ (xs ++ [new]).drop ((xs ++ [new]).length - K), e.j < d.j := by
  have hlen : (xs ++ [new]).length = K + 1 := by
    simp only [List.length_append, List.length_singleton]
    by_contra h
    have hz : (xs ++ [new]).length - K = 0 := by
      simp only [List.length_append, List.length_singleton]; omega
    exact gone (by simpa only [hz, List.drop_zero] using List.mem_append_left [new] he)
  have hdrop : (xs ++ [new]).length - K = 1 := by omega
  rw [hdrop] at gone ⊢
  constructor
  · simp only [List.length_drop]; omega
  · cases xs with
    | nil => simp at he
    | cons a xs =>
        have hea : e = a := by
          rcases List.mem_cons.mp he with h | h
          · exact h
          · exact (gone (by simpa using List.mem_append_left [new] h)).elim
        subst e
        change (a :: (xs ++ [new])).Pairwise _ at hord
        exact fun d hd => ((List.pairwise_cons.mp hord).1 d hd).1

private theorem b3History_node_evicted (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (e : Entry V) (he : e ∈ (derive E cfg K P).W)
    (gone : ¬ ∃ d ∈ (derive E cfg K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X)
    (above : (derive E cfg K (.node P s r_s x rs)).h_F < e.j) :
    (derive E cfg K (.node P s r_s x rs)).W.length = K ∧
    ∀ d ∈ (derive E cfg K (.node P s r_s x rs)).W, e.j < d.j := by
  let B := FGBlock.node P s r_s x rs
  let w := certificateFolded E cfg K B
  let f := finalizeWindow E w
  let d := rs.foldl (fun e a => window_addBit a e) e
  have ff := window_fold_fields rs { derive E cfg K P with s := s }
  have dk := window_fold_entry rs e
  have fin := b3History_final_fields E cfg w
  have ef := b3History_events_finality E cfg K w
  have dw : d ∈ w.W := by
    change d ∈ (rs.foldl process_row { derive E cfg K P with s := s }).W
    rw [ff.1]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have df : d ∈ f.W := by
    rw [fin.2.2.2.2, List.mem_filter]
    refine ⟨dw, decide_eq_true ?_⟩
    rw [← ef.2, dk.1]
    exact above
  have cap : f.W.length ≤ K := by
    rw [fin.2.2.2.2]
    refine (List.length_filter_le _ _).trans ?_
    change (rs.foldl process_row { derive E cfg K P with s := s }).W.length ≤ K
    rw [ff.1, List.length_map]
    exact window_capacity E cfg K hne hK P
  have ord : f.W.Pairwise (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X) := by
    rw [fin.2.2.2.2]
    apply List.Pairwise.filter
    change (rs.foldl process_row { derive E cfg K P with s := s }).W.Pairwise _
    rw [ff.1, List.pairwise_map]
    exact (window_ordered E cfg K hne hK P).imp (fun {a b} h => by
      simpa only [(window_fold_entry rs a).1, (window_fold_entry rs a).2.1,
        (window_fold_entry rs b).1, (window_fold_entry rs b).2.1] using h)
  have fh : w.h = (derive E cfg K P).h := ff.2.1
  have fT : w.T_h = (derive E cfg K P).T_h := ff.2.2.1
  have newer : ∀ a ∈ f.W, a.j < f.h ∧ FGBlock.Preceq a.X f.T_h := by
    intro a ha
    have haw := (List.mem_filter.mp (fin.2.2.2.2 ▸ ha)).1
    change a ∈ (rs.foldl process_row { derive E cfg K P with s := s }).W at haw
    rw [ff.1, List.mem_map] at haw
    obtain ⟨c, hc, rfl⟩ := haw
    have cb := window_bounds E cfg K hne hK P c hc
    have laws := windowHeightLaws E cfg K hK
    exact ⟨by rw [(window_fold_entry rs c).1, fin.1, fh]
              exact cb.2.1.trans_lt (laws.justified_below_height P),
      by rw [(window_fold_entry rs c).2.1, fin.2.1, fT]
         exact preceq_trans cb.2.2.2 (laws.justified_preceq_entry P)⟩
  have appendOrd : (f.W ++ [Entry.mk f.h f.T_h ∅]).Pairwise
      (fun a b => a.j < b.j ∧ FGBlock.Preceq a.X b.X) := by
    rw [List.pairwise_append]
    exact ⟨ord, by simp, fun a ha b hb => List.mem_singleton.mp hb ▸ newer a ha⟩
  change (process_height_events E cfg K w).W.length = K ∧
    ∀ d ∈ (process_height_events E cfg K w).W, e.j < d.j
  change ¬ ∃ d ∈ (process_height_events E cfg K w).W, _ at gone
  rw [process_height_events_def] at gone ⊢
  dsimp only at gone ⊢
  split_ifs at gone ⊢ with ht hp
  · have gd : d ∉ (f.W ++ [Entry.mk f.h f.T_h ∅]).drop
        ((f.W ++ [Entry.mk f.h f.T_h ∅]).length - K) := by
      intro hd
      exact gone ⟨d, hd, dk.1, dk.2.1⟩
    obtain ⟨hl, hn⟩ := b3History_drop_oldest K f.W _ d cap appendOrd df gd
    exact ⟨hl, fun a ha => dk.1 ▸ hn a ha⟩
  · exact (gone ⟨d, df, dk.1, dk.2.1⟩).elim
  · exact (gone ⟨d, df, dk.1, dk.2.1⟩).elim

/-- A capacity removal leaves exactly K newer entries. Each has a birth
strictly after the removed entry's birth on the same chain. -/
theorem window_evicted_has_K_newer (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (e : Entry V) (he : e ∈ (derive E cfg K P).W)
    (gone : ¬ ∃ d ∈ (derive E cfg K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X)
    (above : (derive E cfg K (.node P s r_s x rs)).h_F < e.j) :
    (derive E cfg K (.node P s r_s x rs)).W.length = K ∧
    ∃ C, FGBlock.Preceq C P ∧
      JustificationBirth E (certificateHeight E cfg K) C e.j e.X ∧
      ∀ d ∈ (derive E cfg K (.node P s r_s x rs)).W, e.j < d.j ∧
        ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
          JustificationBirth E (certificateHeight E cfg K) D d.j d.X := by
  obtain ⟨hl, hn⟩ := b3History_node_evicted E cfg K hne hK P s r_s x rs e he gone above
  obtain ⟨C, hc, hb, _⟩ := window_entry_origin E cfg K hK P e he
  refine ⟨hl, C, hc, hb, ?_⟩
  intro d hd
  obtain ⟨D, hD, hbirth, _⟩ := window_entry_origin E cfg K hK (.node P s r_s x rs) d hd
  have hlt := hn d hd
  have heights : (certificateHeight E cfg K C).h < (certificateHeight E cfg K D).h := by
    rw [hb.2.2.2.2.2.1, hbirth.2.2.2.2.2.1]
    exact Nat.succ_lt_succ hlt
  have hCD : FGBlock.Preceq C D := by
    rcases preceq_total_of_common (preceq_node_of_preceq s r_s x rs hc) hD with h | h
    · exact h
    · exact (Nat.not_lt_of_ge ((windowHeightLaws E cfg K hK).h_mono h) heights).elim
  exact ⟨hlt, D, ⟨hCD, fun h => by simp only [h, lt_self_iff_false] at heights⟩, hD, hbirth⟩

private theorem b3History_first_removal (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (gone : ¬ ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X) :
    ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
      (∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X) ∧
      ¬ ∃ d ∈ (derive E cfg K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X := by
  induction B with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAB
      exact (gone ⟨e, he, rfl, rfl⟩).elim
  | node P s r_s x rs ih =>
      by_cases ha : A = .node P s r_s x rs
      · subst A
        exact (gone ⟨e, he, rfl, rfl⟩).elim
      · have hAP := preceq_parent_of_preceq_node hAB ha
        by_cases hp : ∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X
        · exact ⟨P, s, r_s, x, rs, hAP, preceq_refl _, hp, gone⟩
        · obtain ⟨R, t, r_t, y, rows, hAR, hRP, hr, hg⟩ := ih hAP hp
          exact ⟨R, t, r_t, y, rows, hAR, preceq_node_of_preceq s r_s x rs hRP, hr, hg⟩

/-- [07-F entry] The cases refer to B's state and are exclusive by key
presence and coverage. A later finalization can cover an earlier eviction. -/
theorem window_entry_history (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
      (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W) :
    (∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q) ∨
    ((¬ ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X) ∧
      e.j ≤ (derive E cfg K B).h_F ∧ FGBlock.Preceq e.X (derive E cfg K B).F) ∨
    ((¬ ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X) ∧
      ¬ (e.j ≤ (derive E cfg K B).h_F ∧ FGBlock.Preceq e.X (derive E cfg K B).F) ∧
      (derive E cfg K B).h_F < e.j ∧
      ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
        (∃ d ∈ (derive E cfg K P).W, d.j = e.j ∧ d.X = e.X) ∧
        (¬ ∃ d ∈ (derive E cfg K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X) ∧
        (derive E cfg K (.node P s r_s x rs)).W.length = K ∧
        ∃ C, FGBlock.Preceq C P ∧
          JustificationBirth E (certificateHeight E cfg K) C e.j e.X ∧
          ∀ d ∈ (derive E cfg K (.node P s r_s x rs)).W, e.j < d.j ∧
            ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
              JustificationBirth E (certificateHeight E cfg K) D d.j d.X) := by
  by_cases present : ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X
  · obtain ⟨d, hd, hj, hX⟩ := present
    exact Or.inl ⟨d, hd, hj, hX,
      window_bit_retained E cfg K hne hK A B hAB e d he hd hj.symm hX.symm⟩
  · by_cases covered : e.j ≤ (derive E cfg K B).h_F ∧ FGBlock.Preceq e.X (derive E cfg K B).F
    · exact Or.inr (Or.inl ⟨present, covered⟩)
    · have above := window_evicted_above_hF E cfg K hne hK A B hAB e he present covered
      obtain ⟨P, s, r_s, x, rs, hAP, hPB, hp, hg⟩ := b3History_first_removal E cfg K A B hAB e he
        present
      obtain ⟨d, hd, hj, hX⟩ := hp
      have stepAbove : (derive E cfg K (.node P s r_s x rs)).h_F < d.j := by
        rw [hj]
        exact (window_hF_mono E cfg K hne hK _ _ hPB).trans_lt above
      have stepGone : ¬ ∃ a ∈ (derive E cfg K (.node P s r_s x rs)).W,
          a.j = d.j ∧ a.X = d.X := by simpa only [hj, hX] using hg
      have ev := window_evicted_has_K_newer E cfg K hne hK P s r_s x rs d hd stepGone stepAbove
      rw [hj, hX] at ev
      exact Or.inr (Or.inr ⟨present, covered, above, P, s, r_s, x, rs, hAP, hPB,
        ⟨d, hd, hj, hX⟩, hg, ev⟩)

end AvailableChain.KitFG.Window
end
