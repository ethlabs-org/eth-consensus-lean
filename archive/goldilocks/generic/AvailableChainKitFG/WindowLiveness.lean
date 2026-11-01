module
public import AvailableChainKitFG.WindowHistory

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [RowCodec V]

private def b3Liveness_livenessAddBit (a : Row V) (e : Entry V) : Entry V :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then { e with Q := insert a.signer e.Q } else e

private theorem b3Liveness_livenessAddBit_key (a : Row V) (e : Entry V) :
    (b3Liveness_livenessAddBit a e).j = e.j ∧ (b3Liveness_livenessAddBit a e).X = e.X := by
  unfold b3Liveness_livenessAddBit
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem b3Liveness_livenessAddBit_bits (a : Row V) (e : Entry V) (i : V) :
    i ∈ (b3Liveness_livenessAddBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  unfold b3Liveness_livenessAddBit
  split_ifs with h <;> simp [h, eq_comm, or_comm]

private theorem b3Liveness_livenessRow_fields (w : State V) (a : Row V) :
    (process_row w a).W = w.W.map (b3Liveness_livenessAddBit a) ∧
    (process_row w a).h = w.h := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [process_row_def, NamedHeightPair.matchesEntry]
      exact ⟨rfl, rfl⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def] <;> split_ifs <;> exact ⟨rfl, rfl⟩

private theorem b3Liveness_livenessFold_fields (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W =
      w.W.map (fun e => rs.foldl (fun e a => b3Liveness_livenessAddBit a e) e) ∧
    (rs.foldl process_row w).h = w.h := by
  induction rs generalizing w with
  | nil => simp
  | cons a rs ih =>
      have h := b3Liveness_livenessRow_fields w a
      have t := ih (process_row w a)
      simpa only [List.foldl_cons, t.1, h.1, List.map_map, Function.comp_def,
        t.2, h.2] using (show True ∧ True from ⟨trivial, trivial⟩)

private theorem b3Liveness_livenessFold_entry (rs : List (Row V)) (e : Entry V) :
    let d := rs.foldl (fun e a => b3Liveness_livenessAddBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  induction rs generalizing e with
  | nil => simp
  | cons a rs ih =>
      have h := ih (b3Liveness_livenessAddBit a e)
      have k := b3Liveness_livenessAddBit_key a e
      simp only [List.foldl_cons]
      refine ⟨h.1.trans k.1, h.2.1.trans k.2, ?_⟩
      intro i
      rw [h.2.2, b3Liveness_livenessAddBit_bits, k.1, k.2]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem b3Liveness_livenessFinal_fields (E : Electorate V) (w : State V) :
    (finalizeWindow E w).h = w.h ∧ (finalizeWindow E w).W ⊆ w.W := by
  rw [finalizeWindow_def]
  cases greatestReady E w <;> exact ⟨rfl, fun _ h => (List.mem_filter.mp h).1⟩

omit [DecidableEq V] [RowCodec V] in
private theorem b3Liveness_livenessEvents_old (E : Electorate V) (cfg : FGConfig)
    (K : Nat) (w : State V) (d : Entry V)
    (hd : d ∈ (process_height_events E cfg K w).W) (hj : d.j < w.h) :
    d ∈ w.W := by
  have ff := b3Liveness_livenessFinal_fields E w
  rw [process_height_events_def] at hd
  dsimp only at hd
  split_ifs at hd
  · simp only [advance_height_def] at hd
    rcases List.mem_append.mp (List.mem_of_mem_drop hd) with hd | hd
    · exact ff.2 hd
    · have heq := List.mem_singleton.mp hd
      have hj' : d.j = w.h := by simp only [heq, ff.1]
      exact (Nat.ne_of_lt hj hj').elim
  · exact ff.2 hd
  · exact ff.2 hd

/-- Every row with the exact finality pair adds its bit to a retained entry.
The height pair and the R6W arm do not restrict this effect. -/
theorem window_bit_add_of_row (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
      (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (e d : Entry V) (he : e ∈ (derive E cfg K P).W)
    (hd : d ∈ (derive E cfg K (.node P s r_s x rs)).W)
    (hj : d.j = e.j) (hX : d.X = e.X)
    (a : Row V) (ha : a ∈ rs)
    (hpair : a.finality_pair = some ⟨e.j, e.X.root⟩) : a.signer ∈ d.Q := by
  have ff := b3Liveness_livenessFold_fields rs { derive E cfg K P with s := s }
  have below : d.j < (derive E cfg K P).h := by
    rw [hj]
    exact (window_bounds E cfg K hne hK P e he).2.1.trans_lt
      ((windowHeightLaws E cfg K hK).justified_below_height P)
  have hm := b3Liveness_livenessEvents_old E cfg K (certificateFolded E cfg K (.node P s r_s x rs))
    d hd (by
      change d.j < (rs.foldl process_row { derive E cfg K P with s := s }).h
      rw [ff.2]
      exact below)
  change d ∈ (rs.foldl process_row { derive E cfg K P with s := s }).W at hm
  rw [ff.1, List.mem_map] at hm
  obtain ⟨c, _, hc⟩ := hm
  have fe := b3Liveness_livenessFold_entry rs c
  have cj : c.j = e.j := fe.1.symm.trans ((congrArg Entry.j hc).trans hj)
  have cX : c.X = e.X := fe.2.1.symm.trans ((congrArg Entry.X hc).trans hX)
  rw [← hc]
  exact (fe.2.2 a.signer).mpr (Or.inr ⟨a, ha, rfl, by simpa only [cj, cX] using hpair⟩)

/-- Retention at both ends preserves old bits and all exact-pair row bits
carried strictly after A. This statement is independent of the latest J. -/
theorem window_bits_accumulate (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
      ∅) (hK : 2 ≤ K)
    (A C : FGBlock V) (hAC : FGBlock.Preceq A C)
    (e d : Entry V) (he : e ∈ (derive E cfg K A).W)
    (hd : d ∈ (derive E cfg K C).W) (hj : d.j = e.j) (hX : d.X = e.X) :
    e.Q ⊆ d.Q ∧ ∀ B, StrictPrefix A B → FGBlock.Preceq B C →
      ∀ a ∈ B.rows, a.finality_pair = some ⟨e.j, e.X.root⟩ → a.signer ∈ d.Q := by
  refine ⟨window_bit_retained E cfg K hne hK A C hAC e d he hd hj.symm hX.symm, ?_⟩
  intro B hAB hBC a ha hpair
  cases B with
  | genesis => simp [FGBlock.rows] at ha
  | node P s r_s x rs =>
      have hAP := preceq_parent_of_preceq_node hAB.1 hAB.2
      obtain ⟨b, hb, hbj, hbX, _, _⟩ := window_retained_bits_mono E cfg K hne hK
        A P C hAP (preceq_trans (preceq_parent_node P s r_s x rs) hBC) e d he hd hj hX
      obtain ⟨c, hc, hcj, hcX, _, hcQ⟩ := window_retained_bits_mono E cfg K hne hK
        A (.node P s r_s x rs) C hAB.1 hBC e d he hd hj hX
      apply hcQ
      exact window_bit_add_of_row E cfg K hne hK P s r_s x rs b c hb hc
        (hcj.trans hbj.symm) (hcX.trans hbX.symm) a ha
        (by simpa only [hbj, hbX] using hpair)

/-- A quorum of old bits and later row bits finalizes a prefix that covers
the retained pair. A greater ready height can win the same finality test. -/
theorem window_finalize_of_accumulated_quorum (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne :
      ¬ E.IsQuorum ∅) (hK : 2 ≤ K)
    (A P : FGBlock V) (hAP : FGBlock.Preceq A P)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (e d : Entry V) (he : e ∈ (derive E cfg K A).W)
    (hd : d ∈ (derive E cfg K P).W) (hj : d.j = e.j) (hX : d.X = e.X)
    (Q : Finset V) (hQ : E.IsQuorum Q)
    (hcover : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ B, StrictPrefix A B ∧
      FGBlock.Preceq B (.node P s r_s x rs) ∧ ∃ a ∈ B.rows,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) :
    FGBlock.Preceq e.X (derive E cfg K (.node P s r_s x rs)).F ∧
      e.j ≤ (derive E cfg K (.node P s r_s x rs)).h_F := by
  have acc := window_bits_accumulate E cfg K hne hK A P hAP e d he hd hj hX
  have cover : ∀ i ∈ Q, i ∈ d.Q ∨ ∃ a ∈ rs,
      a.signer = i ∧ a.finality_pair = some ⟨d.j, d.X.root⟩ := by
    intro i hi
    rcases hcover i hi with old | ⟨B, hAB, hBC, a, ha, hai, hp⟩
    · exact Or.inl (acc.1 old)
    · by_cases hB : B = .node P s r_s x rs
      · subst B
        exact Or.inr ⟨a, ha, hai, by simpa only [hj, hX] using hp⟩
      · rw [← hai]
        exact Or.inl (acc.2 B hAB (preceq_parent_of_preceq_node hBC hB) a ha hp)
  simpa only [hj, hX] using window_finality_of_cover E cfg K hne hK P s r_s x rs d hd Q hQ cover

/-- The exact target branch appends the current height and target after
finality pruning. The appended entry is last and has the greatest height. -/
theorem window_target_appended_newest (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (ht : targetQuorum E
      (finalizeWindow E (certificateFolded E cfg K (.node P s r_s x rs))) = true) :
    let B := FGBlock.node P s r_s x rs
    let f := finalizeWindow E (certificateFolded E cfg K B)
    let new : Entry V := ⟨f.h, f.T_h, ∅⟩
    (derive E cfg K B).W = (f.W ++ [new]).drop ((f.W ++ [new]).length - K) ∧
      ∃ older, (derive E cfg K B).W = older ++ [new] ∧
        (∀ d ∈ older, d.j < new.j) ∧ (derive E cfg K B).h_F < new.j := by
  dsimp only
  let B := FGBlock.node P s r_s x rs
  let f := finalizeWindow E (certificateFolded E cfg K B)
  let new : Entry V := ⟨f.h, f.T_h, ∅⟩
  have hw : (derive E cfg K B).W = (f.W ++ [new]).drop ((f.W ++ [new]).length - K) := by
    change (process_height_events E cfg K (certificateFolded E cfg K B)).W = _
    rw [process_height_events_def, ite_eq_left ht]
    rfl
  refine ⟨hw, f.W.drop ((f.W ++ [new]).length - K), ?_⟩
  have hdrop : (f.W ++ [new]).length - K ≤ f.W.length := by
    simp only [List.length_append, List.length_singleton]
    omega
  have happ : (derive E cfg K B).W = f.W.drop ((f.W ++ [new]).length - K) ++ [new] := by
    rw [hw, List.drop_append_of_le_length hdrop]
  refine ⟨happ, ?_, ?_⟩
  · have ord := window_ordered E cfg K hne hK B
    rw [happ, List.pairwise_append] at ord
    exact fun d hd => (ord.2.2 d hd new (by simp)).1
  · exact (window_bounds E cfg K hne hK B new (by rw [happ]; simp)).1

/-- Above current finality, fewer than K newer entries prevents eviction. -/
theorem window_retained_of_few_newer (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
      E.IsQuorum ∅) (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (e : Entry V) (he : e ∈ (derive E cfg K P).W)
    (above : (derive E cfg K (.node P s r_s x rs)).h_F < e.j)
    (few : ((derive E cfg K (.node P s r_s x rs)).W.filter (fun d => decide (e.j < d.j))).length <
      K) :
    ∃ d ∈ (derive E cfg K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  have present : ∃ d ∈ (derive E cfg K (.node P s r_s x rs)).W, d.j = e.j ∧ d.X = e.X := by
    by_contra gone
    obtain ⟨hl, _, _, _, hn⟩ := window_evicted_has_K_newer E cfg K hne hK P s r_s x rs e he gone
      above
    have hf : (derive E cfg K (.node P s r_s x rs)).W.filter (fun d => decide (e.j < d.j)) =
        (derive E cfg K (.node P s r_s x rs)).W := by
      apply List.filter_eq_self.mpr
      intro d hd
      exact decide_eq_true (hn d hd).1
    rw [hf, hl] at few
    exact (Nat.lt_irrefl K) few
  obtain ⟨d, hd, hj, hX⟩ := present
  exact ⟨d, hd, hj, hX, window_bit_retained E cfg K hne hK P (.node P s r_s x rs)
    (preceq_parent_node P s r_s x rs) e d he hd hj.symm hX.symm⟩

/-- Apply the current-state finality and capacity bounds at each child
strictly after A. The same entry key remains, and its bits only increase. -/
theorem window_retained_along (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
      (hK : 2 ≤ K)
    (A C : FGBlock V) (hAC : FGBlock.Preceq A C)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (bounds : ∀ P s r_s x rs, FGBlock.Preceq A P → FGBlock.Preceq (.node P s r_s x rs) C →
      (derive E cfg K (.node P s r_s x rs)).h_F < e.j ∧
        ((derive E cfg K (.node P s r_s x rs)).W.filter (fun d => decide (e.j < d.j))).length < K) :
    ∃ d ∈ (derive E cfg K C).W, d.j = e.j ∧ d.X = e.X ∧ e.Q ⊆ d.Q := by
  induction C with
  | genesis =>
      obtain rfl := preceq_genesis.mp hAC
      exact ⟨e, he, rfl, rfl, Finset.Subset.refl _⟩
  | node P s r_s x rs ih =>
      by_cases hA : A = .node P s r_s x rs
      · subst A
        exact ⟨e, he, rfl, rfl, Finset.Subset.refl _⟩
      · have hAP := preceq_parent_of_preceq_node hAC hA
        obtain ⟨b, hb, hbj, hbX, hbQ⟩ := ih hAP (fun R t r_t y rows hAR hRP =>
          bounds R t r_t y rows hAR (preceq_node_of_preceq s r_s x rs hRP))
        have hbound := bounds P s r_s x rs hAP (preceq_refl _)
        obtain ⟨d, hd, hdj, hdX, hdQ⟩ := window_retained_of_few_newer E cfg K hne hK P s r_s x rs
          b hb
          (by simpa only [hbj] using hbound.1) (by simpa only [hbj] using hbound.2)
        exact ⟨d, hd, hdj.trans hbj, hdX.trans hbX, hbQ.trans hdQ⟩

end AvailableChain.KitFG.Window
end
