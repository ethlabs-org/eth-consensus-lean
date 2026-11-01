module
public import AvailableChainKitFG.WindowSteps

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- [bp §3.1] Structural invariant before or after the row fold.
Height geometry is supplied separately by `windowHeightLaws`. -/
private structure Inv (K : Nat) (w : State V) : Prop where
  ordered : w.W.Pairwise (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X)
  bounds : ∀ e ∈ w.W, w.h_F < e.j ∧ e.j ≤ w.h_j ∧
    FGBlock.Preceq w.F e.X ∧ FGBlock.Preceq e.X w.J
  capacity : w.W.length ≤ K
  finality : FGBlock.Preceq w.F w.J
  heights : w.h_F ≤ w.h_j
  zero : w.h_F = 0 → w.F = .genesis

private theorem inv_fold (K : Nat) (w : State V) (rs : List (Row V))
    (hw : Inv K w) : Inv K (rs.foldl process_row w) := by
  have f := window_fold_fields rs w
  constructor
  · rw [f.1, List.pairwise_map]
    exact hw.ordered.imp (fun {a b} h => by
      simpa only [(window_fold_entry rs a).1, (window_fold_entry rs a).2.1,
        (window_fold_entry rs b).1, (window_fold_entry rs b).2.1] using h)
  · intro d hd
    rw [f.1, List.mem_map] at hd
    obtain ⟨e, he, rfl⟩ := hd
    simpa only [f.2.2.2.2.2.1, f.2.2.2.1, f.2.2.2.2.2.2,
      f.2.2.2.2.1, (window_fold_entry rs e).1, (window_fold_entry rs e).2.1] using hw.bounds e he
  · simpa only [f.1, List.length_map] using hw.capacity
  · simpa only [f.2.2.2.2.2.2, f.2.2.2.2.1] using hw.finality
  · simpa only [f.2.2.2.2.2.1, f.2.2.2.1] using hw.heights
  · simpa only [f.2.2.2.2.2.1, f.2.2.2.2.2.2] using hw.zero

variable [Fintype V]

omit [RowCodec V] [Fintype V] in
private theorem ordered_compare {xs : List (Entry V)}
    (h : xs.Pairwise (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X))
    {e d : Entry V} (he : e ∈ xs) (hd : d ∈ xs) :
    e = d ∨ (e.j < d.j ∧ FGBlock.Preceq e.X d.X) ∨
      (d.j < e.j ∧ FGBlock.Preceq d.X e.X) := by
  induction xs with
  | nil => simp at he
  | cons a xs ih =>
      obtain ⟨ha, ht⟩ := List.pairwise_cons.mp h
      rcases List.mem_cons.mp he with hea | he
      · subst e
        rcases List.mem_cons.mp hd with hda | hd
        · subst d
          exact Or.inl rfl
        · exact Or.inr (Or.inl (ha d hd))
      · rcases List.mem_cons.mp hd with hda | hd
        · subst d
          exact Or.inr (Or.inr (ha e he))
        · exact ih ht he hd

omit [RowCodec V] [Fintype V] in
private theorem ordered_le {xs : List (Entry V)}
    (h : xs.Pairwise (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X))
    {e d : Entry V} (he : e ∈ xs) (hd : d ∈ xs) (hj : e.j ≤ d.j) :
    FGBlock.Preceq e.X d.X := by
  rcases ordered_compare h he hd with rfl | h | h
  · exact preceq_refl _
  · exact h.2
  · exact False.elim (Nat.not_lt_of_ge hj h.1)

omit [DecidableEq V] [RowCodec V] in
private theorem windowInv_final_fields (E : Electorate V) (w : State V) :
    (finalizeWindow E w).h = w.h ∧ (finalizeWindow E w).T_h = w.T_h ∧
    (finalizeWindow E w).h_j = w.h_j ∧ (finalizeWindow E w).J = w.J ∧
    (finalizeWindow E w).W ⊆ w.W := by
  rw [finalizeWindow_def]
  cases greatestReady E w <;> simp

omit [RowCodec V] in
private theorem inv_final (E : Electorate V) (K : Nat) (w : State V) (hw : Inv K w) :
    Inv K (finalizeWindow E w) ∧
    (∀ e ∈ (finalizeWindow E w).W, ¬ E.IsQuorum e.Q) ∧
    w.h_F ≤ (finalizeWindow E w).h_F ∧ FGBlock.Preceq w.F (finalizeWindow E w).F := by
  have g := window_greatest_spec E w
  rw [finalizeWindow_def]
  cases hg : greatestReady E w with
  | none =>
      simp only
      refine ⟨?_, ?_, le_rfl, preceq_refl _⟩
      · exact ⟨hw.ordered.filter _, fun e he => hw.bounds e (List.mem_filter.mp he).1,
          (List.length_filter_le _ _).trans hw.capacity, hw.finality, hw.heights, hw.zero⟩
      · intro e he hq
        have hb := hw.bounds e (List.mem_filter.mp he).1
        obtain ⟨d, hd, _⟩ := g.2 e (List.mem_filter.mp he).1 hb.1 hq
        simp [hg] at hd
  | some d =>
      have gd := g.1 d hg
      have bd := hw.bounds d gd.1
      simp only
      refine ⟨?_, ?_, Nat.le_of_lt bd.1, bd.2.2.1⟩
      · refine ⟨hw.ordered.filter _, ?_,
          (List.length_filter_le _ _).trans hw.capacity, bd.2.2.2, bd.2.1, ?_⟩
        · intro e he
          obtain ⟨he, hj⟩ := List.mem_filter.mp he
          have hj' : d.j < e.j := of_decide_eq_true hj
          have be := hw.bounds e he
          exact ⟨hj', be.2.1, ordered_le hw.ordered gd.1 he (Nat.le_of_lt hj'), be.2.2.2⟩
        · intro hz
          have : d.j = 0 := hz
          exact False.elim (Nat.not_lt_zero _ (this ▸ bd.1))
      · intro e he hq
        obtain ⟨he, hj⟩ := List.mem_filter.mp he
        have hj' : d.j < e.j := of_decide_eq_true hj
        obtain ⟨a, ha, hle⟩ := g.2 e he (hw.bounds e he).1 hq
        have : a = d := Option.some.inj (ha.symm.trans hg)
        subst a
        exact False.elim (Nat.not_lt_of_ge hle hj')

omit [RowCodec V] in
private theorem final_cover (E : Electorate V) (K : Nat) (w : State V)
    (hw : Inv K w) (e : Entry V) (he : e ∈ w.W) (hq : E.IsQuorum e.Q) :
    FGBlock.Preceq e.X (finalizeWindow E w).F ∧ e.j ≤ (finalizeWindow E w).h_F := by
  obtain ⟨d, hd, hle⟩ := (window_greatest_spec E w).2 e he (hw.bounds e he).1 hq
  have hm := ((window_greatest_spec E w).1 d hd).1
  rw [finalizeWindow_def, hd]
  exact ⟨ordered_le hw.ordered he hm hle, hle⟩

omit [RowCodec V] [Fintype V] in
private theorem inv_advance (K : Nat) (w : State V) (hw : Inv K w) :
    Inv K (advance_height w) := by
  rw [advance_height_def]
  exact ⟨hw.ordered, hw.bounds, hw.capacity, hw.finality, hw.heights, hw.zero⟩

omit [RowCodec V] [Fintype V] in
private theorem inv_append (K : Nat) (w : State V) (hw : Inv K w)
    (hj : w.h_j < w.h) (hJT : FGBlock.Preceq w.J w.T_h) :
    Inv K { w with
      J := w.T_h, h_j := w.h
      W := (w.W ++ [Entry.mk w.h w.T_h ∅]).drop ((w.W ++ [Entry.mk w.h w.T_h ∅]).length - K) } := by
  have hp : (w.W ++ [Entry.mk w.h w.T_h ∅]).Pairwise
      (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X) := by
    rw [List.pairwise_append]
    refine ⟨hw.ordered, by simp, ?_⟩
    intro e he d hd
    have hd' : d = Entry.mk w.h w.T_h ∅ := List.mem_singleton.mp hd
    subst d
    have hb := hw.bounds e he
    exact ⟨Nat.lt_of_le_of_lt hb.2.1 hj, preceq_trans hb.2.2.2 hJT⟩
  refine ⟨hp.drop, ?_, ?_, preceq_trans hw.finality hJT,
    hw.heights.trans (Nat.le_of_lt hj), hw.zero⟩
  · intro e he
    have hm := List.mem_of_mem_drop he
    rcases List.mem_append.mp hm with hm | hm
    · have hb := hw.bounds e hm
      exact ⟨hb.1, hb.2.1.trans (Nat.le_of_lt hj), hb.2.2.1,
        preceq_trans hb.2.2.2 hJT⟩
    · have : e = Entry.mk w.h w.T_h ∅ := List.mem_singleton.mp hm
      subst e
      exact ⟨Nat.lt_of_le_of_lt hw.heights hj, le_rfl,
        preceq_trans hw.finality hJT, preceq_refl _⟩
  · simp only [List.length_drop]
    omega

omit [DecidableEq V] [RowCodec V] in
private theorem windowInv_events_finality (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (w : State V) :
    (process_height_events E cfg K w).F = (finalizeWindow E w).F ∧
    (process_height_events E cfg K w).h_F = (finalizeWindow E w).h_F := by
  rw [process_height_events_def]
  dsimp only
  split_ifs <;> simp only [advance_height_def, and_self]

omit [RowCodec V] in
private theorem inv_events (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : State V)
    (hw : Inv K w) (hj : w.h_j < w.h) (hJT : FGBlock.Preceq w.J w.T_h)
    (hzero : ¬ E.IsQuorum ∅) :
    Inv K (process_height_events E cfg K w) ∧
      ∀ e ∈ (process_height_events E cfg K w).W, ¬ E.IsQuorum e.Q := by
  have hf := inv_final E K w hw
  have ff := windowInv_final_fields E w
  have hi := inv_append K _ hf.1 (by simpa only [ff.1, ff.2.2.1] using hj)
    (by simpa only [ff.2.1, ff.2.2.2.1] using hJT)
  rw [process_height_events_def]
  dsimp only
  split_ifs
  · refine ⟨inv_advance K _ hi, ?_⟩
    intro e he
    simp only [advance_height_def] at he
    rcases List.mem_append.mp (List.mem_of_mem_drop he) with he | he
    · exact hf.2.1 e he
    · have : e = ⟨(finalizeWindow E w).h, (finalizeWindow E w).T_h, ∅⟩ :=
        List.mem_singleton.mp he
      subst e
      exact hzero
  · exact ⟨inv_advance K _ hf.1, by simpa only [advance_height_def] using hf.2.1⟩
  · exact ⟨hf.1, hf.2.1⟩

/-- [bp §3.1] One induction on the original block tree. -/
private theorem derived_inv (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
    ∅) (hK : 2 ≤ K)
    (B : FGBlock V) :
    Inv K (derive E cfg K B) ∧ ∀ e ∈ (derive E cfg K B).W, ¬ E.IsQuorum e.Q := by
  induction B with
  | genesis =>
      rw [derive_def, initial_def]
      refine ⟨⟨by simp, by simp, by simp, preceq_refl _, le_rfl, fun _ => rfl⟩, by simp⟩
  | node P s r_s x rs ih =>
      have hw : Inv K { derive E cfg K P with s := (FGBlock.node P s r_s x rs).slot } :=
        ⟨ih.1.ordered, ih.1.bounds, ih.1.capacity, ih.1.finality, ih.1.heights, ih.1.zero⟩
      have hi := inv_fold K _ rs hw
      have ff := window_fold_fields rs { derive E cfg K P with s := (FGBlock.node P s r_s x
          rs).slot }
      have hg := windowHeightLaws E cfg K hK
      have hj : (derive E cfg K P).h_j < (derive E cfg K P).h := hg.justified_below_height P
      have hJT : FGBlock.Preceq (derive E cfg K P).J (derive E cfg K P).T_h :=
        hg.justified_preceq_entry P
      simp only [derive_def E cfg K (.node P s r_s x rs), transition_def]
      apply inv_events
      · exact ⟨hi.ordered, hi.bounds, hi.capacity, hi.finality, hi.heights, hi.zero⟩
      · simpa only [ff.2.1, ff.2.2.2.1] using hj
      · simpa only [ff.2.2.1, ff.2.2.2.2.1] using hJT
      · exact hne

/-- [bp §3.1; W5] Entry heights strictly increase in chain order. -/
theorem window_ordered (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅) (hK
    : 2 ≤ K) (B : FGBlock V) :
    ((derive E cfg K B).W).Pairwise (fun e d => e.j < d.j ∧ FGBlock.Preceq e.X d.X) :=
  (derived_inv E cfg K hne hK B).1.ordered

/-- [bp §3.1] Every retained entry lies between finality and the latest justification. -/
theorem window_bounds (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅) (hK
    : 2 ≤ K)
    (B : FGBlock V) (e : Entry V) (he : e ∈ (derive E cfg K B).W) :
    (derive E cfg K B).h_F < e.j ∧ e.j ≤ (derive E cfg K B).h_j ∧
    FGBlock.Preceq (derive E cfg K B).F e.X ∧ FGBlock.Preceq e.X (derive E cfg K B).J :=
  (derived_inv E cfg K hne hK B).1.bounds e he

/-- [bp §3.1] The window keeps at most K entries. -/
theorem window_capacity (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
    (hK : 2 ≤ K) (B : FGBlock V) :
    (derive E cfg K B).W.length ≤ K := (derived_inv E cfg K hne hK B).1.capacity

/-- [bp §3.1] Finality removes every ready entry; new entries have no bits. -/
theorem window_post_not_ready (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
    ∅) (hK : 2 ≤ K)
    (B : FGBlock V) (e : Entry V) (he : e ∈ (derive E cfg K B).W) :
    ¬ E.IsQuorum e.Q := (derived_inv E cfg K hne hK B).2 e he

/-- [bp §3.1] Finality precedes the latest justification. -/
theorem window_F_preceq_J (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
    (hK : 2 ≤ K) (B : FGBlock V) :
    FGBlock.Preceq (derive E cfg K B).F (derive E cfg K B).J := (derived_inv E cfg K hne hK
        B).1.finality

/-- [bp §3.1] Finalized height does not exceed justified height. -/
theorem window_hF_le_hj (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
    (hK : 2 ≤ K) (B : FGBlock V) :
    (derive E cfg K B).h_F ≤ (derive E cfg K B).h_j := (derived_inv E cfg K hne hK B).1.heights

/-- [bp §3.1] Finality at height zero is genesis. -/
theorem window_finalized_zero (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
    ∅) (hK : 2 ≤ K)
    (B : FGBlock V) (hz : (derive E cfg K B).h_F = 0) :
    (derive E cfg K B).F = .genesis := (derived_inv E cfg K hne hK B).1.zero hz

private theorem node_mono (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
    (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) :
    (derive E cfg K P).h_F ≤ (derive E cfg K (.node P s r_s x rs)).h_F ∧
    FGBlock.Preceq (derive E cfg K P).F (derive E cfg K (.node P s r_s x rs)).F := by
  have hw := (derived_inv E cfg K hne hK P).1
  have hs : Inv K { derive E cfg K P with s := (FGBlock.node P s r_s x rs).slot } :=
    ⟨hw.ordered, hw.bounds, hw.capacity, hw.finality, hw.heights, hw.zero⟩
  have hi := inv_fold K _ rs hs
  have ff := window_fold_fields rs { derive E cfg K P with s := (FGBlock.node P s r_s x rs).slot }
  have hm := (inv_final E K
    { rs.foldl process_row { derive E cfg K P with s := (FGBlock.node P s r_s x rs).slot }
      with L := .node P s r_s x rs }
    ⟨hi.ordered, hi.bounds, hi.capacity, hi.finality, hi.heights, hi.zero⟩).2.2
  simp only [derive_def E cfg K (.node P s r_s x rs), transition_def]
  rw [(windowInv_events_finality E cfg K _).1, (windowInv_events_finality E cfg K _).2]
  simpa only [ff.2.2.2.2.2.1, ff.2.2.2.2.2.2] using hm

private theorem ancestor_mono (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
    ∅) (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B) :
    (derive E cfg K A).h_F ≤ (derive E cfg K B).h_F ∧
    FGBlock.Preceq (derive E cfg K A).F (derive E cfg K B).F := by
  induction B with
  | genesis =>
      have : A = .genesis := preceq_genesis.mp hAB
      subst A
      exact ⟨le_rfl, preceq_refl _⟩
  | node P s r_s x rs ih =>
      by_cases heq : A = .node P s r_s x rs
      · subst A
        exact ⟨le_rfl, preceq_refl _⟩
      · have ha := ih (preceq_parent_of_preceq_node hAB heq)
        have hb := node_mono E cfg K hne hK P s r_s x rs
        exact ⟨ha.1.trans hb.1, preceq_trans ha.2 hb.2⟩

/-- [bp §3.1] Finalized height is monotone along ancestry. -/
theorem window_hF_mono (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅) (hK
    : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B) :
    (derive E cfg K A).h_F ≤ (derive E cfg K B).h_F := (ancestor_mono E cfg K hne hK A B hAB).1

/-- [bp §3.1] Finalized blocks are monotone along ancestry. -/
theorem window_F_mono (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅) (hK
    : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B) :
    FGBlock.Preceq (derive E cfg K A).F (derive E cfg K B).F := (ancestor_mono E cfg K hne hK A
        B hAB).2

omit [DecidableEq V] [RowCodec V] in
private theorem events_old (E : Electorate V) (cfg : FGConfig) (K : Nat) (w : State V)
    (d : Entry V) (hd : d ∈ (process_height_events E cfg K w).W) (hj : d.j < w.h) :
    d ∈ w.W := by
  have ff := windowInv_final_fields E w
  rw [process_height_events_def] at hd
  dsimp only at hd
  split_ifs at hd
  · simp only [advance_height_def] at hd
    rcases List.mem_append.mp (List.mem_of_mem_drop hd) with hd | hd
    · exact ff.2.2.2.2 hd
    · have heq := List.mem_singleton.mp hd
      have hj' : d.j = w.h := by simp only [heq, ff.1]
      exact False.elim (Nat.ne_of_lt hj hj')
  · simp only [advance_height_def] at hd
    exact ff.2.2.2.2 hd
  · exact ff.2.2.2.2 hd

private theorem node_old (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (d : Entry V) (hd : d ∈ (derive E cfg K (.node P s r_s x rs)).W)
    (hj : d.j < (derive E cfg K P).h) :
    ∃ e ∈ (derive E cfg K P).W, e.j = d.j ∧ e.X = d.X ∧ e.Q ⊆ d.Q := by
  have ff := window_fold_fields rs { derive E cfg K P with s := (FGBlock.node P s r_s x rs).slot }
  simp only [derive_def E cfg K (.node P s r_s x rs), transition_def] at hd
  have hm := events_old E cfg K _ d hd (by simpa only [ff.2.1] using hj)
  change d ∈ (rs.foldl process_row _).W at hm
  rw [ff.1, List.mem_map] at hm
  obtain ⟨e, he, rfl⟩ := hm
  have fe := window_fold_entry rs e
  exact ⟨e, he, fe.1.symm, fe.2.1.symm, fun i hi => (fe.2.2 i).mpr (Or.inl hi)⟩

/-- An entry below an ancestor's height must have survived from that ancestor. -/
private theorem ancestor_old (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (d : Entry V) (hd : d ∈ (derive E cfg K B).W) (hj : d.j < (derive E cfg K A).h) :
    ∃ e ∈ (derive E cfg K A).W, e.j = d.j ∧ e.X = d.X ∧ e.Q ⊆ d.Q := by
  induction B generalizing d with
  | genesis =>
      have : A = .genesis := preceq_genesis.mp hAB
      subst A
      exact ⟨d, hd, rfl, rfl, Finset.Subset.refl _⟩
  | node P s r_s x rs ih =>
      by_cases heq : A = .node P s r_s x rs
      · subst A
        exact ⟨d, hd, rfl, rfl, Finset.Subset.refl _⟩
      · have ha := preceq_parent_of_preceq_node hAB heq
        have hh : (derive E cfg K A).h ≤ (derive E cfg K P).h :=
          (windowHeightLaws E cfg K hK).h_mono ha
        obtain ⟨c, hc, hcj, hcX, hcQ⟩ := node_old E cfg K P s r_s x rs d hd (hj.trans_le hh)
        obtain ⟨e, he, hej, heX, heQ⟩ := ih ha c hc (hcj ▸ hj)
        exact ⟨e, he, hej.trans hcj, heX.trans hcX, heQ.trans hcQ⟩

/-- [bp §3.1] Bits only grow while the exact entry is retained. -/
theorem window_bit_retained (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum
    ∅) (hK : 2 ≤ K)
    (A B : FGBlock V) (hAB : FGBlock.Preceq A B)
    (e d : Entry V) (he : e ∈ (derive E cfg K A).W) (hd : d ∈ (derive E cfg K B).W)
    (hj : e.j = d.j) (hX : e.X = d.X) : e.Q ⊆ d.Q := by
  have hb := window_bounds E cfg K hne hK A e he
  have hh : (derive E cfg K A).h_j < (derive E cfg K A).h :=
    (windowHeightLaws E cfg K hK).justified_below_height A
  obtain ⟨c, hc, hcj, _, hcQ⟩ := ancestor_old E cfg K hK A B hAB d hd
    (hj ▸ Nat.lt_of_le_of_lt hb.2.1 hh)
  have hkey : e.j = c.j := hj.trans hcj.symm
  have _sameBlock := hX
  rcases ordered_compare (window_ordered E cfg K hne hK A) he hc with heq | hlt | hlt
  · simpa only [heq] using hcQ
  · exact False.elim (Nat.ne_of_lt hlt.1 hkey)
  · exact False.elim (Nat.ne_of_lt hlt.1 hkey.symm)

/-- [bp §3.1] Removal is permanent: all later births have greater height. -/
theorem window_no_reentry (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬ E.IsQuorum ∅)
    (hK : 2 ≤ K)
    (A B C : FGBlock V) (hAB : FGBlock.Preceq A B) (hBC : FGBlock.Preceq B C)
    (e : Entry V) (he : e ∈ (derive E cfg K A).W)
    (gone : ¬ ∃ d ∈ (derive E cfg K B).W, d.j = e.j ∧ d.X = e.X) :
    ¬ ∃ d ∈ (derive E cfg K C).W, d.j = e.j ∧ d.X = e.X := by
  rintro ⟨d, hd, hdj, hdX⟩
  have hb := window_bounds E cfg K hne hK A e he
  have hh : (derive E cfg K A).h_j < (derive E cfg K A).h :=
    (windowHeightLaws E cfg K hK).justified_below_height A
  have hm : (derive E cfg K A).h ≤ (derive E cfg K B).h := (windowHeightLaws E cfg K hK).h_mono hAB
  obtain ⟨c, hc, hcj, hcX, _⟩ := ancestor_old E cfg K hK B C hBC d hd
    (hdj ▸ (Nat.lt_of_le_of_lt hb.2.1 hh).trans_le hm)
  exact gone ⟨c, hc, hcj.trans hdj, hcX.trans hdX⟩

/-- [design §5; bp 22 I7] A covered quorum finalizes this entry or a later entry. -/
theorem window_finality_of_cover (E : Electorate V) (cfg : FGConfig) (K : Nat) (hne : ¬
    E.IsQuorum ∅) (hK : 2 ≤ K)
    (P : FGBlock V) (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V))
    (e : Entry V) (he : e ∈ (derive E cfg K P).W)
    (Q : Finset V) (hQ : E.IsQuorum Q)
    (hcover : ∀ i ∈ Q, i ∈ e.Q ∨ ∃ a ∈ rs,
      a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) :
    FGBlock.Preceq e.X (derive E cfg K (.node P s r_s x rs)).F ∧
      e.j ≤ (derive E cfg K (.node P s r_s x rs)).h_F := by
  let w := { derive E cfg K P with s := (FGBlock.node P s r_s x rs).slot }
  let u := { rs.foldl process_row w with L := FGBlock.node P s r_s x rs }
  let d := rs.foldl (fun e a => window_addBit a e) e
  have hw := (derived_inv E cfg K hne hK P).1
  have hw' : Inv K w :=
    ⟨hw.ordered, hw.bounds, hw.capacity, hw.finality, hw.heights, hw.zero⟩
  have hi := inv_fold K w rs hw'
  have hu : Inv K u :=
    ⟨hi.ordered, hi.bounds, hi.capacity, hi.finality, hi.heights, hi.zero⟩
  have hd : d ∈ u.W := by
    change d ∈ (rs.foldl process_row w).W
    rw [(window_fold_fields rs w).1]
    exact List.mem_map.mpr ⟨e, he, rfl⟩
  have hsub : Q ⊆ d.Q := fun i hi => ((window_fold_entry rs e).2.2 i).mpr (hcover i hi)
  have hc := final_cover E K u hu d hd (isQuorum_of_subset E hQ hsub)
  simp only [derive_def E cfg K (.node P s r_s x rs), transition_def]
  rw [(windowInv_events_finality E cfg K _).1, (windowInv_events_finality E cfg K _).2]
  simpa only [d, (window_fold_entry rs e).1, (window_fold_entry rs e).2.1] using hc

end AvailableChain.KitFG.Window
end
