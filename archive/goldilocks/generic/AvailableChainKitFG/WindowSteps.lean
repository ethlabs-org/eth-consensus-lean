module
public import AvailableChainKitFG.WindowEntriesDef
public import AvailableChainKitFG.WindowHeightBridge -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [RowCodec V]

theorem window_addBit_key (a : Row V) (e : Entry V) :
    (window_addBit a e).j = e.j ∧ (window_addBit a e).X = e.X := by
  rw [window_addBit_def]
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem window_addBit_bits (a : Row V) (e : Entry V) (i : V) :
    i ∈ (window_addBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  rw [window_addBit_def]
  split_ifs with h <;> simp [h, eq_comm, or_comm]

theorem window_row_fields (w : State V) (a : Row V) :
    (process_row w a).W = w.W.map (window_addBit a) ∧
    (process_row w a).h = w.h ∧ (process_row w a).T_h = w.T_h ∧
    (process_row w a).h_j = w.h_j ∧ (process_row w a).J = w.J ∧
    (process_row w a).h_F = w.h_F ∧ (process_row w a).F = w.F := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [process_row_def, NamedHeightPair.matchesEntry]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def] <;> split_ifs <;>
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem window_fold_fields (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W = w.W.map (fun e => rs.foldl (fun e a => window_addBit a e) e) ∧
    (rs.foldl process_row w).h = w.h ∧ (rs.foldl process_row w).T_h = w.T_h ∧
    (rs.foldl process_row w).h_j = w.h_j ∧ (rs.foldl process_row w).J = w.J ∧
    (rs.foldl process_row w).h_F = w.h_F ∧ (rs.foldl process_row w).F = w.F := by
  induction rs generalizing w with
  | nil => simp
  | cons a rs ih =>
      have h := window_row_fields w a
      have t := ih (process_row w a)
      simpa only [List.foldl_cons, t.1, h.1, List.map_map, Function.comp_def,
        t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
        t.2.2.2.2.2.2, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2] using
        (show True ∧ True ∧ True ∧ True ∧ True ∧ True ∧ True from by trivial)

theorem window_fold_entry (rs : List (Row V)) (e : Entry V) :
    let d := rs.foldl (fun e a => window_addBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  induction rs generalizing e with
  | nil => simp
  | cons a rs ih =>
      have h := ih (window_addBit a e)
      have k := window_addBit_key a e
      simp only [List.foldl_cons]
      refine ⟨h.1.trans k.1, h.2.1.trans k.2, ?_⟩
      intro i
      rw [h.2.2, window_addBit_bits, k.1, k.2]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
/-- The fold selects a ready member and dominates every ready height. -/
theorem window_greatest_spec (E : Electorate V) (w : State V) :
    (∀ e, greatestReady E w = some e →
      e ∈ w.W ∧ w.h_F < e.j ∧ E.IsQuorum e.Q) ∧
    (∀ d ∈ w.W, w.h_F < d.j → E.IsQuorum d.Q →
      ∃ e, greatestReady E w = some e ∧ d.j ≤ e.j) := by
  let step := fun (best : Option (Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  have go (xs : List (Entry V)) (best : Option (Entry V)) :
      (∀ e, xs.foldl step best = some e →
        best = some e ∨ (e ∈ xs ∧ w.h_F < e.j ∧ E.IsQuorum e.Q)) ∧
      (∀ d, (best = some d ∨ (d ∈ xs ∧ w.h_F < d.j ∧ E.IsQuorum d.Q)) →
        ∃ e, xs.foldl step best = some e ∧ d.j ≤ e.j) := by
    induction xs generalizing best with
    | nil =>
        simp only [List.foldl_nil, List.not_mem_nil, false_and, or_false]
        exact ⟨fun _ h => h, fun d h => ⟨d, h, le_rfl⟩⟩
    | cons a xs ih =>
        have h := ih (step best a)
        simp only [List.foldl_cons]
        constructor
        · intro e he
          rcases h.1 e he with he | he
          · unfold step at he
            dsimp only [Electorate.IsQuorum] at *
            split_ifs at he with ha <;> cases best <;> simp_all
            all_goals aesop
          · exact Or.inr ⟨List.mem_cons_of_mem _ he.1, he.2⟩
        · intro d hd
          have next : ∃ b, (step best a = some b ∨
              (b ∈ xs ∧ w.h_F < b.j ∧ E.IsQuorum b.Q)) ∧ d.j ≤ b.j := by
            rcases hd with hd | ⟨hd, hf, hq⟩
            · subst best
              by_cases ha : w.h_F < a.j ∧ E.q ≤ E.weightOf a.Q
              · by_cases hj : d.j < a.j
                · exact ⟨a, Or.inl (by simp [step, ha, hj]), Nat.le_of_lt hj⟩
                · exact ⟨d, Or.inl (by simp [step, ha, hj]), le_rfl⟩
              · exact ⟨d, Or.inl (by simp [step, ha]), le_rfl⟩
            · rcases List.mem_cons.mp hd with hd | hd
              · subst d
                have ha : w.h_F < a.j ∧ E.q ≤ E.weightOf a.Q := ⟨hf, hq⟩
                cases best with
                | none => exact ⟨a, Or.inl (by simp [step, ha]), le_rfl⟩
                | some old =>
                    by_cases hj : old.j < a.j
                    · exact ⟨a, Or.inl (by simp [step, ha, hj]), le_rfl⟩
                    · exact ⟨old, Or.inl (by simp [step, ha, hj]), Nat.le_of_not_gt hj⟩
              · exact ⟨d, Or.inr ⟨hd, hf, hq⟩, le_rfl⟩
          obtain ⟨b, hb, hdb⟩ := next
          obtain ⟨e, he, hbe⟩ := h.2 b hb
          exact ⟨e, he, hdb.trans hbe⟩
  have heq : greatestReady E w = w.W.foldl step none := by
    rw [greatestReady_def]
    congr 1
    funext best e
    dsimp [step]
    split_ifs <;> cases best <;> rfl
  rw [heq]
  have h := go w.W none
  exact ⟨fun e he => (h.1 e he).resolve_left (by simp),
    fun d hd hf hq => h.2 d (Or.inr ⟨hd, hf, hq⟩)⟩

omit [RowCodec V] [Fintype V] in
theorem window_strict_node {C P : FGBlock V}
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) (hCP : FGBlock.Preceq C P) :
    StrictPrefix C (.node P s r_s x rs) := by
  refine ⟨preceq_node_of_preceq s r_s x rs hCP, ?_⟩
  intro he
  have hcycle := preceq_antisymm (he ▸ hCP) (preceq_parent_node P s r_s x rs)
  have hs := congrArg sizeOf hcycle
  simp only [FGBlock.node.sizeOf_spec] at hs
  omega

omit [Fintype V] in
/-- The row fold changes only bits of existing entries. Each new bit names
an exact finality pair from a row in this fold. -/
theorem window_fold_sources (rs : List (Row V))
    (w : State V) :
    (rs.foldl process_row w).h = w.h ∧
    (rs.foldl process_row w).T_h = w.T_h ∧
    ∀ e ∈ (rs.foldl process_row w).W, ∃ d ∈ w.W,
      d.j = e.j ∧ d.X = e.X ∧
      ∀ i ∈ e.Q, i ∈ d.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have row (w : State V) (a : Row V) :
      (process_row w a).h = w.h ∧ (process_row w a).T_h = w.T_h ∧
      (process_row w a).W = w.W.map (fun e =>
        if a.finality_pair = some ⟨e.j, e.X.root⟩ then
          { e with Q := insert a.signer e.Q } else e) := by
    obtain ⟨i, pair, fp⟩ := a
    cases pair with
    | empty => simp only [process_row_def, NamedHeightPair.matchesEntry]; exact ⟨rfl, rfl, rfl⟩
    | vote j X t =>
        cases t <;> simp only [process_row_def] <;> split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  induction rs generalizing w with
  | nil => exact ⟨rfl, rfl, fun e he => ⟨e, he, rfl, rfl, fun _ hi => Or.inl hi⟩⟩
  | cons a rs ih =>
      obtain ⟨hh, hT, hs⟩ := ih (process_row w a)
      obtain ⟨rh, rT, rW⟩ := row w a
      refine ⟨hh.trans rh, hT.trans rT, ?_⟩
      intro e he
      obtain ⟨d, hd, hj, hX, hbits⟩ := hs e he
      rw [rW, List.mem_map] at hd
      obtain ⟨c, hc, hcd⟩ := hd
      have keys : c.j = d.j ∧ c.X = d.X := by
        split_ifs at hcd <;> subst d <;> exact ⟨rfl, rfl⟩
      have cX : c.X = e.X := keys.2.trans hX
      have cj := keys.1.trans hj
      refine ⟨c, hc, cj, cX, ?_⟩
      intro i hi
      rcases hbits i hi with hi | ⟨b, hb, hbi, hbf⟩
      · split_ifs at hcd with hm
        · subst d
          rcases Finset.mem_insert.mp hi with hi | hi
          · exact Or.inr ⟨a, List.mem_cons_self, hi.symm, by simpa only [cj, cX] using hm⟩
          · exact Or.inl hi
        · subst d; exact Or.inl hi
      · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, hbi, hbf⟩

end AvailableChain.KitFG.Window
end
