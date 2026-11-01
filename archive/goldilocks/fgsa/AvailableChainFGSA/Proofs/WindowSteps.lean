module
public import AvailableChainFGSA.Statements.WindowCertificate -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.WindowHeightBridge -- shake: keep (re-export)
public import AvailableChainKitFG.WindowSteps

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.KitFG

section

private abbrev ws_Old := FGSA.Window.State
private abbrev ws_New := SimplexFG.Window.State

private def ws_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def ws_toWindow {V : Type} (w : ws_Old V) : ws_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map ws_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem ws_entry_eq {V : Type} (e : Entry V) :
    ws_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem ws_state_eq {V : Type} (w : ws_Old V) :
    ws_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map ws_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem ws_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (ws_toEntry e).j = e.j ∧ (ws_toEntry e).X = e.X ∧ (ws_toEntry e).Q = e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem ws_state_fields {V : Type} (w : ws_Old V) :
    (ws_toWindow w).L = w.L ∧ (ws_toWindow w).s = w.s ∧
    (ws_toWindow w).h = w.h ∧ (ws_toWindow w).T_h = w.T_h ∧
    (ws_toWindow w).target_participation = w.target_participation ∧
    (ws_toWindow w).progress = w.progress ∧ (ws_toWindow w).W = w.W.map ws_toEntry ∧
    (ws_toWindow w).J = w.J ∧ (ws_toWindow w).h_j = w.h_j ∧
    (ws_toWindow w).F = w.F ∧ (ws_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ws_initial_eq {V : Type} :
    ws_toWindow (FGSA.Window.initial (V := V)) = SimplexFG.Window.initial := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem ws_row_eq (w : ws_Old V) (a : Row V) :
    ws_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (ws_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map ws_toEntry =
      (w.W.map ws_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [ws_entry_eq, he]
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
        NamedHeightPair.matchesEntry, Bool.false_eq_true, ↓reduceIte, ws_state_eq] using
        congrArg (fun es => ({ ws_toWindow w with W := es } : ws_New V)) bits
  | vote h X t =>
      cases t <;>
        simp only [FGSA.Window.process_row_def, SimplexFG.Window.process_row_def,
          NamedHeightPair.matchesEntry] <;>
        split_ifs <;> dsimp [ws_state_eq] <;> rw [bits] <;> simp_all [ws_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem ws_rows_eq (rs : List (Row V)) (w : ws_Old V) :
    ws_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (ws_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, ws_row_eq]

omit [DecidableEq V] [RowCodec V] in
private theorem ws_advance_eq (w : ws_Old V) :
    ws_toWindow (FGSA.Window.advance_height w) =
      SimplexFG.Window.advance_height (ws_toWindow w) := rfl

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
private theorem ws_greatest_eq (E : Electorate V) (w : ws_Old V) :
    (FGSA.Window.greatestReady E w).map ws_toEntry =
      SimplexFG.Window.greatestReady E (ws_toWindow w) := by
  classical
  let oldStep := fun (best : Option (FGSA.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  let newStep := fun (best : Option (SimplexFG.Window.Entry V)) e =>
    if w.h_F < e.j ∧ E.q ≤ E.weightOf e.Q then
      best.elim (some e) (fun old => if old.j < e.j then some e else best)
    else best
  have step (best) (e) :
      (oldStep best e).map ws_toEntry = newStep (best.map ws_toEntry) (ws_toEntry e) := by
    dsimp [oldStep, newStep, ws_entry_eq]
    split_ifs <;> cases best <;> simp_all [ws_entry_eq]
    split_ifs <;> rfl
  have fold (es : List (FGSA.Window.Entry V)) (best) :
      (es.foldl oldStep best).map ws_toEntry =
        (es.map ws_toEntry).foldl newStep (best.map ws_toEntry) := by
    induction es generalizing best with
    | nil => rfl
    | cons e es ih => simp only [List.foldl_cons, List.map_cons, ih, step]
  have old_eq : FGSA.Window.greatestReady E w = w.W.foldl oldStep none := by
    rw [FGSA.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  have new_eq : SimplexFG.Window.greatestReady E (ws_toWindow w) =
      (w.W.map ws_toEntry).foldl newStep none := by
    rw [SimplexFG.Window.greatestReady_def]
    congr 1
    funext best e
    cases best <;> rfl
  rw [old_eq, new_eq]
  exact fold w.W none

end

private theorem ws_toEntry_injective {V : Type} :
    Function.Injective (ws_toEntry (V := V)) := by
  intro a b h
  cases a
  cases b
  simpa only [ws_entry_eq, SimplexFG.Window.Entry.mk.injEq, Entry.mk.injEq] using h

private theorem ws_mem_toEntry {V : Type} (e : Entry V) (es : List (Entry V)) :
    ws_toEntry e ∈ es.map ws_toEntry ↔ e ∈ es :=
  List.mem_map_of_injective ws_toEntry_injective

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- [bp §3.1] One row changes only the bits of its exact entry. -/
def window_addBit (a : Row V) (e : Entry V) : Entry V :=
  if a.finality_pair = some ⟨e.j, e.X.root⟩ then { e with Q := insert a.signer e.Q } else e

private theorem ws_addBit_def (a : Row V) (e : Entry V) :
    window_addBit a e =
      if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e := rfl

private theorem ws_addBit_eq (a : Row V) (e : Entry V) :
    ws_toEntry (window_addBit a e) = KitFG.Window.window_addBit a (ws_toEntry e) := by
  by_cases h : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
    simp [ws_addBit_def, KitFG.Window.window_addBit_def, ws_entry_eq, h]

private theorem ws_bits_fold_eq (rs : List (Row V)) (e : Entry V) :
    ws_toEntry (rs.foldl (fun e a => window_addBit a e) e) =
      rs.foldl (fun e a => KitFG.Window.window_addBit a e) (ws_toEntry e) := by
  induction rs generalizing e with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, ws_addBit_eq]

theorem window_addBit_key (a : Row V) (e : Entry V) :
    (window_addBit a e).j = e.j ∧ (window_addBit a e).X = e.X := by
  have h := KitFG.Window.window_addBit_key a (ws_toEntry e)
  rw [← ws_addBit_eq] at h
  exact h

theorem window_addBit_bits (a : Row V) (e : Entry V) (i : V) :
    i ∈ (window_addBit a e).Q ↔ i ∈ e.Q ∨
      (a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩) := by
  have h := KitFG.Window.window_addBit_bits a (ws_toEntry e) i
  rw [← ws_addBit_eq] at h
  exact h

theorem window_row_fields (w : State V) (a : Row V) :
    (process_row w a).W = w.W.map (window_addBit a) ∧
    (process_row w a).h = w.h ∧ (process_row w a).T_h = w.T_h ∧
    (process_row w a).h_j = w.h_j ∧ (process_row w a).J = w.J ∧
    (process_row w a).h_F = w.h_F ∧ (process_row w a).F = w.F := by
  have h := KitFG.Window.window_row_fields (ws_toWindow w) a
  simp only [← ws_row_eq] at h
  simp only [ws_state_eq, List.map_map, Function.comp_def, ← ws_addBit_eq] at h
  exact ⟨(List.map_injective_iff.mpr ws_toEntry_injective) (by
    simpa only [List.map_map, Function.comp_def] using h.1), h.2⟩

theorem window_fold_fields (rs : List (Row V)) (w : State V) :
    (rs.foldl process_row w).W = w.W.map (fun e => rs.foldl (fun e a => window_addBit a e) e) ∧
    (rs.foldl process_row w).h = w.h ∧ (rs.foldl process_row w).T_h = w.T_h ∧
    (rs.foldl process_row w).h_j = w.h_j ∧ (rs.foldl process_row w).J = w.J ∧
    (rs.foldl process_row w).h_F = w.h_F ∧ (rs.foldl process_row w).F = w.F := by
  have h := KitFG.Window.window_fold_fields rs (ws_toWindow w)
  simp only [← ws_rows_eq] at h
  simp only [ws_state_eq, List.map_map, Function.comp_def, ← ws_bits_fold_eq] at h
  exact ⟨(List.map_injective_iff.mpr ws_toEntry_injective) (by
    simpa only [List.map_map, Function.comp_def] using h.1), h.2⟩

theorem window_fold_entry (rs : List (Row V)) (e : Entry V) :
    let d := rs.foldl (fun e a => window_addBit a e) e
    d.j = e.j ∧ d.X = e.X ∧
      ∀ i, i ∈ d.Q ↔ i ∈ e.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have h := KitFG.Window.window_fold_entry rs (ws_toEntry e)
  dsimp only at h
  rw [← ws_bits_fold_eq] at h
  exact h

variable [Fintype V]

omit [DecidableEq V] [RowCodec V] in
/-- The fold selects a ready member and dominates every ready height. -/
theorem window_greatest_spec (E : Electorate V) (w : State V) :
    (∀ e, greatestReady E w = some e →
      e ∈ w.W ∧ w.h_F < e.j ∧ E.IsQuorum e.Q) ∧
    (∀ d ∈ w.W, w.h_F < d.j → E.IsQuorum d.Q →
      ∃ e, greatestReady E w = some e ∧ d.j ≤ e.j) := by
  have h := KitFG.Window.window_greatest_spec E (ws_toWindow w)
  constructor
  · intro e he
    have hm : SimplexFG.Window.greatestReady E (ws_toWindow w) = some (ws_toEntry e) := by
      rw [← ws_greatest_eq, he]
      rfl
    have hs := h.1 (ws_toEntry e) hm
    exact ⟨(ws_mem_toEntry e w.W).mp hs.1, hs.2⟩
  · intro d hd hf hq
    obtain ⟨e, he, hj⟩ := h.2 (ws_toEntry d) ((ws_mem_toEntry d w.W).mpr hd) hf hq
    rw [← ws_greatest_eq] at he
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp he
    exact ⟨a, ha, hj⟩

theorem window_strict_node (p : Params) {C P : FGBlock (Fin p.n)}
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row (Fin p.n))) (hCP : FGBlock.Preceq C P) :
    StrictPrefix C (.node P s r_s x rs) := by
  exact KitFG.Window.window_strict_node s r_s x rs hCP

/-- The row fold changes only bits of existing entries. Each new bit names
an exact finality pair from a row in this fold. -/
theorem window_fold_sources (p : Params) (rs : List (Row (Fin p.n)))
    (w : State (Fin p.n)) :
    (rs.foldl process_row w).h = w.h ∧
    (rs.foldl process_row w).T_h = w.T_h ∧
    ∀ e ∈ (rs.foldl process_row w).W, ∃ d ∈ w.W,
      d.j = e.j ∧ d.X = e.X ∧
      ∀ i ∈ e.Q, i ∈ d.Q ∨ ∃ a ∈ rs,
        a.signer = i ∧ a.finality_pair = some ⟨e.j, e.X.root⟩ := by
  have h := KitFG.Window.window_fold_sources rs (ws_toWindow w)
  rw [← ws_rows_eq] at h
  refine ⟨h.1, h.2.1, ?_⟩
  intro e he
  obtain ⟨d, hd, hj, hX, hb⟩ :=
    h.2.2 (ws_toEntry e) ((ws_mem_toEntry e _).mpr he)
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  exact ⟨c, hc, hj, hX, hb⟩

#print axioms ws_entry_fields
#print axioms ws_state_fields
#print axioms ws_initial_eq
#print axioms ws_row_eq
#print axioms ws_rows_eq
#print axioms ws_advance_eq
#print axioms ws_greatest_eq
#print axioms ws_toEntry_injective
#print axioms ws_mem_toEntry
#print axioms ws_addBit_eq
#print axioms ws_bits_fold_eq

#print axioms ws_entry_eq
#print axioms ws_state_eq
#print axioms ws_addBit_def

end AvailableChain.FGSA.Window
end
