module
public import AvailableChainFGSA.Model.WindowViews

public import AvailableChainKitFG.WindowValidity
public import AvailableChainKitFG.WindowTransport -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Window

open AvailableChain.SimplexFG hiding process_row derive

section

private abbrev b3validity_Old := FGSA.Window.State
private abbrev b3validity_New := SimplexFG.Window.State

private def b3validity_toEntry {V : Type} (e : FGSA.Window.Entry V) : SimplexFG.Window.Entry V :=
  ⟨e.j, e.X, e.Q⟩

/-- All eleven fields are copied; no field is reconstructed from another field. -/
private def b3validity_toWindow {V : Type} (w : b3validity_Old V) : b3validity_New V :=
  ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
    w.W.map b3validity_toEntry, w.J, w.h_j, w.F, w.h_F⟩

private theorem b3validity_entry_eq {V : Type} (e : Entry V) :
    b3validity_toEntry e = ⟨e.j, e.X, e.Q⟩ := rfl

private theorem b3validity_state_eq {V : Type} (w : b3validity_Old V) :
    b3validity_toWindow w = ⟨w.L, w.s, w.h, w.T_h, w.target_participation, w.progress,
      w.W.map b3validity_toEntry, w.J, w.h_j, w.F, w.h_F⟩ := rfl

private theorem b3validity_entry_fields {V : Type} (e : FGSA.Window.Entry V) :
    (b3validity_toEntry e).j = e.j ∧ (b3validity_toEntry e).X = e.X ∧ (b3validity_toEntry e).Q =
      e.Q :=
  ⟨rfl, rfl, rfl⟩

private theorem b3validity_state_fields {V : Type} (w : b3validity_Old V) :
    (b3validity_toWindow w).L = w.L ∧ (b3validity_toWindow w).s = w.s ∧
    (b3validity_toWindow w).h = w.h ∧ (b3validity_toWindow w).T_h = w.T_h ∧
    (b3validity_toWindow w).target_participation = w.target_participation ∧
    (b3validity_toWindow w).progress = w.progress ∧ (b3validity_toWindow w).W = w.W.map
      b3validity_toEntry ∧
    (b3validity_toWindow w).J = w.J ∧ (b3validity_toWindow w).h_j = w.h_j ∧
    (b3validity_toWindow w).F = w.F ∧ (b3validity_toWindow w).h_F = w.h_F := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem b3validity_row_eq (w : b3validity_Old V) (a : Row V) :
    b3validity_toWindow (FGSA.Window.process_row w a) =
      SimplexFG.Window.process_row (b3validity_toWindow w) a := by
  have bits :
      (w.W.map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map b3validity_toEntry =
      (w.W.map b3validity_toEntry).map (fun e => if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e) := by
    simp only [List.map_map]
    congr 1
    funext e
    by_cases he : a.finality_pair = some ⟨e.j, e.X.root⟩ <;>
      simp [b3validity_entry_eq, he]
  delta FGSA.Window.process_row SimplexFG.Window.process_row
  delta NamedHeightPair.matchesEntry
  rcases a with ⟨i, hp, fp⟩
  cases hp with
  | empty =>
      simpa only [Bool.false_eq_true, ↓reduceIte, b3validity_state_eq] using
        congrArg (fun es => ({ b3validity_toWindow w with W := es } : b3validity_New V)) bits
  | vote h X t =>
      cases t <;> dsimp only <;>
        split_ifs <;> dsimp [b3validity_state_eq] <;> rw [bits] <;> simp_all [b3validity_state_eq]
      all_goals
        exfalso
        have hm : h = w.h ∧ X = w.T_h.root := of_decide_eq_true (by assumption)
        exact (by assumption : h = w.h → ¬ X = w.T_h.root) hm.1 hm.2

private theorem b3validity_rows_eq (rs : List (Row V)) (w : b3validity_Old V) :
    b3validity_toWindow (rs.foldl FGSA.Window.process_row w) =
      rs.foldl SimplexFG.Window.process_row (b3validity_toWindow w) := by
  induction rs generalizing w with
  | nil => rfl
  | cons a rs ih => simp only [List.foldl_cons, ih, b3validity_row_eq]

omit [DecidableEq V] [RowCodec V] in
end

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- R6W accepts a decoded row through either height matching or useful stale finality. -/
theorem rowValidW_iff {n : Nat} (σ : State (Fin n)) (a : RowWire n) :
    rowValidW σ a = true ↔ ∃ b, a.toRow? = some b ∧
      (heightMatch σ b = true ∨ staleUseful σ b = true) := by
  cases hd : a.toRow? <;> simp [rowValidW_def, hd, r6w_def]

/-- Either R6W arm supplies a decoded row. -/
theorem rowValidW_decodes {n : Nat} (σ : State (Fin n)) (a : RowWire n)
    (hv : rowValidW σ a = true) : ∃ b, a.toRow? = some b := by
  obtain ⟨b, hd, _⟩ := (rowValidW_iff σ a).mp hv
  exact ⟨b, hd⟩

/-- The slot does not enter either R6W arm. -/
theorem rowValidW_slot_irrel {n : Nat} (σ : State (Fin n)) (a : RowWire n)
    (s t : Slot) :
    rowValidW { σ with s := s } a = rowValidW { σ with s := t } a := rfl

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem row_validity_keys (σ : State V) (a : Row V) :
    (process_row σ a).h = σ.h ∧ (process_row σ a).T_h = σ.T_h ∧
      (process_row σ a).W.map (fun e => (e.j, e.X)) =
        σ.W.map (fun e => (e.j, e.X)) := by
  have hk : (σ.W.map (fun e =>
      if a.finality_pair = some ⟨e.j, e.X.root⟩ then
        { e with Q := insert a.signer e.Q } else e)).map (fun e => (e.j, e.X)) =
      σ.W.map (fun e => (e.j, e.X)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro e _
    dsimp only [Function.comp_def]
    split_ifs <;> rfl
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty => exact ⟨rfl, rfl, hk⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def] <;> split_ifs <;> exact ⟨rfl, rfl, hk⟩

private theorem fold_validity_keys (rows : List (Row V)) (σ : State V) :
    (rows.foldl process_row σ).h = σ.h ∧ (rows.foldl process_row σ).T_h = σ.T_h ∧
      (rows.foldl process_row σ).W.map (fun e => (e.j, e.X)) =
        σ.W.map (fun e => (e.j, e.X)) := by
  induction rows generalizing σ with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons a rows ih =>
      have hr := row_validity_keys σ a
      have hf := ih (process_row σ a)
      exact ⟨hf.1.trans hr.1, hf.2.1.trans hr.2.1, hf.2.2.trans hr.2.2⟩

omit [DecidableEq V] in
private theorem windowMatch_of_keys (σ τ : State V)
    (hk : σ.W.map (fun e => (e.j, e.X)) = τ.W.map (fun e => (e.j, e.X)))
    (a : Row V) : windowMatch σ a = windowMatch τ a := by
  have h := congrArg (fun keys : List (Height × FGBlock V) =>
    keys.any (fun key => decide (a.finality_pair = some ⟨key.1, key.2.root⟩))) hk
  simpa only [List.any_map, Function.comp_def, windowMatch_def] using h

/-- Row processing keeps height, target, and all entry keys; entry bits do not affect R6W. -/
theorem rowValidW_fold {n : Nat} (σ : State (Fin n))
    (rows : List (Row (Fin n))) (a : RowWire n) :
    rowValidW (rows.foldl process_row σ) a = rowValidW σ a := by
  rw [rowValidW_def, rowValidW_def]
  cases a.toRow? with
  | none => rfl
  | some b =>
      have result := KitFG.Window.r6w_fold (b3validity_toWindow σ) rows b
      have validity (w : State (Fin n)) :
          SimplexFG.Window.r6w (b3validity_toWindow w) b = r6w w b := by
        delta SimplexFG.Window.r6w r6w SimplexFG.Window.heightMatch heightMatch
          SimplexFG.Window.staleUseful staleUseful SimplexFG.Window.windowMatch windowMatch
        rcases b with ⟨i, hp, fp⟩
        cases hp <;> cases fp <;> dsimp only <;>
          simp only [b3validity_state_eq, List.any_map, Function.comp_def, b3validity_entry_eq]
        all_goals rfl
      rw [← b3validity_rows_eq, validity, validity] at result
      exact result

private theorem row_progress (σ : State V) (a : Row V) :
    σ.progress ⊆ (process_row σ a).progress ∧
      (heightMatch σ a = true → a.signer ∈ (process_row σ a).progress) := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty => exact ⟨Finset.Subset.refl _, fun h => Bool.noConfusion h⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def, heightMatch_def] <;>
        split_ifs <;> simp_all

private theorem fold_progress (rows : List (Row V)) (σ : State V) :
    σ.progress ⊆ (rows.foldl process_row σ).progress := by
  induction rows generalizing σ with
  | nil => exact Finset.Subset.refl _
  | cons a rows ih => exact Finset.Subset.trans (row_progress σ a).1 (ih _)

private theorem matched_progress_first (rows : List (Row V)) (σ : State V)
    (b : Row V) (hb : b ∈ rows) (hm : heightMatch σ b = true) :
    b.signer ∈ (rows.foldl process_row σ).progress := by
  induction rows generalizing σ with
  | nil => simp at hb
  | cons a rows ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact fold_progress rows _ ((row_progress σ b).2 hm)
      · apply ih (process_row σ a) hb
        simpa only [heightMatch_def, (row_validity_keys σ a).1,
          (row_validity_keys σ a).2.1] using hm

/-- Height matching supplies the first progress bit; the stale arm alone does not. -/
theorem heightMatch_progress_first (p : Params) (K : Nat) (hK : 2 ≤ K)
    (P : FGBlock (Fin p.n)) (s : Slot) (rows : List (RowWire p.n))
    (a : RowWire p.n) (b : Row (Fin p.n))
    (ha : a ∈ rows) (hd : a.toRow? = some b)
    (hm : heightMatch (parentState p K P s) b = true) :
    b.signer ∈ ((rows.filterMap RowWire.toRow?).foldl process_row
      (parentState p K P s)).progress := by
  have _capacity := hK
  have result := KitFG.Window.heightMatch_progress_first
    (rows.filterMap RowWire.toRow?) (b3validity_toWindow (parentState p K P s)) b
    (List.mem_filterMap.mpr ⟨a, ha, hd⟩) hm
  rw [← b3validity_rows_eq] at result
  exact result

#print axioms b3validity_toEntry
#print axioms b3validity_toWindow
#print axioms b3validity_entry_eq
#print axioms b3validity_state_eq
#print axioms b3validity_entry_fields
#print axioms b3validity_state_fields
#print axioms b3validity_row_eq
#print axioms b3validity_rows_eq

end AvailableChain.FGSA.Window
end
