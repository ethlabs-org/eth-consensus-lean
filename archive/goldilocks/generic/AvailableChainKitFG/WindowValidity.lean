module
public import AvailableChainKitFG.WindowViewsDef -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [RowCodec V]

private theorem b3Validity_row_validity_keys (σ : State V) (a : Row V) :
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

private theorem b3Validity_fold_validity_keys (rows : List (Row V)) (σ : State V) :
    (rows.foldl process_row σ).h = σ.h ∧ (rows.foldl process_row σ).T_h = σ.T_h ∧
      (rows.foldl process_row σ).W.map (fun e => (e.j, e.X)) =
        σ.W.map (fun e => (e.j, e.X)) := by
  induction rows generalizing σ with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons a rows ih =>
      have hr := b3Validity_row_validity_keys σ a
      have hf := ih (process_row σ a)
      exact ⟨hf.1.trans hr.1, hf.2.1.trans hr.2.1, hf.2.2.trans hr.2.2⟩

omit [DecidableEq V] in
private theorem b3Validity_windowMatch_of_keys (σ τ : State V)
    (hk : σ.W.map (fun e => (e.j, e.X)) = τ.W.map (fun e => (e.j, e.X)))
    (a : Row V) : windowMatch σ a = windowMatch τ a := by
  have h := congrArg (fun keys : List (Height × FGBlock V) =>
    keys.any (fun key => decide (a.finality_pair = some ⟨key.1, key.2.root⟩))) hk
  simpa only [List.any_map, Function.comp_def, windowMatch_def] using h

/-- The decoded R6W predicate is unchanged by the row fold. -/
theorem r6w_fold (σ : State V) (rows : List (Row V)) (b : Row V) :
    r6w (rows.foldl process_row σ) b = r6w σ b := by
  obtain ⟨hh, hT, hk⟩ := b3Validity_fold_validity_keys rows σ
  have hm := b3Validity_windowMatch_of_keys _ _ hk b
  have hs : staleUseful (rows.foldl process_row σ) b = staleUseful σ b := by
    obtain ⟨i, pair, fp⟩ := b
    cases pair with
    | empty => rfl
    | vote h X t =>
        cases fp with
        | none => rfl
        | some f =>
            exact congrArg₂ (fun x y : Bool => x && y)
              (congrArg (fun k => decide (f.height < h ∧ h < k)) hh) hm
  simp only [r6w_def, heightMatch_def, hh, hT, hs]

private theorem b3Validity_row_progress (σ : State V) (a : Row V) :
    σ.progress ⊆ (process_row σ a).progress ∧
      (heightMatch σ a = true → a.signer ∈ (process_row σ a).progress) := by
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty => exact ⟨Finset.Subset.refl _, fun h => Bool.noConfusion h⟩
  | vote h X t =>
      cases t <;> simp only [process_row_def, heightMatch_def] <;>
        split_ifs <;> simp_all

private theorem b3Validity_fold_progress (rows : List (Row V)) (σ : State V) :
    σ.progress ⊆ (rows.foldl process_row σ).progress := by
  induction rows generalizing σ with
  | nil => exact Finset.Subset.refl _
  | cons a rows ih => exact Finset.Subset.trans (b3Validity_row_progress σ a).1 (ih _)

private theorem b3Validity_matched_progress_first (rows : List (Row V)) (σ : State V)
    (b : Row V) (hb : b ∈ rows) (hm : heightMatch σ b = true) :
    b.signer ∈ (rows.foldl process_row σ).progress := by
  induction rows generalizing σ with
  | nil => simp at hb
  | cons a rows ih =>
      rcases List.mem_cons.mp hb with rfl | hb
      · exact b3Validity_fold_progress rows _ ((b3Validity_row_progress σ b).2 hm)
      · apply ih (process_row σ a) hb
        simpa only [heightMatch_def, (b3Validity_row_validity_keys σ a).1,
          (b3Validity_row_validity_keys σ a).2.1] using hm

/-- Height matching supplies the first progress bit from an exact decoded row. -/
theorem heightMatch_progress_first (rows : List (Row V)) (σ : State V)
    (b : Row V) (hb : b ∈ rows) (hm : heightMatch σ b = true) :
    b.signer ∈ (rows.foldl process_row σ).progress :=
  b3Validity_matched_progress_first rows σ b hb hm

end AvailableChain.KitFG.Window
end
