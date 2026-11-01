module
public import AvailableChainKitFG.HeightCoreDef
public import AvailableChainKitFG.RowBits

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [DecidableEq V] [Fintype V] in
/-- The identity selector preserves both coverage sets. -/
theorem heightSelector_id :
    HeightSelector (V := V) (fun _ rs => rs) := by
  intro σ rs
  exact ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- Rows that do not match the current entry have no height effect. -/
theorem heightSelector_selectHeightRows :
    HeightSelector (selectHeightRows (V := V)) := by
  intro σ rs
  rw [HeightRowsEq_def, heightOf_def, selectHeightRows_def]
  constructor
  · intro i
    constructor
    · rintro (hi | ⟨a, ha, hs, hm⟩)
      · exact Or.inl hi
      · exact Or.inr ⟨a, (List.mem_filter.mp ha).1, hs, hm⟩
    · rintro (hi | ⟨a, ha, hs, hm⟩)
      · exact Or.inl hi
      · refine Or.inr ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hs, hm⟩
        rw [hm]
        change decide (σ.h = σ.h ∧ σ.T_h.root = σ.T_h.root) = true
        simp only [and_self, decide_true]
  · intro i
    constructor
    · rintro (hi | ⟨a, ha, hs, hm⟩)
      · exact Or.inl hi
      · exact Or.inr ⟨a, (List.mem_filter.mp ha).1, hs, hm⟩
    · rintro (hi | ⟨a, ha, hs, hm⟩)
      · exact Or.inl hi
      · exact Or.inr ⟨a, List.mem_filter.mpr ⟨ha, hm⟩, hs, hm⟩

omit [Fintype V] in
/-- A row reads no finality field when it updates the height projection. -/
theorem process_row_height_congr
    {σ τ : ChainState V}
    (hστ : heightOf σ = heightOf τ) (a : Row V) :
    heightOf (process_row σ a) = heightOf (process_row τ a) := by
  simp only [heightOf_def, FGHeight.mk.injEq] at hστ
  obtain ⟨hL, hs, hh, hT, ht, hp, hj, hJ⟩ := hστ
  obtain ⟨sL, ss, sh, sT, sJ, sj, _, _⟩ := process_row_fields σ a
  obtain ⟨tL, ts, th, tT, tJ, tj, _, _⟩ := process_row_fields τ a
  simp only [heightOf_def, sL, ss, sh, sT, sJ, sj, tL, ts, th, tT, tJ, tj,
    process_row_target, process_row_progress, hL, hs, hh, hT, ht, hp, hj, hJ]

omit [Fintype V] in
/-- Equal resulting coverage gives equal height projections on one geometry. -/
theorem foldRows_height_eq_of_rowsEq
    {σ τ : ChainState V}
    (hστ : heightOf σ = heightOf τ)
    (B : FGBlock V) (rs ts : List (Row V))
    (hrows : HeightRowsEq (heightOf σ) rs ts) :
    heightOf (foldRows σ B rs) = heightOf (foldRows τ B ts) := by
  simp only [heightOf_def, FGHeight.mk.injEq] at hστ
  obtain ⟨hL, hs, hh, hT, ht, hp, hj, hJ⟩ := hστ
  have target : (foldRows σ B rs).target_participation =
      (foldRows τ B ts).target_participation := by
    apply Finset.ext
    intro i
    change i ∈ (rs.foldl process_row { σ with s := B.slot }).target_participation ↔
      i ∈ (ts.foldl process_row { τ with s := B.slot }).target_participation
    have left := bit_fold_iff .target rs { σ with s := B.slot } i
    have right := bit_fold_iff .target ts { τ with s := B.slot } i
    simp only [chainBits_def, rowMatchesBit_def] at left right
    exact left.trans ((hrows.1 i).trans (by simpa only [heightOf_def, hh, hT, ht] using right.symm))
  have progress : (foldRows σ B rs).progress = (foldRows τ B ts).progress := by
    apply Finset.ext
    intro i
    change i ∈ (rs.foldl process_row { σ with s := B.slot }).progress ↔
      i ∈ (ts.foldl process_row { τ with s := B.slot }).progress
    have left := bit_fold_iff .progress rs { σ with s := B.slot } i
    have right := bit_fold_iff .progress ts { τ with s := B.slot } i
    simp only [chainBits_def, rowMatchesBit_def] at left right
    exact left.trans ((hrows.2 i).trans (by simpa only [heightOf_def, hh, hT, hp] using right.symm))
  obtain ⟨sL, sh, sT, sJ, sj, _, _⟩ := foldRows_fields σ B rs
  obtain ⟨tL, th, tT, tJ, tj, _, _⟩ := foldRows_fields τ B ts
  simp only [heightOf_def, sL, sh, sT, sJ, sj, tL, th, tT, tJ, tj,
    foldRows_s, target, progress, hh, hT, hj, hJ]

omit [DecidableEq V] [RowCodec V] in
/-- Finality writes do not change the result of the height events. -/
theorem process_height_events_height_congr
    (E : Electorate V) (cfg : FGConfig)
    {σ τ : ChainState V}
    (hστ : heightOf σ = heightOf τ) :
    heightOf (process_height_events E cfg σ) =
      heightOf (process_height_events E cfg τ) := by
  have hfin : heightOf (afterFin E σ) = heightOf (afterFin E τ) := by
    simpa only [heightOf_def, afterFin_L, afterFin_s, afterFin_h, afterFin_T_h,
      afterFin_target_participation, afterFin_progress, afterFin_h_j, afterFin_J] using hστ
  have core (α β : ChainState V) (heq : heightOf α = heightOf β) :
      heightOf (if α.targetQuorum E then
        advance_height { α with J := α.T_h, h_j := α.h, finalize := ∅ }
        else if progReady E cfg α then advance_height α else α) =
      heightOf (if β.targetQuorum E then
        advance_height { β with J := β.T_h, h_j := β.h, finalize := ∅ }
        else if progReady E cfg β then advance_height β else β) := by
    have fields := heq
    simp only [heightOf_def, FGHeight.mk.injEq] at fields
    obtain ⟨hL, hs, hh, hT, ht, hp, hj, hJ⟩ := fields
    have htarget : α.targetQuorum E = β.targetQuorum E := by
      change decide (E.q ≤ E.weightOf α.target_participation) =
        decide (E.q ≤ E.weightOf β.target_participation)
      rw [ht]
    have hprog : progReady E cfg α = progReady E cfg β := by
      change (α.targetQuorum E ||
        (decide (α.T_h.slot + cfg.timeoutDelay ≤ α.s) &&
          decide (E.q ≤ E.weightOf α.progress))) =
        (β.targetQuorum E ||
        (decide (β.T_h.slot + cfg.timeoutDelay ≤ β.s) &&
          decide (E.q ≤ E.weightOf β.progress)))
      rw [htarget, hT, hs, hp]
    rw [htarget, hprog]
    split_ifs
    · change FGHeight.mk α.L α.s (α.h + 1) α.L ∅ ∅ α.h α.T_h =
        FGHeight.mk β.L β.s (β.h + 1) β.L ∅ ∅ β.h β.T_h
      rw [hL, hs, hh, hT]
    · change FGHeight.mk α.L α.s (α.h + 1) α.L ∅ ∅ α.h_j α.J =
        FGHeight.mk β.L β.s (β.h + 1) β.L ∅ ∅ β.h_j β.J
      rw [hL, hs, hh, hj, hJ]
    · exact heq
  rw [process_height_events_eq, process_height_events_eq]
  exact core _ _ hfin

/-- A selector changes row input while the transition keeps the original block. -/
theorem transition_height_eq_of_rowsEq
    (E : Electorate V) (cfg : FGConfig)
    {σ τ : ChainState V}
    (hστ : heightOf σ = heightOf τ)
    (B : FGBlock V) (rs ts : List (Row V))
    (hrows : HeightRowsEq (heightOf σ) rs ts) :
    heightOf (transition E cfg σ B rs) =
      heightOf (transition E cfg τ B ts) :=
  process_height_events_height_congr E cfg (foldRows_height_eq_of_rowsEq hστ B rs ts hrows)

/-- The identity selector gives the full SimplexFG state. -/
theorem deriveWithSelector_id
    (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    deriveWithSelector E cfg (fun _ rs => rs) B = derive E cfg B := by
  induction B with
  | genesis => rfl
  | node p s r_s x rs ih =>
      rw [deriveWithSelector_def]
      change transition E cfg (deriveWithSelector E cfg (fun _ rs => rs) p)
        (.node p s r_s x rs) rs = transition E cfg (derive E cfg p) (.node p s r_s x rs) rs
      rw [ih]

/-- Coverage preservation at each incoming state lifts through the raw fold. -/
theorem deriveWithSelector_height
    (E : Electorate V) (cfg : FGConfig)
    (sel : ChainState V → List (Row V) → List (Row V))
    (hsel : HeightSelector sel) (B : FGBlock V) :
    heightOf (deriveWithSelector E cfg sel B) =
      heightOf (derive E cfg B) := by
  induction B with
  | genesis => rfl
  | node p s r_s x rs ih =>
      rw [deriveWithSelector_def]
      exact transition_height_eq_of_rowsEq E cfg ih (.node p s r_s x rs)
        (sel (deriveWithSelector E cfg sel p) rs) rs (hsel _ _)

end AvailableChain.KitFG
end
