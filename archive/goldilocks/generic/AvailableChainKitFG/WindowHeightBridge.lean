module
public import AvailableChainKitFG.WindowViewsDef
public import AvailableChainKitFG.HeightLaws

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [Fintype V] in
/-- [spec 1202–1218] Finality writes leave the height projection unchanged. -/
private theorem row_height {w : State V} {σ : ChainState V}
    (heq : projectHeight w = heightOf σ) (a : Row V) :
    projectHeight (process_row w a) = heightOf (SimplexFG.process_row σ a) := by
  simp only [projectHeight_def, heightOf_def, FGHeight.mk.injEq] at heq
  obtain ⟨hL, hs, hh, hT, ht, hp, hj, hJ⟩ := heq
  obtain ⟨i, pair, fp⟩ := a
  cases pair with
  | empty =>
      simp only [process_row_def, SimplexFG.process_row, NamedHeightPair.matchesEntry]
      split_ifs <;> simp_all only [projectHeight_def, heightOf_def]
  | vote k e timeout =>
      cases timeout <;>
        simp only [process_row_def, SimplexFG.process_row, hh, hT] <;>
        split_ifs <;> simp_all only [projectHeight_def, heightOf_def]

omit [Fintype V] in
/-- [spec 1193–1196] The row fold preserves equal height projections. -/
private theorem fold_height (rows : List (Row V))
    {w : State V} {σ : ChainState V} (heq : projectHeight w = heightOf σ) :
    projectHeight (rows.foldl process_row w) =
      heightOf (rows.foldl SimplexFG.process_row σ) := by
  induction rows generalizing w σ with
  | nil => exact heq
  | cons a rows ih => exact ih (row_height heq a)

omit [DecidableEq V] [RowCodec V] in
/-- [spec 1222–1227] Greatest-ready selection and pruning preserve height. -/
private theorem finality_height (E : Electorate V) (w : State V) :
    projectHeight (finalizeWindow E w) = projectHeight w := by
  rw [finalizeWindow_def]
  cases greatestReady E w <;> simp only [projectHeight_def]

omit [DecidableEq V] [RowCodec V] in
/-- [spec 1220–1250] Both evaluators test target before mature progress. -/
private theorem events_height (E : Electorate V) (cfg : FGConfig) (K : Nat)
    {w : State V} {σ : ChainState V} (heq : projectHeight w = heightOf σ) :
    projectHeight (process_height_events E cfg K w) =
      heightOf (SimplexFG.process_height_events E cfg σ) := by
  have hfin : projectHeight (finalizeWindow E w) = heightOf (afterFin E σ) := by
    rw [finality_height]
    simpa only [heightOf_def, afterFin_L, afterFin_s, afterFin_h, afterFin_T_h,
      afterFin_target_participation, afterFin_progress, afterFin_h_j, afterFin_J] using heq
  have core (α : State V) (β : ChainState V) (h : projectHeight α = heightOf β) :
      projectHeight (if targetQuorum E α then
        advance_height { α with
          J := α.T_h
          h_j := α.h
          W := (α.W ++ [Entry.mk α.h α.T_h ∅]).drop ((α.W ++ [Entry.mk α.h α.T_h ∅]).length - K) }
        else if progReady E cfg α then advance_height α else α) =
      heightOf (if β.targetQuorum E then
        SimplexFG.advance_height { β with J := β.T_h, h_j := β.h, finalize := ∅ }
        else if SimplexFG.progReady E cfg β then SimplexFG.advance_height β else β) := by
    have fields := h
    simp only [projectHeight_def, heightOf_def, FGHeight.mk.injEq] at fields
    obtain ⟨hL, hs, hh, hT, ht, hp, hj, hJ⟩ := fields
    have htarget : targetQuorum E α = β.targetQuorum E := by
      rw [targetQuorum_def]
      change decide (E.q ≤ E.weightOf α.target_participation) =
        decide (E.q ≤ E.weightOf β.target_participation)
      rw [ht]
    have hprog : progReady E cfg α = SimplexFG.progReady E cfg β := by
      rw [progReady_def, htarget]
      rw [hT, hs, hp]
      rfl
    rw [htarget, hprog]
    split_ifs
    · simp only [advance_height_def, projectHeight_def, SimplexFG.advance_height,
        heightOf_def, hL, hs, hh, hT]
    · simp only [advance_height_def, projectHeight_def, SimplexFG.advance_height,
        heightOf_def, hL, hs, hh, hj, hJ]
    · exact h
  rw [process_height_events_def, process_height_events_eq]
  exact core _ _ hfin

/-- [bp.heightBridge.v1] The raw window evaluator refines the height fold
on the same block tree. Capacity does not affect this projection. -/
theorem heightRefinement (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K) :
    HeightFoldRefinement E cfg projectHeight initial (transition E cfg K) (derive E cfg K) := by
  have _capacity := hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [initial_def, projectHeight_def]
    rfl
  · rw [derive_def]
  · intro q s r x rs
    rw [derive_def]
  · intro w σ B rs heq
    rw [transition_def]
    apply events_height
    have hslot : projectHeight { w with s := B.slot } =
        heightOf { σ with s := B.slot } := by
      simp only [projectHeight_def, heightOf_def, FGHeight.mk.injEq] at heq ⊢
      exact ⟨heq.1, trivial, heq.2.2⟩
    have hfold := fold_height rs hslot
    simp only [projectHeight_def, heightOf_def, FGHeight.mk.injEq] at hfold ⊢
    exact ⟨trivial, hfold.2⟩

/-- [bp.heightBridge.v1] Lift the step refinement over the original tree. -/
theorem windowHeightBridge (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K) :
    HeightBridge E cfg (fun B => projectHeight (derive E cfg K B)) :=
  heightBridge_of_refinement E cfg projectHeight initial (transition E cfg K)
    (derive E cfg K) (heightRefinement E cfg K hK)

/-- The bridge transfers all height laws and their row certificates. -/
theorem windowHeightLaws (E : Electorate V) (cfg : FGConfig) (K : Nat) (hK : 2 ≤ K) :
    FGHeightLaws E (fun B => projectHeight (derive E cfg K B)) :=
  heightLaws_of_bridge E cfg _ (windowHeightBridge E cfg K hK)

end AvailableChain.KitFG.Window
end
