module
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.StoreSafetyDef

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.Frame

open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3: close the finite table before checking distinct roots. -/
private theorem finite_view_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T := by
  rintro X Y ⟨W, hW, hX⟩ ⟨U, hU, hY⟩ hr
  exact hinj X (ancestor_closed_of_parent_closed T hcl W hW X hX)
    Y (ancestor_closed_of_parent_closed T hcl U hU Y hY) hr

/-- [GLY G18] Finality at height 2, without a height-3 vote. -/
def finalRow (i : Fin 4) : Row (Fin 4) := ⟨i, .empty, some ⟨2, B1a.root⟩⟩

def carrier : FGBlock (Fin 4) := .node childA 3 ⟨100⟩ 0 [finalRow 0, finalRow 1, finalRow 2]

/-- The sibling enters before finalization and remains in the cumulative tree. -/
def st : Store (Fin 4) :=
  [B1b, B1a, childA, carrier].foldl (on_block E4 cfg1) Store.init

theorem invariant : StoreInv E4 cfg1 st := by
  have step : ∀ st B, StoreInv E4 cfg1 st →
      StoreStepRoots st B → StoreInv E4 cfg1 (on_block E4 cfg1 st B) :=
    fun st B hi hr => storeInv_on_block E4 cfg1 st B hi (fun _ => hr)
  have h1 := step Store.init B1b (storeInv_init E4 cfg1)
    (finite_view_roots _ (by decide +kernel) (by decide +kernel))
  have h2 := step _ B1a h1
    (finite_view_roots _ (by decide +kernel) (by decide +kernel))
  have h3 := step _ childA h2
    (finite_view_roots _ (by decide +kernel) (by decide +kernel))
  have h4 := step _ carrier h3
    (finite_view_roots _ (by decide +kernel) (by decide +kernel))
  simpa only [st, List.foldl_cons, List.foldl_nil] using h4

theorem floor_case :
    st.F = B1a ∧ st.J = B1a ∧ (storeControls E4 cfg1 st).j = 2 ∧
      (storeControls E4 cfg1 st).H = 3 ∧ (storeControls E4 cfg1 st).contest = false ∧
      (storeControls E4 cfg1 st).lo = 2 ∧ (derive E4 cfg1 carrier).h_F = 2 ∧
      B1b ∈ st.TF ∧ hOf E4 cfg1 B1b = 2 ∧ ¬ FGBlock.Preceq st.F B1b := by
  decide +kernel

theorem no_slash :
    ∀ K ∈ st.TF, ∀ W ∈ st.TF, ∀ a ∈ chainRows K, ∀ b ∈ chainRows W,
      ¬ Slashable a b := by
  decide +kernel

theorem no_crossing :
    ∀ K ∈ st.TF, ∀ W ∈ st.TF,
      ¬ HasSlashableWeightBetween E4 (chainRows K) (chainRows W) := by
  rintro K hK W hW ⟨S, hS, hev⟩
  by_cases hempty : S = ∅
  · subst S
    exact (by unfold HasIntersectionWeight; decide : ¬ HasIntersectionWeight E4 ∅) hS
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨a, ha, b, hb, -, -, hab⟩ := hev i hi
    exact no_slash K hK W hW a ha b hb hab

/-- [GLY G18] The requested non-strict bound is false, even with no slashable
weight between any held chains and with `FaultX 4 0`. R-XING requires a strict
height bound; the top-J exception in R10 supplies no ancestry for a stale W. -/
theorem F_le_of_height_counterexample :
    StoreInv E4 cfg1 st ∧ AvailableChain.Gen.Pure.FaultX 4 0 ∧
      (∀ K ∈ st.TF, ∀ W ∈ st.TF,
        ¬ HasSlashableWeightBetween E4 (chainRows K) (chainRows W)) ∧
      ∃ W ∈ st.TF, (storeControls E4 cfg1 st).lo ≤ hOf E4 cfg1 W ∧
        ¬ FGBlock.Preceq st.F W := by
  refine ⟨invariant, ⟨by decide⟩, no_crossing, B1b, ?_, ?_, ?_⟩
  · exact floor_case.2.2.2.2.2.2.2.1
  · rw [floor_case.2.2.2.2.2.1, floor_case.2.2.2.2.2.2.2.2.1]
  · exact floor_case.2.2.2.2.2.2.2.2.2

end AvailableChain.KitFG.Tests.Frame
end

#print axioms AvailableChain.KitFG.Tests.Frame.F_le_of_height_counterexample
