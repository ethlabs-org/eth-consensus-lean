module
public import AvailableChainKitFG.TreeTwoChanges
public import AvailableChainKitFG.TreeFrameGeometry

@[expose] public section

namespace AvailableChain.KitFG.Tests.TreeFrameHelpers
open AvailableChain.SimplexFG

/-- Pure view fixtures; no admission or run invariant is asserted. -/
def first : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 []
def second : FGBlock (Fin 4) := .node first 2 ⟨101⟩ 0 []
def third : FGBlock (Fin 4) := .node second 3 ⟨102⟩ 0 []
def fork : FGBlock (Fin 4) := .node .genesis 4 ⟨103⟩ 0 []
def sibling : FGBlock (Fin 4) := .node first 5 ⟨104⟩ 0 []
def lowLeaf : FGBlock (Fin 4) := .node second 6 ⟨105⟩ 0 []
def v : FGHeightView (Fin 4) :=
  fun W => ⟨.genesis, 0, if W = third ∨ W = fork ∨ W = sibling then 2 else 1,
    .genesis, ∅, ∅, 1, second⟩
def st : Store (Fin 4) :=
  ⟨{.genesis, first, second, third, fork, lowLeaf}, first, second, 1, 2⟩

/-- An off-F witness is old EC evidence but is not guarded EC evidence. -/
theorem offF_not_EC :
    (∃ W ∈ st.TF, (v W).h = 2 ∧ ¬ FGBlock.Preceq second W) ∧
      ¬ treeECView v first 2 second st.TF := by
  unfold treeECView
  decide +kernel

/-- The repaired top theorem accepts the retained top block. -/
theorem retained_top_extends_J :
    FGBlock.Preceq (treeFjControlsView v first st.TF).J third := by
  exact treeTop_extends_J v first st.TF (by decide +kernel) third
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The F guard cannot be omitted: the off-F top block does not extend J. -/
theorem offF_top_not_J :
    (treeFjControlsView v first st.TF).rootIsJ = true ∧
      ¬ FGBlock.Preceq (treeFjControlsView v first st.TF).J fork := by decide +kernel

/-- All three guarded phases have their expected normalized frames. -/
theorem phase_table :
    treePhaseOf v first {lowLeaf} = .gap ∧ treeNFrame v first {lowLeaf} = ⟨1, 0, none⟩ ∧
      treePhaseOf v first st.TF = .uncontested ∧
      treeNFrame v first st.TF = ⟨2, 1, some second⟩ ∧
      treePhaseOf v first (insert sibling st.TF) = .contested ∧
      treeNFrame v first (insert sibling st.TF) = ⟨2, 2, none⟩ := by
  simp only [treePhaseOf_eq, treeNFrame_eq]
  decide +kernel

/-- At frontier one, the fallback selects genesis and gives an uncontested frame. -/
theorem frontier_one_fallback :
    treePhaseOf v first ∅ = .uncontested ∧
      treeNFrame v first ∅ = ⟨1, 0, some .genesis⟩ := by
  simp only [treePhaseOf_eq, treeNFrame_eq]
  decide +kernel

/-- A true contest supplies the F guard as well as height and off-J evidence. -/
theorem guarded_witness :
    ∃ W ∈ insert sibling st.TF, FGBlock.Preceq first W ∧
      (v W).h = 2 ∧ ¬ FGBlock.Preceq second W := by
  exact treeStoreControlsView_contest_witness v { st with TF := insert sibling st.TF }
    (by decide +kernel)

/-- Pure fixtures for the changed-J branch; they do not assert an admission invariant. -/
def pairView : FGHeightView (Fin 4) :=
  fun W => ⟨.genesis, 0, 2, .genesis, ∅, ∅, 1, if W = fork then fork else second⟩
def source : Store (Fin 4) := ⟨{third, fork}, .genesis, second, 1, 2⟩
def changed : Store (Fin 4) := { source with J := fork }
def lostCarrier : Store (Fin 4) := { changed with F := fork }

/-- Persistence with unchanged J also checks the destination retention premise. -/
theorem same_J_persistence : (treeStoreControlsView pairView source).contest = true := by
  apply treeStore_contest_persist pairView source source
    (by decide +kernel) rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- When J changes to the old witness, the retained old J carrier proves the contest. -/
theorem changed_J_persistence :
    (treeStoreControlsView pairView changed).contest = true := by
  apply treeStore_contest_persist pairView source changed
    (by decide +kernel) rfl rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Retaining only the old contest witness is insufficient when J changes. -/
theorem old_carrier_retention_needed :
    (treeStoreControlsView pairView source).contest = true ∧
      FGBlock.Preceq lostCarrier.F fork ∧
      ¬ FGBlock.Preceq lostCarrier.F third ∧
      (treeStoreControlsView pairView lostCarrier).contest = false := by decide +kernel

/-- Advancing F can remove EC even with the same view and the same J. -/
theorem moving_F_loses_EC :
    treeECView pairView source.F 2 second source.TF ∧
      ¬ treeECView pairView second 2 second source.TF := by
  unfold treeECView
  decide +kernel

/-- The evidence algebra uses guarded EC, with no premise excluding off-F top blocks. -/
theorem bits_without_guarded_EC {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    {E : Electorate V} (w : FGHeightView V) (hL : FGHeightLaws E w)
    (F J : FGBlock V) (T : View V) (m : Height) (hm : 2 ≤ m)
    (hfront : frontierView w T = m)
    (huniq : ∀ K ∈ T, (w K).h_j = m - 1 → (w K).J = J)
    (hFJ : FGBlock.Preceq F J) (hEJ : treeEJ w m J T)
    (hoff : ∀ W ∈ T, (w W).h = m → ¬ FGBlock.Preceq J W → ¬ FGBlock.Preceq F W) :
    treePhaseOf w F T = .uncontested ∧ treeNFrame w F T = ⟨m, m - 1, some J⟩ := by
  apply (treeEffFrame_of_bits w hL hm hfront huniq (fun _ => hFJ)).2.1 hEJ
  rintro ⟨W, hW, hFW, hh, hJW⟩
  exact hoff W hW hh hJW hFW

/-- A caller can build EJ from a carrier and obtain the guarded contested branch. -/
theorem bits_from_carriers {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    {E : Electorate V} (w : FGHeightView V) (hL : FGHeightLaws E w)
    (F J : FGBlock V) (T : View V) (m : Height) (hm : 2 ≤ m)
    (hfront : frontierView w T = m)
    (huniq : ∀ K ∈ T, (w K).h_j = m - 1 → (w K).J = J)
    (hFJ : FGBlock.Preceq F J)
    (hcar : ∃ K ∈ T, (w K).h_j = m - 1 ∧ (w K).J = J)
    (hc : treeECView w F m J T) :
    treePhaseOf w F T = .contested ∧ treeNFrame w F T = ⟨m, m, none⟩ := by
  have hEJ : treeEJ w m J T := (treeEJ_def w m J T).symm ▸ hcar
  exact (treeEffFrame_of_bits w hL hm hfront huniq (fun _ => hFJ)).2.2 hEJ hc

/-- A root collision below the maximum is permitted. At the maximum it causes fallback.
This shows that a strict maximum does not assert root injectivity on the view. -/
theorem selection_with_root_collision :
    let twin : FGBlock (Fin 4) := .node .genesis 2 ⟨100⟩ 0 []
    let w : FGHeightView (Fin 4) := fun W =>
      ⟨.genesis, 0, 3, .genesis, ∅, ∅, if W = third then 2 else 1, W⟩
    ¬ ViewRootInj {first, twin, third} ∧
      lexKey ((w first).h_j, (w first).J) = lexKey ((w twin).h_j, (w twin).J) ∧
      lexMaxView w .genesis {first, twin} = (0, .genesis) ∧
      lexMaxView w .genesis {first, twin, third} = (2, third) := by
  dsimp only
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_⟩
  · intro hinj
    have heq := hinj first (.node .genesis 2 ⟨100⟩ 0 [])
      ⟨first, by decide +kernel, preceq_refl _⟩
      ⟨.node .genesis 2 ⟨100⟩ 0 [], by decide +kernel, preceq_refl _⟩ rfl
    exact (by decide +kernel : first ≠ .node .genesis 2 ⟨100⟩ 0 []) heq
  · apply treeLexMax_eq_of_greatest _ _ _ third (by decide +kernel)
      (by decide +kernel)
    decide +kernel

end AvailableChain.KitFG.Tests.TreeFrameHelpers
end

-- AvailableChainKitFG/Tests/TreeFrameHelpers.lean
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.first
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.second
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.third
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.fork
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.sibling
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.lowLeaf
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.v
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.st
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.offF_not_EC
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.retained_top_extends_J
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.offF_top_not_J
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.phase_table
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.frontier_one_fallback
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.guarded_witness
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.pairView
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.source
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.changed
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.lostCarrier
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.same_J_persistence
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.changed_J_persistence
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.old_carrier_retention_needed
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.moving_F_loses_EC
#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.bits_without_guarded_EC

#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.bits_from_carriers

#print axioms AvailableChain.KitFG.Tests.TreeFrameHelpers.selection_with_root_collision
