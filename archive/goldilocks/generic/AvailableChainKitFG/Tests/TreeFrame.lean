module
public import AvailableChainKitFG.TreeFrameBridge

@[expose] public section

namespace AvailableChain.KitFG.Tests.TreeFrame

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

/-- The cumulative off-F top block contests the old frame only. -/
theorem offF_top_contest :
    fork ∈ st.TF ∧ (v fork).h = st.h_max ∧ ¬ FGBlock.Preceq st.F fork ∧
      (storeControlsView v st).contest = true ∧
      (treeStoreControlsView v st).contest = false ∧
      (fjControlsView v st.F st.TF).contest = true ∧
      (treeFjControlsView v st.F st.TF).contest = false := by decide +kernel

/-- The guarded root is J, and the floor is one below the cumulative frontier. -/
theorem guarded_root_floor :
    (treeStoreControlsView v st).Z = second ∧
      (treeStoreControlsView v st).lo = 1 ∧
      (storeControlsView v st).Z = first ∧ (storeControlsView v st).lo = 2 := by
  decide +kernel

/-- The frame excludes off-F blocks and includes a held leaf at the lower floor. -/
theorem guarded_frame_membership :
    lowLeaf ∈ treeStoreFrameView v st st.TF ∧
      lowLeaf ∉ storeFrameView v st st.TF ∧
      fork ∉ treeStoreFrameView v st st.TF := by decide +kernel

/-- Removing the off-F top block gives agreement for all four readers. -/
theorem retained_top_agreement :
    let s := { st with TF := st.TF.erase fork }
    treeStoreControlsView v s = storeControlsView v s ∧
      treeStoreFrameView v s s.TF = storeFrameView v s s.TF ∧
      treeFjControlsView v s.F s.TF = fjControlsView v s.F s.TF ∧
      treeFjFrameView v s.F s.TF = fjFrameView v s.F s.TF := by
  dsimp only
  have hs : treeStoreControlsView v { st with TF := st.TF.erase fork } =
      storeControlsView v { st with TF := st.TF.erase fork } :=
    treeStoreControlsView_eq v _ (by decide +kernel)
  have hf : treeFjControlsView v st.F (st.TF.erase fork) =
      fjControlsView v st.F (st.TF.erase fork) :=
    treeFjControlsView_eq v _ _ (by decide +kernel)
  exact ⟨hs, by simp only [treeStoreFrameView, storeFrameView, hs],
    hf, by simp only [treeFjFrameView, fjFrameView, hf]⟩

/-- An off-J top block above F contests both frames, even with an off-F top block. -/
theorem retained_contest_agreement :
    let s := { st with TF := insert sibling st.TF }
    (treeStoreControlsView v s).contest = true ∧
      treeStoreControlsView v s = storeControlsView v s ∧
      treeStoreFrameView v s s.TF = storeFrameView v s s.TF ∧
      treeFjControlsView v s.F s.TF = fjControlsView v s.F s.TF ∧
      treeFjFrameView v s.F s.TF = fjFrameView v s.F s.TF := by
  dsimp only
  have hs : treeStoreControlsView v { st with TF := insert sibling st.TF } =
      storeControlsView v { st with TF := insert sibling st.TF } := by
    unfold treeStoreControlsView storeControlsView
    congr 1
  have hf : treeFjControlsView v st.F (insert sibling st.TF) =
      fjControlsView v st.F (insert sibling st.TF) := by
    unfold treeFjControlsView fjControlsView
    dsimp only
    congr 1
  exact ⟨by decide +kernel, hs, by simp only [treeStoreFrameView, storeFrameView, hs],
    hf, by simp only [treeFjFrameView, fjFrameView, hf]⟩

/-- Without the frontier equation, an off-F top block cannot contest either frame. -/
theorem gap_agreement :
    let s := { st with h_j := 0 }
    (treeStoreControlsView v s).contest = false ∧
      treeStoreControlsView v s = storeControlsView v s ∧
      treeStoreFrameView v s s.TF = storeFrameView v s s.TF := by
  exact ⟨by decide +kernel, rfl, rfl⟩

end AvailableChain.KitFG.Tests.TreeFrame
end

-- AvailableChainKitFG/Tests/TreeFrame.lean
#print axioms AvailableChain.KitFG.Tests.TreeFrame.first
#print axioms AvailableChain.KitFG.Tests.TreeFrame.second
#print axioms AvailableChain.KitFG.Tests.TreeFrame.third
#print axioms AvailableChain.KitFG.Tests.TreeFrame.fork
#print axioms AvailableChain.KitFG.Tests.TreeFrame.sibling
#print axioms AvailableChain.KitFG.Tests.TreeFrame.lowLeaf
#print axioms AvailableChain.KitFG.Tests.TreeFrame.v
#print axioms AvailableChain.KitFG.Tests.TreeFrame.st
#print axioms AvailableChain.KitFG.Tests.TreeFrame.offF_top_contest
#print axioms AvailableChain.KitFG.Tests.TreeFrame.guarded_root_floor
#print axioms AvailableChain.KitFG.Tests.TreeFrame.guarded_frame_membership
#print axioms AvailableChain.KitFG.Tests.TreeFrame.retained_top_agreement
#print axioms AvailableChain.KitFG.Tests.TreeFrame.retained_contest_agreement
#print axioms AvailableChain.KitFG.Tests.TreeFrame.gap_agreement
