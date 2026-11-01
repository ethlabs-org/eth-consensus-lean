module
public import AvailableChainFGSA.Model.Tree -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Frame
public import AvailableChainKitFG.Ancestry

public section

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- [spec 305–326] Tree membership means that the block is held and above F. -/
theorem mem_tree (p : Params) (st : State p.n) (B : FGBlock (Fin p.n)) :
    B ∈ tree p st ↔ B ∈ st.fg.TF ∧ FGBlock.Preceq st.fg.F B := by
  simp only [tree, Finset.mem_filter, FGBlock.Preceq]

/-- [spec 305–326] The frame root belongs to the tree when the store holds it. -/
theorem F_mem_tree (p : Params) (st : State p.n) (hF : st.fg.F ∈ st.fg.TF) :
    st.fg.F ∈ tree p st := by
  exact (mem_tree p st st.fg.F).mpr ⟨hF, KitFG.preceq_refl _⟩

/-- [spec 305–326, 339–353] The tree is a subset of the cumulative accepted store. -/
theorem tree_subset_TF (p : Params) (st : State p.n) :
    tree p st ⊆ st.fg.TF := by
  intro B hB
  exact ((mem_tree p st B).mp hB).1

/-- [spec 305–326; old spec 1033–1037] The viable full tree also requires extension of F,
so it is a subset of `Φ.tree`. No store invariant is needed. -/
theorem fullTree_subset_tree (p : Params) (st : State p.n) :
    fullTree p st ⊆ tree p st := by
  intro B hB
  have h := Finset.mem_filter.mp hB
  apply (mem_tree p st B).mpr
  exact ⟨h.1, (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h.2).1).1⟩

/-- [spec 305–326, 975–1015] Erased membership requires both a held base block
and an FG block in the supplied set with that erasure. -/
theorem mem_erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n)))
    (b : Block) :
    b ∈ erasedList st X ↔ b ∈ st.base.blocks ∧ ∃ B ∈ X, eraseFG B = b := by
  simp [erasedList]

/-- [old spec 1025–1037; model representation] The new list helper keeps the
canonical erasure order and membership test. -/
theorem erasedList_eq {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) :
    erasedList st X = FGSA.erasedList st X := rfl

end AvailableChain.FGSA.Next
end
