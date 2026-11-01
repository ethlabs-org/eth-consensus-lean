module
public import AvailableChainFGSA.Model.Spec.Frame
public import AvailableChainKitFG.FrameBridgeDef -- shake: keep (re-export)
public import AvailableChainKitFG.Ancestry
public import AvailableChainFGSA.Model.ContestFrame

public section

namespace AvailableChain.FGSA.Spec

open AvailableChain.SimplexFG

/-- This equality mentions only the accepted-tree reader from S0-T. -/
theorem frame_tree (p : Params) (st : State p.n) (root : FGBlock (Fin p.n))
    (floor : Nat) (height : FGBlock (Fin p.n) → Nat) :
    (frameOf p st root floor height).tree = Next.tree p st := rfl

theorem mem_viableTree (Φ : Frame n) (X : Finset (FGBlock (Fin n))) (B) :
    B ∈ viableTree Φ X ↔ B ∈ X ∧ FGBlock.Preceq Φ.fcRoot B ∧
      ∃ W ∈ X, W ∈ Φ.allowed ∧ FGBlock.Preceq B W := by
  simp only [viableTree, Finset.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  rfl

/-- Substitute the S0-IJ guarded controls for `c` after merge.
The only control premise is the finality field; no canonical reader is unfolded. -/
theorem viableTree_eq_filter (p : Params) (st : State p.n)
    (v : KitFG.FGHeightView (Fin p.n)) (c : Controls (Fin p.n))
    (hF : c.F = st.fg.F) (X : Finset (FGBlock (Fin p.n)))
    (hX : X ⊆ Next.tree p st) :
    viableTree (frameOf p st c.Z c.lo (fun B => (v B).h)) X =
      KitFG.filteredFromView v c X := by
  dsimp only [KitFG.filteredFromView]
  ext B
  simp only [mem_viableTree, frameOf,
    Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hB, hZ, W, hW, ⟨_, hZW, hHeight⟩, hBW⟩
    exact ⟨hB, ⟨by simpa [Next.tree, hF] using (Finset.mem_filter.mp (hX hB)).2,
      hZ⟩, W, hW, hBW, hHeight⟩
  · rintro ⟨hB, ⟨_, hZ⟩, W, hW, hBW, hHeight⟩
    refine ⟨hB, hZ, W, hW, ⟨?_, ?_, hHeight⟩, hBW⟩
    · exact Finset.mem_filter.mp (hX hW)
    · exact KitFG.preceq_trans hZ hBW

/-- The pure viable-tree correspondence instantiated with the guarded controls. -/
theorem viableTree_next_controls (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (hX : X ⊆ Next.tree p st) :
    viableTree (frameOf p st (Next.controls p st).Z (Next.controls p st).lo
      (fun B => (heightView p B).h)) X =
      KitFG.filteredFromView (heightView p) (Next.controls p st) X :=
  viableTree_eq_filter p st (heightView p) (Next.controls p st) rfl X hX

end AvailableChain.FGSA.Spec
end
