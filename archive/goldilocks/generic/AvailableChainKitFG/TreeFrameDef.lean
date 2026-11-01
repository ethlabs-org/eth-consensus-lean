module
public import AvailableChainKitFG.FrameBridgeDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- [spec 510–525] Store contest witnesses must extend F. -/
def treeStoreControlsView (v : FGHeightView V) (st : Store V) : Controls V :=
  ⟨st.F, st.h_max, st.h_j, st.J, decide (st.h_max = st.h_j + 1) &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq st.F W ∧
      (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W)⟩

omit [RowCodec V] in
theorem treeStoreControlsView_def (v : FGHeightView V) (st : Store V) :
    treeStoreControlsView v st =
  (⟨st.F, st.h_max, st.h_j, st.J, decide (st.h_max = st.h_j + 1) &&
    decide (∃ W ∈ st.TF, FGBlock.Preceq st.F W ∧
      (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W)⟩) := rfl

/-- The store frame uses the view forms of the controls and filter. -/
def treeStoreFrameView (v : FGHeightView V) (st : Store V)
    (blocks : Finset (FGBlock V)) : Finset (FGBlock V) :=
  filteredFromView v (treeStoreControlsView v st) blocks

omit [RowCodec V] in
theorem treeStoreFrameView_def (v : FGHeightView V) (st : Store V)
    (blocks : Finset (FGBlock V)) :
    treeStoreFrameView v st blocks =
      filteredFromView v (treeStoreControlsView v st) blocks := rfl

/-- [spec 510–525] FJ controls keep the cumulative frontier and lex selector.
Contest witnesses must extend F. -/
def treeFjControlsView (v : FGHeightView V) (F : FGBlock V) (Vw : View V) : Controls V :=
  let H := frontierView v Vw
  let p := lexMaxView v F Vw
  ⟨F, H, p.1, p.2, decide (H = p.1 + 1) &&
    decide (∃ W ∈ Vw, FGBlock.Preceq F W ∧
      (v W).h = H ∧ ¬ FGBlock.Preceq p.2 W)⟩

theorem treeFjControlsView_def (v : FGHeightView V) (F : FGBlock V) (Vw : View V) :
    treeFjControlsView v F Vw =
  (let H := frontierView v Vw
   let p := lexMaxView v F Vw
   ⟨F, H, p.1, p.2, decide (H = p.1 + 1) &&
     decide (∃ W ∈ Vw, FGBlock.Preceq F W ∧
      (v W).h = H ∧ ¬ FGBlock.Preceq p.2 W)⟩) := rfl

/-- The FJ frame uses the view forms of the controls and the filter. -/
def treeFjFrameView (v : FGHeightView V) (F : FGBlock V) (Vw : View V) : Frame V :=
  let c := treeFjControlsView v F Vw
  ⟨c.F, c.H, c.j, c.J, c.Z, c.lo, filteredFromView v c Vw, c.contest⟩

theorem treeFjFrameView_def (v : FGHeightView V) (F : FGBlock V) (Vw : View V) :
    treeFjFrameView v F Vw =
  (let c := treeFjControlsView v F Vw
   ⟨c.F, c.H, c.j, c.J, c.Z, c.lo, filteredFromView v c Vw, c.contest⟩) := rfl

/-- Guarded EC evidence records a held top block above F and off J. -/
def treeECView (v : FGHeightView V) (F : FGBlock V) (m : Height)
    (J : FGBlock V) (Vw : View V) : Prop :=
  ∃ W ∈ Vw, FGBlock.Preceq F W ∧ (v W).h = m ∧ ¬ FGBlock.Preceq J W

omit [RowCodec V] in
theorem treeECView_def (v : FGHeightView V) (F : FGBlock V) (m : Height)
    (J : FGBlock V) (Vw : View V) :
    treeECView v F m J Vw =
      (∃ W ∈ Vw, FGBlock.Preceq F W ∧ (v W).h = m ∧ ¬ FGBlock.Preceq J W) := rfl

end AvailableChain.KitFG
end
