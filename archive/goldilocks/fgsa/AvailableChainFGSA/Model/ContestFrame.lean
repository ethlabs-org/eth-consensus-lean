module
public import AvailableChainFGSA.Model.Tree -- shake: keep (re-export)
public import AvailableChainFGSA.Model.WindowViews
public import AvailableChainKitFG.TreeFrameDef

@[expose] public section

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- [spec 510–525, 571–599] Live controls use only contest witnesses above F. -/
def controls (p : Params) (st : State p.n) : Controls (Fin p.n) :=
  KitFG.treeStoreControlsView (heightView p) st.fg

theorem controlsNext_def (p : Params) (st : State p.n) :
    controls p st = KitFG.treeStoreControlsView (heightView p) st.fg := rfl

/-- [spec 305–326, 571–599] The full viable tree uses guarded live controls. -/
def fullTree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF

theorem fullTreeNext_def (p : Params) (st : State p.n) :
    fullTree p st = KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF := rfl

private theorem controls_eq_1_export :
    type_of% (@controls.eq_1) := @controls.eq_1
private theorem fullTree_eq_1_export :
    type_of% (@fullTree.eq_1) := @fullTree.eq_1

end AvailableChain.FGSA.Next
end
