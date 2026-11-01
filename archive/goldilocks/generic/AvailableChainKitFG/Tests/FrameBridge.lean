module
public import AvailableChainKitFG.FrameBridge -- shake: keep (axioms)

public section

namespace AvailableChain.KitFG.Tests.FrameBridge

open AvailableChain.SimplexFG

-- Each concrete test uses the evaluator with selected height rows.
def frameBridgeSelectedView : FGHeightView (Fin 4) :=
  fun B => heightOf (deriveWithSelector E4 cfg1 selectHeightRows B)

theorem frameBridge_selected_bridge : HeightBridge E4 cfg1 frameBridgeSelectedView :=
  deriveWithSelector_height E4 cfg1 selectHeightRows heightSelector_selectHeightRows

example : hOf E4 cfg1 B3 = (frameBridgeSelectedView B3).h :=
  hOf_of_bridge E4 cfg1 _ frameBridge_selected_bridge B3

example : frontier E4 cfg1 {.genesis, B1, B2, B3} =
    frontierView frameBridgeSelectedView {.genesis, B1, B2, B3} :=
  frontier_of_bridge E4 cfg1 _ frameBridge_selected_bridge _

example : lexMax E4 cfg1 B1 {.genesis, B1, B2, B3} =
    lexMaxView frameBridgeSelectedView B1 {.genesis, B1, B2, B3} :=
  lexMax_of_bridge E4 cfg1 _ frameBridge_selected_bridge B1 _

example : filteredFrom E4 cfg1 (storeControls E4 cfg1 stC) stC.TF =
    filteredFromView frameBridgeSelectedView (storeControls E4 cfg1 stC) stC.TF :=
  filteredFrom_of_bridge E4 cfg1 _ frameBridge_selected_bridge _ _

example : storeControls E4 cfg1 stC = storeControlsView frameBridgeSelectedView stC :=
  storeControls_of_bridge E4 cfg1 _ frameBridge_selected_bridge stC

example : storeFrame E4 cfg1 stC stC.TF = storeFrameView frameBridgeSelectedView stC stC.TF :=
  storeFrame_of_bridge E4 cfg1 _ frameBridge_selected_bridge stC stC.TF

-- The SimplexFG instance equalities are immediate.
variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

example (E : Electorate V) (cfg : FGConfig) (W : FGBlock V) :
    hOf E cfg W = (simplexHeightView E cfg W).h := rfl

example (E : Electorate V) (cfg : FGConfig) (Vw : View V) :
    frontier E cfg Vw = frontierView (simplexHeightView E cfg) Vw := rfl

example (E : Electorate V) (cfg : FGConfig) (F : FGBlock V) (Vw : View V) :
    lexMax E cfg F Vw = lexMaxView (simplexHeightView E cfg) F Vw := rfl

example (E : Electorate V) (cfg : FGConfig) (c : Controls V)
    (blocks : Finset (FGBlock V)) :
    filteredFrom E cfg c blocks = filteredFromView (simplexHeightView E cfg) c blocks := rfl

example (E : Electorate V) (cfg : FGConfig) (st : Store V) :
    storeControls E cfg st = storeControlsView (simplexHeightView E cfg) st := rfl

example (E : Electorate V) (cfg : FGConfig) (st : Store V)
    (blocks : Finset (FGBlock V)) :
    storeFrame E cfg st blocks = storeFrameView (simplexHeightView E cfg) st blocks := rfl

example (E : Electorate V) (cfg : FGConfig) (F : FGBlock V) (Vw : View V) :
    fjControls E cfg F Vw = fjControlsView (simplexHeightView E cfg) F Vw := rfl

example (E : Electorate V) (cfg : FGConfig) (F : FGBlock V) (Vw : View V) :
    fjFrame E cfg F Vw = fjFrameView (simplexHeightView E cfg) F Vw := rfl

example : fjFrame E4 cfg1 stC.F stC.TF = fjFrameView frameBridgeSelectedView stC.F stC.TF :=
  fjFrame_of_bridge E4 cfg1 _ frameBridge_selected_bridge stC.F stC.TF

#print axioms frontierView_def
#print axioms lexMaxView_def
#print axioms filteredFromView_def
#print axioms storeControlsView_def
#print axioms storeFrameView_def
#print axioms hOf_of_bridge
#print axioms frontier_of_bridge
#print axioms lexMax_of_bridge
#print axioms filteredFrom_of_bridge
#print axioms storeControls_of_bridge
#print axioms storeFrame_of_bridge
#print axioms fjControlsView_def
#print axioms fjFrameView_def
#print axioms fjControls_of_bridge
#print axioms fjFrame_of_bridge
#print axioms frameBridge_selected_bridge

end AvailableChain.KitFG.Tests.FrameBridge
end
