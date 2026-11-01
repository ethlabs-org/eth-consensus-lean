module
public import AvailableChainKitFG.WindowHeightBridge
public import AvailableChainKitFG.WindowViewsDef
public import AvailableChainKitFG.FrameBridge
public import AvailableChainKitFG.ProvenanceCoreDef

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

variable (E : Electorate V) (cfg : FGConfig) (K : Nat)

/-- The window hOf read equals the old read on the same arguments. -/
theorem window_hOf_eq (hK : 2 ≤ K) (B : FGBlock V) :
    (projectHeight (derive E cfg K B)).h =
      hOf E cfg B :=
  (hOf_of_bridge E cfg _ (windowHeightBridge E cfg K hK) B).symm

/-- The window frontier read equals the old read on the same arguments. -/
theorem window_frontier_eq (hK : 2 ≤ K) (blocks : View V) :
    frontierView (fun B => projectHeight (derive E cfg K B)) blocks =
      frontier E cfg blocks :=
  (frontier_of_bridge E cfg _ (windowHeightBridge E cfg K hK) blocks).symm

/-- The window lexMax read equals the old read on the same arguments. -/
theorem window_lexMax_eq (hK : 2 ≤ K) (F : FGBlock V) (blocks : View V) :
    lexMaxView (fun B => projectHeight (derive E cfg K B)) F blocks =
      lexMax E cfg F blocks :=
  (lexMax_of_bridge E cfg _ (windowHeightBridge E cfg K hK) F blocks).symm

/-- The window filteredFrom read equals the old read on the same arguments. -/
theorem window_filteredFrom_eq (hK : 2 ≤ K) (c : Controls V)
    (blocks : Finset (FGBlock V)) :
    filteredFromView (fun B => projectHeight (derive E cfg K B)) c blocks =
      filteredFrom E cfg c blocks :=
  (filteredFrom_of_bridge E cfg _ (windowHeightBridge E cfg K hK) c blocks).symm

/-- The window storeControls read equals the old read on the same arguments. -/
theorem window_storeControls_eq (hK : 2 ≤ K) (st : SimplexFG.Store V) :
    storeControlsView (fun B => projectHeight (derive E cfg K B)) st =
      storeControls E cfg st :=
  (storeControls_of_bridge E cfg _ (windowHeightBridge E cfg K hK) st).symm

/-- The window storeFrame read equals the old read on the same arguments. -/
theorem window_storeFrame_eq (hK : 2 ≤ K) (st : SimplexFG.Store V)
    (blocks : Finset (FGBlock V)) :
    storeFrameView (fun B => projectHeight (derive E cfg K B)) st blocks =
      storeFrame E cfg st blocks :=
  (storeFrame_of_bridge E cfg _ (windowHeightBridge E cfg K hK) st blocks).symm

/-- The window fjControls read equals the old read on the same arguments. -/
theorem window_fjControls_eq (hK : 2 ≤ K) (F : FGBlock V) (blocks : View V) :
    fjControlsView (fun B => projectHeight (derive E cfg K B)) F blocks =
      fjControls E cfg F blocks :=
  (fjControls_of_bridge E cfg _ (windowHeightBridge E cfg K hK) F blocks).symm

/-- The window fjFrame read equals the old read on the same arguments. -/
theorem window_fjFrame_eq (hK : 2 ≤ K) (F : FGBlock V) (blocks : View V) :
    fjFrameView (fun B => projectHeight (derive E cfg K B)) F blocks =
      fjFrame E cfg F blocks :=
  (fjFrame_of_bridge E cfg _ (windowHeightBridge E cfg K hK) F blocks).symm

/-- The direct window head fields equal the certificate head fields. -/
theorem headFields_eq_certificateHeadFields (Hd : FGBlock V) :
    headFields E cfg K Hd =
      certificateHeadFields (certificateHeight E cfg K) (certificateFinality E cfg K) Hd := rfl

end AvailableChain.KitFG.Window
end
