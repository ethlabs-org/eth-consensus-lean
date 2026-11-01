module
public import AvailableChainKitFG.FrameBridgeDef
public import AvailableChainKitFG.HeightBridge -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- The bridge gives the height read by the frame. -/
theorem hOf_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v) (W : FGBlock V) :
    hOf E cfg W = (v W).h :=
  show (derive E cfg W).h = (v W).h from
    (congrArg FGHeight.h (hb W)).symm

/-- The frontier is unchanged under the height bridge. -/
theorem frontier_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v) (Vw : View V) :
    frontier E cfg Vw = frontierView v Vw := by
  rw [frontierView_def]
  exact show Vw.sup (hOf E cfg) ⊔ 1 = Vw.sup (fun W => (v W).h) ⊔ 1 from
    congrArg (fun f : FGBlock V → Height => Vw.sup f ⊔ 1)
      (funext (hOf_of_bridge E cfg v hb))

/-- The bridge gives both fields used by the lex selector. -/
theorem lexMax_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (F : FGBlock V) (Vw : View V) :
    lexMax E cfg F Vw = lexMaxView v F Vw := by
  have hj : ∀ W, (derive E cfg W).h_j = (v W).h_j :=
    fun W => (congrArg FGHeight.h_j (hb W)).symm
  have hJ : ∀ W, (derive E cfg W).J = (v W).J :=
    fun W => (congrArg FGHeight.J (hb W)).symm
  rw [lexMaxView_def]
  exact show
    (let candidates : Finset (Height × FGBlock V) :=
      (Vw.filter (fun W => FGBlock.preceq F (derive E cfg W).J)).image
        (fun W => ((derive E cfg W).h_j, (derive E cfg W).J))
     let key := candidates.sup lexKey
     (pickPair candidates (fun p => decide (lexKey p = key))).getD (0, .genesis)) = _ from by
      simp only [hj, hJ]

/-- The frame filter is unchanged under the height bridge. -/
theorem filteredFrom_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (c : Controls V) (blocks : Finset (FGBlock V)) :
    filteredFrom E cfg c blocks = filteredFromView v c blocks := by
  rw [filteredFromView_def]
  exact show (blocks.filter (fun B => FGBlock.preceq c.F B && FGBlock.preceq c.Z B &&
    decide (∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ hOf E cfg W))) = _ from by
      simp only [hOf_of_bridge E cfg v hb]

/-- The store controls are unchanged under the height bridge. -/
theorem storeControls_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v) (st : Store V) :
    storeControls E cfg st = storeControlsView v st := by
  rw [storeControlsView_def]
  exact show (⟨st.F, st.h_max, st.h_j, st.J, decide (st.h_max = st.h_j + 1) &&
    decide (∃ W ∈ st.TF, hOf E cfg W = st.h_max ∧ ¬ FGBlock.Preceq st.J W)⟩ :
      Controls V) = _ from by
        simp only [hOf_of_bridge E cfg v hb]

/-- The store frame is unchanged under the height bridge. -/
theorem storeFrame_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (st : Store V) (blocks : Finset (FGBlock V)) :
    storeFrame E cfg st blocks = storeFrameView v st blocks := by
  rw [storeFrameView_def]
  exact show filteredFrom E cfg (storeControls E cfg st) blocks = _ from by
    rw [storeControls_of_bridge E cfg v hb, filteredFrom_of_bridge E cfg v hb]

/-- The FJ controls are unchanged under the height bridge. -/
theorem fjControls_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v) (F : FGBlock V) (Vw : View V) :
    fjControls E cfg F Vw = fjControlsView v F Vw := by
  rw [fjControlsView_def]
  exact show (let H := frontier E cfg Vw
    let p := lexMax E cfg F Vw
    (⟨F, H, p.1, p.2, decide (H = p.1 + 1) &&
      decide (∃ W ∈ Vw, hOf E cfg W = H ∧ ¬ FGBlock.Preceq p.2 W)⟩ : Controls V)) = _ from by
        simp only [frontier_of_bridge E cfg v hb, lexMax_of_bridge E cfg v hb,
          hOf_of_bridge E cfg v hb]

/-- The FJ frame is unchanged under the height bridge. -/
theorem fjFrame_of_bridge (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v) (F : FGBlock V) (Vw : View V) :
    fjFrame E cfg F Vw = fjFrameView v F Vw := by
  rw [fjFrameView_def]
  exact show (let c := fjControls E cfg F Vw
    (⟨c.F, c.H, c.j, c.J, c.Z, c.lo, filteredFrom E cfg c Vw, c.contest⟩ : Frame V)) = _ from by
      simp only [fjControls_of_bridge E cfg v hb, filteredFrom_of_bridge E cfg v hb]

end AvailableChain.KitFG
end
