module
public import AvailableChainKitFG.HeightCoreDef
public import AvailableChainSimplexFG.Store

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [RowCodec V]

/-- The frontier uses the height view. -/
def frontierView (v : FGHeightView V) (Vw : View V) : Height :=
  Vw.sup (fun W => (v W).h) ⊔ 1

omit [DecidableEq V] [RowCodec V] in
theorem frontierView_def (v : FGHeightView V) (Vw : View V) :
    frontierView v Vw = (Vw.sup (fun W => (v W).h) ⊔ 1) := rfl

/-- The lex selector uses the justified fields of the height view. -/
def lexMaxView (v : FGHeightView V) (F : FGBlock V) (Vw : View V) :
    Height × FGBlock V :=
  let candidates : Finset (Height × FGBlock V) :=
    (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
      (fun W => ((v W).h_j, (v W).J))
  let key := candidates.sup lexKey
  (pickPair candidates (fun p => decide (lexKey p = key))).getD (0, .genesis)

theorem lexMaxView_def (v : FGHeightView V) (F : FGBlock V) (Vw : View V) :
    lexMaxView v F Vw =
  (let candidates : Finset (Height × FGBlock V) :=
    (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
      (fun W => ((v W).h_j, (v W).J))
   let key := candidates.sup lexKey
   (pickPair candidates (fun p => decide (lexKey p = key))).getD (0, .genesis)) := rfl

/-- The frame filter uses witness heights from the height view. -/
def filteredFromView (v : FGHeightView V) (c : Controls V)
    (blocks : Finset (FGBlock V)) : Finset (FGBlock V) :=
  blocks.filter (fun B => FGBlock.preceq c.F B && FGBlock.preceq c.Z B &&
    decide (∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ (v W).h))

omit [RowCodec V] in
theorem filteredFromView_def (v : FGHeightView V) (c : Controls V)
    (blocks : Finset (FGBlock V)) :
    filteredFromView v c blocks =
  (blocks.filter (fun B => FGBlock.preceq c.F B && FGBlock.preceq c.Z B &&
    decide (∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ (v W).h))) := rfl

/-- The store controls use the height view to test for a contest. -/
def storeControlsView (v : FGHeightView V) (st : Store V) : Controls V :=
  ⟨st.F, st.h_max, st.h_j, st.J, decide (st.h_max = st.h_j + 1) &&
    decide (∃ W ∈ st.TF, (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W)⟩

omit [RowCodec V] in
theorem storeControlsView_def (v : FGHeightView V) (st : Store V) :
    storeControlsView v st =
  (⟨st.F, st.h_max, st.h_j, st.J, decide (st.h_max = st.h_j + 1) &&
    decide (∃ W ∈ st.TF, (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W)⟩) := rfl

/-- The store frame uses the view forms of the controls and filter. -/
def storeFrameView (v : FGHeightView V) (st : Store V)
    (blocks : Finset (FGBlock V)) : Finset (FGBlock V) :=
  filteredFromView v (storeControlsView v st) blocks

omit [RowCodec V] in
theorem storeFrameView_def (v : FGHeightView V) (st : Store V)
    (blocks : Finset (FGBlock V)) :
    storeFrameView v st blocks =
      filteredFromView v (storeControlsView v st) blocks := rfl

/-- The FJ controls use the view forms of the frontier, the lex selector and the
height test. -/
def fjControlsView (v : FGHeightView V) (F : FGBlock V) (Vw : View V) : Controls V :=
  let H := frontierView v Vw
  let p := lexMaxView v F Vw
  ⟨F, H, p.1, p.2, decide (H = p.1 + 1) &&
    decide (∃ W ∈ Vw, (v W).h = H ∧ ¬ FGBlock.Preceq p.2 W)⟩

theorem fjControlsView_def (v : FGHeightView V) (F : FGBlock V) (Vw : View V) :
    fjControlsView v F Vw =
  (let H := frontierView v Vw
   let p := lexMaxView v F Vw
   ⟨F, H, p.1, p.2, decide (H = p.1 + 1) &&
     decide (∃ W ∈ Vw, (v W).h = H ∧ ¬ FGBlock.Preceq p.2 W)⟩) := rfl

/-- The FJ frame uses the view forms of the controls and the filter. -/
def fjFrameView (v : FGHeightView V) (F : FGBlock V) (Vw : View V) : Frame V :=
  let c := fjControlsView v F Vw
  ⟨c.F, c.H, c.j, c.J, c.Z, c.lo, filteredFromView v c Vw, c.contest⟩

theorem fjFrameView_def (v : FGHeightView V) (F : FGBlock V) (Vw : View V) :
    fjFrameView v F Vw =
  (let c := fjControlsView v F Vw
   ⟨c.F, c.H, c.j, c.J, c.Z, c.lo, filteredFromView v c Vw, c.contest⟩) := rfl

end AvailableChain.KitFG
end
