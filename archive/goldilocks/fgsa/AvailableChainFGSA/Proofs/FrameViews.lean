module
public import AvailableChainFGSA.Model.Frame
public import AvailableChainKitFG.FrameBridge
public import AvailableChainKitFG.TreeFrameBridge
public import AvailableChainKitFG.FrameGeometry
public import AvailableChainFGSA.Proofs.Carrier
public import AvailableChainGeneric.Proofs.Pure.Fold
public import AvailableChainFGSA.Proofs.WindowHeightBridge

public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG AvailableChain.KitFG

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
One bridge supplies all active height readers. -/
theorem heightView_bridge (p : Params) : HeightBridge p.E p.cfg (heightView p) :=
  Window.windowHeightBridge p p.K_W p.kWLarge

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The active controls equal the old controls when off-J top blocks extend F. -/
theorem fgsa_controls_eq_of_top_retained (p : Params) (st : State p.n)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    controls p st = storeControls p.E p.cfg st.fg :=
  (treeStoreControlsView_eq (heightView p) st.fg hF).trans
    (storeControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) st.fg).symm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The active full tree equals the old frame when off-J top blocks extend F. -/
theorem fgsa_fullTree_eq_of_top_retained (p : Params) (st : State p.n)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    fullTree p st = storeFrame p.E p.cfg st.fg st.fg.TF :=
  (treeStoreFrameView_eq (heightView p) st.fg st.fg.TF hF).trans
    (storeFrame_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) st.fg st.fg.TF).symm

/-- The height bridge preserves the filter with the guarded canonical controls. -/
theorem fgsa_fullTree_eq_filtered (p : Params) (st : State p.n) :
    fullTree p st = filteredFrom p.E p.cfg (controls p st) st.fg.TF :=
  (filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) _ _).symm

/-- [ROOT-DIGEST-2 W1; DC root HEAD] The height view preserves the old eligibility test. -/
theorem fgsa_eligible_eq (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root)) (b : Block) :
    eligible p st raw support b =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧
        hOf p.E p.cfg P < (controls p st).lo) ||
      decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
      b.slot == st.slot p) := by
  unfold eligible
  simp only [hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The voter frame equals the old frame when off-J top blocks extend F. -/
theorem fgsa_headVote_eq_of_top_retained (p : Params) (st : State p.n) (s : Slot)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    headVote p st s =
      (if s = 0 then .genesis else
        headInTree p st (erasedList st (storeFrame p.E p.cfg st.fg (voterBlocks p st s)))
          (headVotes p st s) (headSupport p st s)) := by
  unfold headVote
  rw [treeStoreFrameView_eq (heightView p) st.fg _ hF]
  rw [← storeFrame_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]

/-- The voter frame uses the guarded canonical controls through the height bridge. -/
theorem fgsa_headVote_eq_filtered (p : Params) (st : State p.n) (s : Slot) :
    headVote p st s =
      (if s = 0 then .genesis else
        headInTree p st
          (erasedList st (filteredFrom p.E p.cfg (controls p st) (voterBlocks p st s)))
          (headVotes p st s) (headSupport p st s)) := by
  unfold headVote treeStoreFrameView
  rw [← filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  rfl

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The live-root selector returns a descendant of the active root. -/
theorem fgsa_Z_preceq_liveRoot (p : Params) (st : State p.n) :
    Block.Preceq (eraseFG (controls p st).Z) (liveRoot p st) := by
  unfold liveRoot
  dsimp only
  rcases Gen.Pure.foldl_select_mem (fun (best b : Block) => best.depth < b.depth ||
      (best.depth == b.depth && best.root < b.root)) _ _ with he | hm
  · rw [he]
    exact block_preceq_refl _
  · obtain ⟨entry, -, hr⟩ := List.mem_filterMap.1 hm
    split at hr
    · next hc =>
      obtain ⟨B, hB, he⟩ := of_decide_eq_true (Bool.and_eq_true_iff.mp hc).2
      rw [← Option.some.inj hr, ← he]
      exact eraseFG_preceq
        ((KitFG.mem_filteredFromView (heightView p) (controls p st) st.fg.TF B).mp hB).2.2.1
    · cases hr

/-- Guarding contest evidence can only lower the old band floor. -/
theorem fgsa_controls_lo_le_store (p : Params) (st : State p.n) :
    (controls p st).lo ≤ (storeControls p.E p.cfg st.fg).lo := by
  rw [storeControls_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)]
  have hc := treeStoreControlsView_contest_imp (heightView p) st.fg
  change (treeStoreControlsView (heightView p) st.fg).lo ≤ _
  unfold Controls.lo
  by_cases hn : (treeStoreControlsView (heightView p) st.fg).contest = true
  · rw [ite_eq_left hn, ite_eq_left (hc hn)]
    exact Nat.le_refl _
  · rw [ite_eq_right hn]
    split
    · exact Nat.sub_le _ _
    · exact Nat.le_refl _

/-- An old-frame block above the live root remains in the guarded frame. -/
theorem fgsa_storeFrame_mem_above_liveRoot (p : Params) (st : State p.n)
    (X : Finset (FGBlock (Fin p.n))) (b : Block)
    (hm : b ∈ erasedList st (storeFrame p.E p.cfg st.fg X))
    (ha : Block.Preceq (liveRoot p st) b) :
    b ∈ erasedList st (filteredFrom p.E p.cfg (controls p st) X) := by
  obtain ⟨hb, hkeep⟩ := List.mem_filter.mp hm
  obtain ⟨B, hmem, rfl⟩ := of_decide_eq_true hkeep
  obtain ⟨hBX, hFB, _, W, hWX, hBW, hlo⟩ :=
    (mem_filteredFrom_of_bridge p.E p.cfg (heightView p) (heightView_bridge p) _ _ B).mp hmem
  apply List.mem_filter.mpr
  refine ⟨hb, decide_eq_true ?_⟩
  refine ⟨B, (mem_filteredFrom_of_bridge
    p.E p.cfg (heightView p) (heightView_bridge p) _ _ B).mpr ?_, rfl⟩
  exact ⟨hBX, hFB,
    eraseFG_preceq_iff.mp (block_preceq_trans (fgsa_Z_preceq_liveRoot p st) ha),
    W, hWX, hBW, (fgsa_controls_lo_le_store p st).trans hlo⟩

end AvailableChain.FGSA
end
