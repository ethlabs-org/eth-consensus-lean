module
public import AvailableChainFGSA.Model.ContestFrame -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Frame
public import AvailableChainFGSA.Model.Legacy.Frame
public import AvailableChainKitFG.TreeFrameBridge

public section

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- Pure store comparison: every off-J top block must extend F. -/
theorem controls_eq_of_top_extends_F (p : Params) (st : State p.n)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    controls p st = FGSA.controls p st := by
  have _ := hF
  rfl

theorem fullTree_eq_of_top_extends_F (p : Params) (st : State p.n)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    fullTree p st = FGSA.fullTree p st := by
  have _ := hF
  rfl

theorem controls_contest_imp (p : Params) (st : State p.n)
    (hc : (controls p st).contest = true) : (FGSA.controls p st).contest = true := hc

/-- Compare canonical guarded controls with the complete Legacy reader chain. -/
theorem port_controls_eq_legacy_of_top_extends_F (p : Params) (st : State p.n)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    FGSA.controls p st = Legacy.controls p st :=
  KitFG.treeStoreControlsView_eq (heightView p) st.fg hF

/-- The same top retention condition gives the old viable tree. -/
theorem port_fullTree_eq_legacy_of_top_extends_F (p : Params) (st : State p.n)
    (hF : ∀ W ∈ st.fg.TF, (heightView p W).h = st.fg.h_max →
      ¬ FGBlock.Preceq st.fg.J W → FGBlock.Preceq st.fg.F W) :
    FGSA.fullTree p st = Legacy.fullTree p st :=
  KitFG.treeStoreFrameView_eq (heightView p) st.fg st.fg.TF hF

/-- A canonical contest supplies a Legacy contest without an extra premise. -/
theorem port_controls_contest_imp_legacy (p : Params) (st : State p.n)
    (hc : (FGSA.controls p st).contest = true) :
    (Legacy.controls p st).contest = true :=
  KitFG.treeStoreControlsView_contest_imp (heightView p) st.fg hc

theorem controls_contest_witness (p : Params) (st : State p.n)
    (hc : (controls p st).contest = true) :
    ∃ W ∈ st.fg.TF, FGBlock.Preceq st.fg.F W ∧
      (heightView p W).h = st.fg.h_max ∧ ¬ FGBlock.Preceq st.fg.J W :=
  KitFG.treeStoreControlsView_contest_witness (heightView p) st.fg hc

theorem controls_J_preceq_of_rootIsJ (p : Params) (st : State p.n)
    (hr : (controls p st).rootIsJ = true) (W : FGBlock (Fin p.n))
    (hW : W ∈ st.fg.TF) (hFW : FGBlock.Preceq st.fg.F W)
    (hH : (heightView p W).h = st.fg.h_max) : FGBlock.Preceq st.fg.J W :=
  KitFG.treeStoreControlsView_J_preceq_of_rootIsJ (heightView p) st.fg hr W hW hFW hH

/-- The guarded viable full tree is a subset of the S0-T accepted tree. -/
theorem contestFullTree_subset_tree (p : Params) (st : State p.n) :
    fullTree p st ⊆ tree p st := by
  intro B hB
  have h := Finset.mem_filter.mp hB
  apply Finset.mem_filter.mpr
  exact ⟨h.1, (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h.2).1).1⟩

end AvailableChain.FGSA.Next
end
