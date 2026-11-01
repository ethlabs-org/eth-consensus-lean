module
public import AvailableChainKitFG.TreeFrameDef

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [RowCodec V]

omit [RowCodec V] in
/-- The guarded contest gives both the frontier equation and guarded EC evidence. -/
theorem treeStoreControlsView_contest_iff (v : FGHeightView V) (st : Store V) :
    (treeStoreControlsView v st).contest = true ↔
      st.h_max = st.h_j + 1 ∧ treeECView v st.F st.h_max st.J st.TF := by
  simp only [treeStoreControlsView_def, treeECView_def, Bool.and_eq_true, decide_eq_true_eq]

theorem treeFjControlsView_contest_iff (v : FGHeightView V) (F : FGBlock V)
    (Vw : View V) :
    (treeFjControlsView v F Vw).contest = true ↔
      frontierView v Vw = (lexMaxView v F Vw).1 + 1 ∧
        treeECView v F (frontierView v Vw) (lexMaxView v F Vw).2 Vw := by
  simp only [treeFjControlsView_def, treeECView_def, Bool.and_eq_true, decide_eq_true_eq]

omit [RowCodec V] in
/-- Extract an EC witness with its F guard. -/
theorem treeStoreControlsView_contest_witness (v : FGHeightView V) (st : Store V)
    (hc : (treeStoreControlsView v st).contest = true) :
    ∃ W ∈ st.TF, FGBlock.Preceq st.F W ∧
      (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W :=
  ((treeStoreControlsView_contest_iff v st).mp hc).2

theorem treeFjControlsView_contest_witness (v : FGHeightView V) (F : FGBlock V)
    (Vw : View V) (hc : (treeFjControlsView v F Vw).contest = true) :
    ∃ W ∈ Vw, FGBlock.Preceq F W ∧
      (v W).h = (treeFjControlsView v F Vw).H ∧
        ¬ FGBlock.Preceq (treeFjControlsView v F Vw).J W :=
  ((treeFjControlsView_contest_iff v F Vw).mp hc).2

omit [RowCodec V] in
/-- A guarded contest is also an old contest. -/
theorem treeStoreControlsView_contest_imp (v : FGHeightView V) (st : Store V)
    (hc : (treeStoreControlsView v st).contest = true) :
    (storeControlsView v st).contest = true := by
  obtain ⟨hh, W, hW, -, hH, hJ⟩ := (treeStoreControlsView_contest_iff v st).mp hc
  simp only [storeControlsView_def, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hh, W, hW, hH, hJ⟩

theorem treeFjControlsView_contest_imp (v : FGHeightView V) (F : FGBlock V)
    (Vw : View V) (hc : (treeFjControlsView v F Vw).contest = true) :
    (fjControlsView v F Vw).contest = true := by
  obtain ⟨hh, W, hW, -, hH, hJ⟩ := (treeFjControlsView_contest_iff v F Vw).mp hc
  simp only [fjControlsView_def, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hh, W, hW, hH, hJ⟩

omit [RowCodec V] in
/-- Off-J top blocks above F give equality with the old controls. -/
theorem treeStoreControlsView_eq (v : FGHeightView V) (st : Store V)
    (hF : ∀ W ∈ st.TF, (v W).h = st.h_max →
      ¬ FGBlock.Preceq st.J W → FGBlock.Preceq st.F W) :
    treeStoreControlsView v st = storeControlsView v st := by
  have he : (∃ W ∈ st.TF, FGBlock.Preceq st.F W ∧
      (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W) ↔
      ∃ W ∈ st.TF, (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.J W := by
    constructor
    · rintro ⟨W, hW, -, hH, hJ⟩
      exact ⟨W, hW, hH, hJ⟩
    · rintro ⟨W, hW, hH, hJ⟩
      exact ⟨W, hW, hF W hW hH hJ, hH, hJ⟩
  simp only [treeStoreControlsView_def, storeControlsView_def, he]

omit [RowCodec V] in
theorem treeStoreFrameView_eq (v : FGHeightView V) (st : Store V)
    (blocks : Finset (FGBlock V))
    (hF : ∀ W ∈ st.TF, (v W).h = st.h_max →
      ¬ FGBlock.Preceq st.J W → FGBlock.Preceq st.F W) :
    treeStoreFrameView v st blocks = storeFrameView v st blocks := by
  simp only [treeStoreFrameView_def, storeFrameView_def, treeStoreControlsView_eq v st hF]

theorem treeFjControlsView_eq (v : FGHeightView V) (F : FGBlock V) (Vw : View V)
    (hF : ∀ W ∈ Vw, (v W).h = frontierView v Vw →
      ¬ FGBlock.Preceq (lexMaxView v F Vw).2 W → FGBlock.Preceq F W) :
    treeFjControlsView v F Vw = fjControlsView v F Vw := by
  exact treeStoreControlsView_eq v
    ⟨Vw, F, (lexMaxView v F Vw).2, (lexMaxView v F Vw).1, frontierView v Vw⟩ hF

theorem treeFjFrameView_eq (v : FGHeightView V) (F : FGBlock V) (Vw : View V)
    (hF : ∀ W ∈ Vw, (v W).h = frontierView v Vw →
      ¬ FGBlock.Preceq (lexMaxView v F Vw).2 W → FGBlock.Preceq F W) :
    treeFjFrameView v F Vw = fjFrameView v F Vw := by
  simp only [treeFjFrameView_def, fjFrameView_def, treeFjControlsView_eq v F Vw hF]

omit [RowCodec V] in
/-- With no off-F top block, the guarded and old controls agree. -/
theorem treeStoreControlsView_eq_of_no_offF_top (v : FGHeightView V) (st : Store V)
    (hF : ¬ ∃ W ∈ st.TF, (v W).h = st.h_max ∧ ¬ FGBlock.Preceq st.F W) :
    treeStoreControlsView v st = storeControlsView v st := by
  apply treeStoreControlsView_eq v st
  intro W hW hH _
  by_contra hn
  exact hF ⟨W, hW, hH, hn⟩

theorem treeFjControlsView_eq_of_no_offF_top (v : FGHeightView V) (F : FGBlock V)
    (Vw : View V)
    (hF : ¬ ∃ W ∈ Vw, (v W).h = frontierView v Vw ∧ ¬ FGBlock.Preceq F W) :
    treeFjControlsView v F Vw = fjControlsView v F Vw := by
  exact treeStoreControlsView_eq_of_no_offF_top v
    ⟨Vw, F, (lexMaxView v F Vw).2, (lexMaxView v F Vw).1, frontierView v Vw⟩ hF

omit [RowCodec V] in
/-- Repair 5: a top block extends J only when it also extends F. -/
theorem treeStoreControlsView_J_preceq_of_rootIsJ (v : FGHeightView V) (st : Store V)
    (hr : (treeStoreControlsView v st).rootIsJ = true) (W : FGBlock V)
    (hW : W ∈ st.TF) (hFW : FGBlock.Preceq st.F W) (hH : (v W).h = st.h_max) :
    FGBlock.Preceq st.J W := by
  rw [treeStoreControlsView_def] at hr
  unfold Controls.rootIsJ at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hr
  obtain ⟨hHj, hc⟩ := hr
  rcases hc with hc | hc
  · exact absurd hHj hc
  · by_contra hn
    exact hc ⟨W, hW, hFW, hH, hn⟩

theorem treeFjControlsView_J_preceq_of_rootIsJ (v : FGHeightView V) (F : FGBlock V)
    (Vw : View V) (hr : (treeFjControlsView v F Vw).rootIsJ = true)
    (W : FGBlock V) (hW : W ∈ Vw) (hFW : FGBlock.Preceq F W)
    (hH : (v W).h = (treeFjControlsView v F Vw).H) :
    FGBlock.Preceq (treeFjControlsView v F Vw).J W := by
  exact treeStoreControlsView_J_preceq_of_rootIsJ v
    ⟨Vw, F, (lexMaxView v F Vw).2, (lexMaxView v F Vw).1, frontierView v Vw⟩
    hr W hW hFW hH

end AvailableChain.KitFG
end
