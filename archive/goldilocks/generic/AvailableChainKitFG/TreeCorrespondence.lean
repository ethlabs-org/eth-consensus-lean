module
public import AvailableChainKitFG.TreeFrameBridge
public import AvailableChainKitFG.FrameGeometry -- shake: keep (re-export)
public import AvailableChainKitFG.Correspondence

public section

namespace AvailableChain.KitFG
open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
variable {E : Electorate V} (v : FGHeightView V) (hL : FGHeightLaws E v)

omit [Fintype V] [DecidableEq V] in
/-- Repairs `pair_eq_of_lexKey_eq`: equal keys give equal heights; supply structural J
equality separately. A key contains only the root, so it cannot identify a full block. -/
theorem treePair_eq_of_lexKey_eq {W W' : FGBlock V}
    (hJ : (v W).J = (v W').J)
    (hk : lexKey ((v W).h_j, (v W).J) =
      lexKey ((v W').h_j, (v W').J)) :
    ((v W).h_j, (v W).J) = ((v W').h_j, (v W').J) := by
  have hh := congrArg Prod.fst (toLex.injective hk)
  exact Prod.ext hh hJ

omit [Fintype V] in
/-- Repairs `lexMax_eq_of_greatest`: require a strict maximum among distinct candidate
pairs. Only the maximum must be unique; keys of lower pairs may collide. -/
theorem treeLexMax_eq_of_greatest (F : FGBlock V) (Vw : View V)
    (K : FGBlock V) (hK : K ∈ Vw) (hFK : FGBlock.Preceq F (v K).J)
    (hmax : ∀ W ∈ Vw, FGBlock.Preceq F (v W).J →
      ((v W).h_j, (v W).J) ≠ ((v K).h_j, (v K).J) →
      lexKey ((v W).h_j, (v W).J) < lexKey ((v K).h_j, (v K).J)) :
    lexMaxView v F Vw = ((v K).h_j, (v K).J) := by
  unfold lexMaxView
  dsimp only
  have hmem : ∀ q, q ∈ (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
      (fun W => ((v W).h_j, (v W).J)) ↔
      ∃ W ∈ Vw, FGBlock.Preceq F (v W).J ∧
        ((v W).h_j, (v W).J) = q := by
    intro q
    simp only [Finset.mem_image, Finset.mem_filter, FGBlock.Preceq, and_assoc]
  have hp : ((v K).h_j, (v K).J) ∈
      (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
        (fun W => ((v W).h_j, (v W).J)) :=
    (hmem _).2 ⟨K, hK, hFK, rfl⟩
  have hsup : ((Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
      (fun W => ((v W).h_j, (v W).J))).sup lexKey =
      lexKey ((v K).h_j, (v K).J) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      obtain ⟨W, hW, hFW, rfl⟩ := (hmem q).1 hq
      by_cases heq : ((v W).h_j, (v W).J) = ((v K).h_j, (v K).J)
      · exact le_of_eq (congrArg lexKey heq)
      · exact le_of_lt (hmax W hW hFW heq)
    · exact Finset.le_sup hp
  rw [hsup, pickPair_eq_of_unique _ _ _ hp (by simp)]
  · rfl
  · intro q hq hk
    obtain ⟨W, hW, hFW, rfl⟩ := (hmem q).1 hq
    by_contra hne
    exact (ne_of_lt (hmax W hW hFW hne)) (of_decide_eq_true hk)

omit [Fintype V] in
/-- Repairs `lexMax_spec` without collision freedom. Selection either falls back (including
an ambiguous maximum), or returns a candidate with greatest key. -/
theorem treeLexMax_spec (F : FGBlock V) (Vw : View V) :
    lexMaxView v F Vw = (0, .genesis) ∨
    ∃ K ∈ Vw, FGBlock.Preceq F (v K).J ∧
      lexMaxView v F Vw = ((v K).h_j, (v K).J) ∧
      ∀ W ∈ Vw, FGBlock.Preceq F (v W).J →
        lexKey ((v W).h_j, (v W).J) ≤ lexKey ((v K).h_j, (v K).J) := by
  let T := (Vw.filter (fun W => FGBlock.preceq F (v W).J)).image
    (fun W => ((v W).h_j, (v W).J))
  let p := fun (q : Height × FGBlock V) => decide (lexKey q = T.sup lexKey)
  change (pickPair T p).getD (0, .genesis) = (0, .genesis) ∨ _
  unfold pickPair
  split
  · rename_i hu
    have hc := Finset.choose_spec (fun q => p q = true) T hu
    obtain ⟨K, hK, heq⟩ := Finset.mem_image.mp hc.1
    have hKF := Finset.mem_filter.mp hK
    have hkey : lexKey ((v K).h_j, (v K).J) = T.sup lexKey := by
      rw [heq]
      exact of_decide_eq_true hc.2
    right
    refine ⟨K, hKF.1, hKF.2, ?_, ?_⟩
    · change (pickPair T p).getD (0, .genesis) = _
      unfold pickPair
      rw [dite_eq_left hu]
      exact heq.symm
    · intro W hW hFW
      rw [hkey]
      exact Finset.le_sup (Finset.mem_image.mpr
        ⟨W, Finset.mem_filter.mpr ⟨hW, hFW⟩, rfl⟩)
  · exact Or.inl rfl

omit [Fintype V] in
/-- Repairs `lexMax_of_none` for a supplied height view and its laws. -/
theorem treeLexMax_of_none (F : FGBlock V) (Vw : View V)
    (hno : ∀ W ∈ Vw, ¬ FGBlock.Preceq F (v W).J) :
    lexMaxView v F Vw = (0, .genesis) := by
  unfold lexMaxView
  dsimp only
  have hempty : (Vw.filter (fun W => FGBlock.preceq F (v W).J)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact hno
  rw [hempty, Finset.image_empty, pickPair_empty]
  rfl

omit [Fintype V] in
/-- Repairs `fjControls_J_preceq_of_rootIsJ`: a top block must also extend F. -/
theorem treeTop_extends_J (F : FGBlock V) (Vw : View V)
    (hr : (treeFjControlsView v F Vw).rootIsJ = true)
    (W : FGBlock V) (hW : W ∈ Vw) (hFW : FGBlock.Preceq F W)
    (hH : (v W).h = (treeFjControlsView v F Vw).H) :
    FGBlock.Preceq (treeFjControlsView v F Vw).J W :=
  treeFjControlsView_J_preceq_of_rootIsJ v F Vw hr W hW hFW hH

end AvailableChain.KitFG
end
