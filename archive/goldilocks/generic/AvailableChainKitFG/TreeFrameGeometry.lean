module
public import AvailableChainKitFG.TreeFrameBridge
public import AvailableChainKitFG.StoreBounds

public section

namespace AvailableChain.KitFG
open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [RowCodec V]

omit [RowCodec V] in
/-- Repairs the witness step of `healing_phase_contest_persist` for pure stores.
Destination retention covers every held top block, including the old J carrier.
The supplied entry law covers both equal and changed J; no run is assumed. -/
theorem treeStore_contest_persist (v : FGHeightView V) (src dst : Store V)
    (hsub : src.TF ⊆ dst.TF) (hH : src.h_max = dst.h_max)
    (hj : src.h_j = dst.h_j)
    (hretain : ∀ W ∈ dst.TF, (v W).h = dst.h_max → FGBlock.Preceq dst.F W)
    (hsrc : ∃ C ∈ src.TF, src.h_j = (v C).h_j ∧ src.J = (v C).J)
    (hdst : ∃ D ∈ dst.TF, dst.h_j = (v D).h_j ∧ dst.J = (v D).J)
    (hbound : ∀ C ∈ src.TF, (v C).h ≤ src.h_max)
    (hbelow : ∀ C ∈ src.TF, (v C).h_j < (v C).h)
    (hanc : ∀ C ∈ src.TF, FGBlock.Preceq (v C).J C)
    (heq : ∀ C ∈ src.TF, ∀ D ∈ dst.TF, (v C).h_j = (v D).h_j →
      FGBlock.Preceq (v C).J C → FGBlock.Preceq (v D).J C → (v C).J = (v D).J)
    (hc : (treeStoreControlsView v src).contest = true) :
    (treeStoreControlsView v dst).contest = true := by
  obtain ⟨ht, W, hW, _, hWh, hWJ⟩ := (treeStoreControlsView_contest_iff v src).mp hc
  apply (treeStoreControlsView_contest_iff v dst).mpr
  refine ⟨by rw [← hH, ← hj]; exact ht, ?_⟩
  by_cases hJ : src.J = dst.J
  · have hh := hWh.trans hH
    exact ⟨W, hsub hW, hretain W (hsub hW) hh, hh, hJ ▸ hWJ⟩
  · obtain ⟨C, hC, hjC, hJC⟩ := hsrc
    obtain ⟨D, hD, hjD, hJD⟩ := hdst
    have hlo := hbelow C hC
    have hhi := hbound C hC
    have hh : (v C).h = dst.h_max := by
      simp only [Height] at *
      omega
    refine ⟨C, hsub hC, hretain C (hsub hC) hh, hh, ?_⟩
    intro hDC
    apply hJ
    rw [hJC, hJD]
    exact heq C hC D hD (hjC.symm.trans (hj.trans hjD)) (hanc C hC) (hJD ▸ hDC)

variable [Fintype V]

/-- Repairs `healing_phase_contest_persist` using supplied store and certificate laws.
A fixed frontier cap and monotone justified height give equal top heights.
Destination top retention is required even if the cached J changes. -/
theorem treeStore_contest_persist_of_inv (E : Electorate V)
    (v : FGHeightView V) (f : FGFinalityView V)
    (hL : FGCertificateLaws E v f) (hJ : FGJustificationLaws v)
    (src dst : Store V) (hs : FGStoreInvariant v f src) (hd : FGStoreInvariant v f dst)
    (hsub : src.TF ⊆ dst.TF) (hmono : src.h_j ≤ dst.h_j)
    (hcap : dst.h_max ≤ src.h_max)
    (hretain : ∀ W ∈ dst.TF, (v W).h = dst.h_max → FGBlock.Preceq dst.F W)
    (hc : (treeStoreControlsView v src).contest = true) :
    dst.h_max = src.h_max ∧ (treeStoreControlsView v dst).contest = true := by
  have ht := ((treeStoreControlsView_contest_iff v src).mp hc).1
  have hlt := store_justified_lt E v f hL dst hd
  have hH : src.h_max = dst.h_max := by simp only [Height] at *; omega
  have hj : src.h_j = dst.h_j := by simp only [Height] at *; omega
  refine ⟨hH.symm, treeStore_contest_persist v src dst hsub hH hj hretain ?_ ?_
    (fun C hC => store_height_le v f src hs hC)
    (fun C _ => hL.height.justified_below_height C)
    (fun C _ => preceq_trans (hL.height.justified_preceq_entry C)
      (hL.height.entry_preceq C)) ?_ hc⟩
  · obtain ⟨C, hC, _, hjC, hJC⟩ := hs.pair.1
    exact ⟨C, hC, hjC, hJC⟩
  · obtain ⟨D, hD, _, hjD, hJD⟩ := hd.pair.1
    exact ⟨D, hD, hjD, hJD⟩
  · intro C _ D _ hh hC hD
    exact store_entries_eq E v f hL hJ hh hC hD

end AvailableChain.KitFG
end
