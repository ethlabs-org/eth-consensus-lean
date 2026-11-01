module
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainKitFG.FrameSelection
public import AvailableChainKitFG.Certificates -- shake: keep (re-export)
public import AvailableChainKitFG.JustificationLawsDef

public section

namespace AvailableChain.KitFG
open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

omit [Fintype V] in
/-- Every stored block's height is at most the store frontier. -/
theorem store_height_le (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hs : FGStoreInvariant H f st) {W : FGBlock V} (hW : W ∈ st.TF) :
    (H W).h ≤ st.h_max := by
  rw [hs.hmax]
  exact (Finset.le_sup (f := fun B => (H B).h) hW).trans (Nat.le_max_left _ _)

/-- The store's justified height is below its frontier. -/
theorem store_justified_lt (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (st : Store V) (hs : FGStoreInvariant H f st) :
    st.h_j < st.h_max := by
  obtain ⟨K, hK, _, hj, _⟩ := hs.pair.1
  rw [hj]
  exact (hc.height.justified_below_height K).trans_le (store_height_le H f st hs hK)

/-- An accepted certificate's finalized height is at most the store's justified height. -/
theorem store_finality_le (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (st : Store V) (hs : FGStoreInvariant H f st)
    {K : FGBlock V} (hK : K ∈ st.TF) (hF : (f K).F = st.F) : (f K).h_F ≤ st.h_j := by
  have hp := hs.pair.2 K hK (hF ▸ hc.finalized_preceq_justified K)
  exact (hc.heights_ordered K).trans (fst_le_of_lexKey_le hp)

/-- A nonempty cumulative store attains its frontier. -/
theorem store_frontier_witness (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (st : Store V) (hs : FGStoreInvariant H f st) :
    ∃ W ∈ st.TF, (H W).h = st.h_max := by
  obtain ⟨W, hW, hw⟩ := Finset.exists_mem_eq_sup _ ⟨_, hs.gen⟩ (fun W => (H W).h)
  refine ⟨W, hW, ?_⟩
  rw [hs.hmax, hw, max_eq_left (hc.height.one_le_h W)]

/-- Equal-height entries on one path are equal, including height zero. -/
theorem store_entries_eq (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (hc : FGCertificateLaws E H f) (hj : FGJustificationLaws H) {C D W : FGBlock V}
    (hh : (H C).h_j = (H D).h_j) (hC : FGBlock.Preceq (H C).J W)
    (hD : FGBlock.Preceq (H D).J W) : (H C).J = (H D).J := by
  by_cases hn : (H C).h_j = 0
  · rw [hj.J_zero C hn, hj.J_zero D (hh ▸ hn)]
  have he : (H (H C).J).h = (H (H D).J).h := by
    rw [hj.J_height C hn, hj.J_height D (hh ▸ hn), hh]
  rcases preceq_total_of_common hC hD with h | h
  · simpa only [hj.J_entry] using hc.height.entry_plateau h he
  · simpa only [hj.J_entry] using (hc.height.entry_plateau h he.symm).symm

end AvailableChain.KitFG
end
