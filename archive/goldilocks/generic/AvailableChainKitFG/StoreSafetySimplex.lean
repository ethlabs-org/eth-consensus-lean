module
public import AvailableChainKitFG.StoreSafety
public import AvailableChainKitFG.CertificateSimplex
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.ProvenanceCoreDef

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- The certificate views give the same head fields as the block adapter. -/
theorem simplex_certificateHeadFields_eq (E : Electorate V) (cfg : FGConfig)
    (Hd : FGBlock V) :
    certificateHeadFields (simplexHeightView E cfg) (simplexFinalityView E cfg) Hd =
      HeadFields.ofBlock E cfg Hd := rfl

/-- Project the existing SimplexFG store invariant into the shared structure. -/
theorem simplexStoreInvariant (E : Electorate V) (cfg : FGConfig) (st : Store V)
    (hi : StoreInv E cfg st) (hinj : ViewRootInj st.TF) :
    FGStoreInvariant (simplexHeightView E cfg) (simplexFinalityView E cfg) st := by
  refine ⟨hi.closed, hi.gen, hi.Fmem, hi.hmax, ?_, hi.FJ, hi.Fcar⟩
  obtain ⟨D, hD, hDF⟩ := hi.Fcar
  have hDJ : FGBlock.Preceq st.F (derive E cfg D).J :=
    hDF ▸ derive_F_preceq_J E cfg D
  obtain ⟨C, hC, hFC, hpair, hmax⟩ :=
    lexMax_spec E cfg st.F st.TF hinj ⟨D, hD, hDJ⟩
  have heq := hi.pair.trans hpair
  refine ⟨⟨C, hC, hFC, congrArg Prod.fst heq, congrArg Prod.snd heq⟩, ?_⟩
  intro B hB hFB
  change lexKey ((derive E cfg B).h_j, (derive E cfg B).J) ≤ lexKey (st.h_j, st.J)
  rw [heq]
  exact hmax B hB hFB

/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] Simplex uses local step roots. -/
theorem simplexStoreSafety (E : Electorate V) (cfg : FGConfig) :
    FGStoreSafety E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (id : Store V → Store V)
      (fun _ B => (simplexHeightView E cfg B, simplexFinalityView E cfg B))
      Store.init (on_block E cfg)
      (fun st => StoreInv E cfg st ∧ ViewRootInj st.TF) StoreStepRoots := by
  apply FGStoreSafety.of_certificate E _ _ (simplexCertificateLaws E cfg)
    id _ Store.init (on_block E cfg)
    (fun st => StoreInv E cfg st ∧ ViewRootInj st.TF) StoreStepRoots
  · refine ⟨storeInv_init E cfg, ?_⟩
    rintro X Y ⟨A, hA, hXA⟩ ⟨B, hB, hYB⟩ _
    have ha : A = .genesis := Finset.mem_singleton.mp hA
    have hb : B = .genesis := Finset.mem_singleton.mp hB
    subst A B
    exact (preceq_genesis.mp hXA).trans (preceq_genesis.mp hYB).symm
  · intro st h
    exact simplexStoreInvariant E cfg st h.1 h.2
  · intro st B h hroots
    refine ⟨storeInv_on_block E cfg st B h.1 (fun _ => hroots), ?_⟩
    apply viewRootInj_mono hroots
    unfold on_block
    split_ifs
    · exact Finset.subset_insert B st.TF
    · rw [update_finality_TF]
  · intro st B _
    exact on_block_TF_subset E cfg st B
  · intro st B _
    exact on_block_F_mono E cfg st B
  · intros
    rfl

end AvailableChain.KitFG
end
