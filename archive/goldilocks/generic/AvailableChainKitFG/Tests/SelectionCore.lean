module
public import AvailableChainKitFG.SelectionCore
public import AvailableChainKitFG.CertificateSimplex

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.SelectionCore

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- Build the instance without supplying its coverage field.
theorem selection_simplex_core_constructor_test (E : Electorate V) (cfg : FGConfig) :
    FGSelectionLaws E (simplexHeightView E cfg) (simplexFinalityView E cfg)
      (simplexSelectionView E cfg) :=
  FGSelectionLaws.of_core E _ _ _
    (simplexSelectionLaws E cfg).initial (simplexSelectionLaws E cfg).ordered
    (simplexSelectionLaws E cfg).bounds (simplexSelectionLaws E cfg).entry_origin
    (simplexSelectionLaws E cfg).none_iff (simplexSelectionLaws E cfg).greatest
    (simplexSelectionLaws E cfg).write (simplexSelectionLaws E cfg).prune

-- The generic constructor works on the existing instance, with explicit bounds.
theorem selection_simplex_constructor_test (E : Electorate V) (cfg : FGConfig) :
    FGCertificateLaws E (simplexHeightView E cfg) (simplexFinalityView E cfg) :=
  FGCertificateLaws.of_selection E _ _ _ (selection_simplex_core_constructor_test E cfg)
    (simplexHeightLaws E cfg) rfl (justified_zero_is_genesis E cfg)
    (derive_F_preceq_J E cfg) (heights_ordered E cfg)

private def scFinalOne : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

-- Read the instance's pruning result through the named library equation.
private theorem selection_simplex_afterPrune_test :
    ((simplexSelectionView E4 cfg1).afterPrune scFinalOne).length = 0 := by
  rw [FGSelectionLaws.prune_eq E4 _ _ _
    (selection_simplex_core_constructor_test E4 cfg1) scFinalOne]
  simp only [pruneCertEntries_def]
  decide

-- Use the generic historical induction after the selected entry has been pruned.
private theorem selection_historical_origin_test :
    ∃ C D, StrictPrefix C D ∧ FGBlock.Preceq D scFinalOne ∧
      JustificationBirth E4 (simplexHeightView E4 cfg1) C 1 .genesis ∧
      FinalityQCAfter E4 C D 1 .genesis := by
  obtain ⟨C, D, hCD, hD, hb, _, _, hqc⟩ :=
    (selection_simplex_constructor_test E4 cfg1).finality_origin scFinalOne (by decide)
  exact ⟨C, D, hCD, hD, hb, hqc⟩

private def scLowBlock : FGBlock (Fin 4) := .node .genesis 1 ⟨101⟩ 0 []
private def scHighBlock : FGBlock (Fin 4) := .node scLowBlock 2 ⟨102⟩ 0 []
private def scLow : FGCertEntry (Fin 4) := ⟨2, scLowBlock, ∅⟩
private def scHigh : FGCertEntry (Fin 4) := ⟨3, scHighBlock, {0, 1, 2}⟩

-- The lower entry has no QC. The ordered higher target covers it after pruning.
private theorem selection_pruned_without_qc_test :
    (pruneCertEntries 3 [scLow, scHigh]).length = 0 ∧
      ¬ E4.IsQuorum scLow.Q ∧ E4.IsQuorum scHigh.Q ∧
      scLow.j ≤ scHigh.j ∧ FGBlock.Preceq scLow.X scHigh.X := by
  refine ⟨by simp only [pruneCertEntries_def]; decide, ?_, ?_, by decide, ?_⟩
  · change ¬ (3 ≤ 0)
    decide
  · change 3 ≤ 3
    decide
  · exact certEntry_preceq_of_le [scLow, scHigh] (by decide)
      scLow scHigh (by simp) (by simp) (by decide)

-- Pruning retains an entry above F. A later capacity drop gives no coverage.
private theorem selection_eviction_no_coverage_test :
    let kept := pruneCertEntries 1 [scLow, scHigh]
    kept.length = 2 ∧ (kept.drop 1).length = 1 ∧
      (kept.drop 1).map FGCertEntry.j = [3] ∧
      ¬ FGBlock.Preceq scLow.X .genesis ∧ ¬ scLow.j ≤ 1 := by
  simp only [pruneCertEntries_def]
  decide

-- The core constructor supplies coverage from the other selection fields.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hs : FGSelectionLaws E H f r)
    (B : FGBlock V) (X : FGBlock V) (j : Height)
    (he : (⟨j, X, ∅⟩ : FGCertEntry V) ∈ r.before B) (hle : j ≤ (f B).h_F) :
    FGBlock.Preceq X (f B).F :=
  (FGSelectionLaws.of_core E H f r hs.initial hs.ordered hs.bounds hs.entry_origin
    hs.none_iff hs.greatest hs.write hs.prune).pruned_covered B _ he hle

#print axioms selection_simplex_core_constructor_test
#print axioms selection_simplex_constructor_test
#print axioms selection_simplex_afterPrune_test
#print axioms selection_historical_origin_test
#print axioms selection_pruned_without_qc_test
#print axioms selection_eviction_no_coverage_test
#print axioms pruneCertEntries_def
#print axioms mem_pruneCertEntries
#print axioms certEntry_preceq_of_le
#print axioms FGSelectionLaws.of_core
#print axioms FGSelectionLaws.prune_eq
#print axioms selection_chosen_spec
#print axioms selection_ready_covered
#print axioms selection_chosen_removed
#print axioms selection_retained_iff
#print axioms selection_removed_covered
#print axioms selection_finalized_zero
#print axioms selection_finalized_mono
#print axioms selection_finality_origin
#print axioms FGCertificateLaws.of_selection

end AvailableChain.KitFG.Tests.SelectionCore
end
