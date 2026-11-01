module
public import AvailableChainKitFG.CertificateSimplex -- shake: keep (axioms)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.CertificateSimplex

open AvailableChain.SimplexFG

private def csFinalRow (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .empty, some ⟨1, genesisRoot⟩⟩

private def csFinalBlock : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [csFinalRow 0, csFinalRow 1, csFinalRow 2]

private def csBirthRow (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote 1 genesisRoot false, some ⟨1, genesisRoot⟩⟩

private def csBirthBlock : FGBlock (Fin 4) :=
  .node .genesis 1 ⟨101⟩ 0 [csBirthRow 0, csBirthRow 1, csBirthRow 2]

private def csBothRow (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩

private def csBothBlock : FGBlock (Fin 4) :=
  .node B1 2 ⟨102⟩ 0 [csBothRow 0, csBothRow 1, csBothRow 2]

-- Genesis at height 1 is a different key from the initial anchor at height 0.
theorem simplex_certificate_genesis_key_test :
    (derive E4 cfg1 B1).J = .genesis ∧ (derive E4 cfg1 B1).h_j = 1 ∧
    (derive E4 cfg1 B1).h_F = 0 := by decide

-- Rows in the birth block cannot set bits for its new entry.
example : ((simplexSelectionView E4 cfg1).chosen csBirthBlock).isNone = true ∧
    (derive E4 cfg1 csBirthBlock).h_j = 1 ∧
    (derive E4 cfg1 csBirthBlock).finalize = ∅ := by decide

-- The selected QC is in before. Pruning removes it.
example : ((simplexSelectionView E4 cfg1).before csFinalBlock).map (fun e => e.Q) =
    [{0, 1, 2}] ∧
    ((simplexSelectionView E4 cfg1).chosen csFinalBlock).map (fun e => (e.j, e.X, e.Q)) =
      some (1, .genesis, {0, 1, 2}) ∧
    ((simplexSelectionView E4 cfg1).afterPrune csFinalBlock).length = 0 := by decide

-- A target write clears post-state bits. The selected QC still comes from before.
example : ((simplexSelectionView E4 cfg1).chosen csBothBlock).map (fun e => e.Q) =
    some {0, 1, 2} ∧ (derive E4 cfg1 csBothBlock).finalize = ∅ ∧
    (derive E4 cfg1 csBothBlock).h_F = 1 ∧ (derive E4 cfg1 csBothBlock).h_j = 2 := by decide

-- The birth block is strictly before every row of the finality QC.
example : ∃ C D, StrictPrefix C D ∧ FGBlock.Preceq D csFinalBlock ∧
    JustificationBirth E4 (simplexHeightView E4 cfg1) C 1 .genesis ∧
    FinalityQCAfter E4 C D 1 .genesis := by
  obtain ⟨C, D, hCD, hD, hb, _, _, hw⟩ :=
    (simplexCertificateLaws E4 cfg1).finality_origin csFinalBlock (by decide)
  exact ⟨C, D, hCD, hD, hb, hw⟩

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- Coverage for a lower pruned entry has no quorum premise for that entry.
example (E : Electorate V) (H : FGHeightView V) (f : FGFinalityView V)
    (r : FGSelectionView V) (hc : FGChainCertificate E H f r)
    (B X : FGBlock V) (j : Height)
    (he : (⟨j, X, ∅⟩ : FGCertEntry V) ∈ r.before B) (hle : j ≤ (f B).h_F) :
    FGBlock.Preceq X (f B).F ∧ j ≤ (f B).h_F :=
  ⟨hc.selection.pruned_covered B _ he hle, hle⟩

-- Deletion alone gives no coverage: a raw pending pair can lie above finality.
example : let X : FGBlock (Fin 4) := .node .genesis 1 ⟨103⟩ 0 []
    let σ : ChainState (Fin 4) := { ChainState.initial with h_j := 2, J := X }
    (simplexPending σ).length = 1 ∧ ¬ FGBlock.Preceq X σ.F ∧ ¬ (2 ≤ σ.h_F) := by decide

#print axioms simplex_certificate_genesis_key_test
#print axioms simplexPending_def
#print axioms simplexSelectionView_def
#print axioms simplex_finalized_mono
#print axioms simplex_justification_birth_interval
#print axioms simplex_prefinal_entry_origin
#print axioms simplex_finality_origin
#print axioms simplexCertificateLaws
#print axioms simplexSelectionLaws
#print axioms simplexChainCertificate

end AvailableChain.KitFG.Tests.CertificateSimplex
end
