module
public import AvailableChainKitFG.HeightFold

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.HeightFold

open AvailableChain.SimplexFG

set_option maxRecDepth 4096

-- The last row has no height effect, but it remains part of the block.
def inertRow : Row (Fin 4) := ⟨3, .empty, some ⟨1, genesisRoot⟩⟩
def fullBlock : FGBlock (Fin 4) :=
  .node .genesis 1 ⟨100⟩ 0 [rowT 0, rowT 1, rowT 2, inertRow]
def rebuiltBlock : FGBlock (Fin 4) :=
  .node .genesis 1 ⟨101⟩ 0 [rowT 0, rowT 1, rowT 2]

/-- Filtering fold input preserves the complete height projection. -/
theorem heightFold_same_geometry :
    heightOf (transition E4 cfg1 .initial fullBlock
      (selectHeightRows .initial fullBlock.rows)) =
    heightOf (transition E4 cfg1 .initial fullBlock fullBlock.rows) :=
  transition_height_eq_of_rowsEq E4 cfg1 rfl fullBlock _ _
    (heightSelector_selectHeightRows _ _)

-- Both folds advance, and both use the original block as the new entry.
example : (transition E4 cfg1 .initial fullBlock fullBlock.rows).h = 2 ∧
    (transition E4 cfg1 .initial fullBlock fullBlock.rows).T_h = fullBlock ∧
    (transition E4 cfg1 .initial fullBlock
      (selectHeightRows .initial fullBlock.rows)).T_h = fullBlock := by
  decide +kernel

/-- Removing a row from the block changes its root. -/
theorem heightFold_rebuilt_root_ne : fullBlock.root ≠ rebuiltBlock.root := by decide +kernel

-- The forbidden rebuild also changes the new entry block.
example : (derive E4 cfg1 fullBlock).T_h ≠ (derive E4 cfg1 rebuiltBlock).T_h := by
  have hfull : (derive E4 cfg1 fullBlock).T_h = fullBlock := by decide +kernel
  have hrebuilt : (derive E4 cfg1 rebuiltBlock).T_h = rebuiltBlock := by decide +kernel
  rw [hfull, hrebuilt]
  exact fun h => heightFold_rebuilt_root_ne (congrArg FGBlock.root h)

-- Duplicate rows and order do not change signer coverage.
example : heightOf (transition E4 cfg1 .initial fullBlock
    [rowT 2, rowT 0, rowT 2, rowT 1]) =
    heightOf (transition E4 cfg1 .initial fullBlock [rowT 0, rowT 1, rowT 2]) := by
  apply transition_height_eq_of_rowsEq E4 cfg1 rfl
  unfold HeightRowsEq heightOf
  decide +kernel

-- A matching row can be removed when both bits are already stored.
def storedState : ChainState (Fin 4) :=
  { ChainState.initial with target_participation := {0}, progress := {0} }

example : HeightRowsEq (heightOf storedState) [rowT 0, rowT 1] [rowT 1] := by
  unfold HeightRowsEq heightOf
  decide +kernel

example : heightOf (transition E4 cfg1 storedState fullBlock [rowT 0, rowT 1, rowT 2]) =
    heightOf (transition E4 cfg1 storedState fullBlock [rowT 1, rowT 2]) := by
  apply transition_height_eq_of_rowsEq E4 cfg1 rfl
  unfold HeightRowsEq heightOf
  decide +kernel

-- Row input and stored coverage together reach a target quorum.
example : (transition E4 ⟨10⟩ storedState fullBlock [rowT 1, rowT 2]).h = 2 ∧
    (transition E4 ⟨10⟩ storedState fullBlock [rowT 1, rowT 2]).h_j = 1 := by
  decide +kernel

-- Different finality fields can enable different finality writes.
def readyState : ChainState (Fin 4) :=
  { ChainState.initial with h_j := 1, finalize := {0, 1, 2} }
def otherFinality : ChainState (Fin 4) :=
  { readyState with finalize := ∅, F := fullBlock, h_F := 7 }

/-- The projection is independent of all three omitted finality fields. -/
theorem heightFold_finality_independent :
    heightOf (transition E4 cfg1 readyState fullBlock []) =
      heightOf (transition E4 cfg1 otherFinality fullBlock []) :=
  transition_height_eq_of_rowsEq E4 cfg1 rfl fullBlock [] [] (heightSelector_id _ _)

example : (transition E4 cfg1 readyState fullBlock []).h_F = 1 ∧
    (transition E4 cfg1 otherFinality fullBlock []).h_F = 7 := by decide +kernel

-- A stale row cannot supply the current-height matching premise.
example : (rowT 0).height_pair.matchesEntry (derive E4 cfg1 fullBlock).h
    (derive E4 cfg1 fullBlock).T_h.root = false := by decide +kernel

#print axioms heightSelector_id
#print axioms heightSelector_selectHeightRows
#print axioms process_row_height_congr
#print axioms foldRows_height_eq_of_rowsEq
#print axioms process_height_events_height_congr
#print axioms transition_height_eq_of_rowsEq
#print axioms deriveWithSelector_id
#print axioms deriveWithSelector_height
#print axioms heightFold_same_geometry
#print axioms heightFold_rebuilt_root_ne
#print axioms heightFold_finality_independent

end AvailableChain.KitFG.Tests.HeightFold
end
