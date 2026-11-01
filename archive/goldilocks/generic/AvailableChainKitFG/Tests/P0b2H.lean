module
public import AvailableChainKitFG.WindowInvariant

set_option linter.privateModule false

namespace AvailableChain.KitFG.Tests.P0b2H

open AvailableChain.SimplexFG hiding derive process_row
open AvailableChain.SimplexFG.Window

private def E : Electorate (Fin 2) :=
  ⟨fun i => if i = 0 then 3 else 1, fun i => by split <;> decide⟩
private def cfg : FGConfig := ⟨0⟩
private def B1 : FGBlock (Fin 2) :=
  .node .genesis 1 ⟨10⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def B2 : FGBlock (Fin 2) :=
  .node B1 2 ⟨11⟩ 0 [⟨0, .vote 2 B1.root false, none⟩]
private def B3 : FGBlock (Fin 2) :=
  .node B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]

private theorem nonempty_quorum : ¬ E.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

/-- An actual block fold retains two entries before a non-genesis finalization. -/
private theorem inhabited_window :
    (derive E cfg 2 B2).W = [⟨1, .genesis, ∅⟩, ⟨2, B1, ∅⟩] ∧
    (derive E cfg 2 B3).W = [⟨3, B2, ∅⟩] ∧
    (derive E cfg 2 B3).F = B1 ∧ (derive E cfg 2 B3).h_F = 2 ∧
    (derive E cfg 2 B3).h = 4 := by
  decide +kernel

/-- The cover theorem applies to a real retained entry and a weighted quorum. -/
private theorem inhabited_cover :
    FGBlock.Preceq B1 (derive E cfg 2 B3).F ∧ 2 ≤ (derive E cfg 2 B3).h_F := by
  exact Window.window_finality_of_cover E cfg 2 nonempty_quorum (by decide)
    B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]
    ⟨2, B1, ∅⟩ (by decide +kernel) {0} (by unfold Electorate.IsQuorum; decide +kernel) (by
      intro i hi
      have hi' : i = 0 := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨_, List.mem_singleton_self _, rfl, rfl⟩)

/-- Empty electorates violate the premise needed for the post-finality invariant. -/
private theorem empty_quorum_control :
    let E0 : Electorate (Fin 0) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩
    let B : FGBlock (Fin 0) := .node .genesis 1 ⟨1⟩ 0 []
    E0.IsQuorum ∅ ∧ ∃ e ∈ (derive E0 cfg 2 B).W, E0.IsQuorum e.Q := by
  dsimp only
  refine ⟨?_, ⟨⟨1, .genesis, ∅⟩, ?_, ?_⟩⟩
  · change 0 ≤ 0
    decide
  · decide +kernel
  · change 0 ≤ 0
    decide

/-- All four refinement fields are supplied, including the arbitrary-state step. -/
private theorem p0b2h_generic_complete_refinement :
    HeightFoldRefinement E cfg Window.projectHeight initial
      (transition E cfg 2) (derive E cfg 2) where
  initial_height := (Window.heightRefinement E cfg 2 (by decide)).initial_height
  derive_genesis := (Window.heightRefinement E cfg 2 (by decide)).derive_genesis
  derive_node := (Window.heightRefinement E cfg 2 (by decide)).derive_node
  step_height := (Window.heightRefinement E cfg 2 (by decide)).step_height

/-- Reconstruct the complete existing record, including both row origins and certificates. -/
private theorem p0b2h_generic_complete_height :
    FGHeightLaws E (fun B => Window.projectHeight (derive E cfg 2 B)) where
  one_le_h := (Window.windowHeightLaws E cfg 2 (by decide)).one_le_h
  h_mono := (Window.windowHeightLaws E cfg 2 (by decide)).h_mono
  node_cases := (Window.windowHeightLaws E cfg 2 (by decide)).node_cases
  entry_preceq := (Window.windowHeightLaws E cfg 2 (by decide)).entry_preceq
  entry_same_height := (Window.windowHeightLaws E cfg 2 (by decide)).entry_same_height
  entry_idem := (Window.windowHeightLaws E cfg 2 (by decide)).entry_idem
  entry_plateau := (Window.windowHeightLaws E cfg 2 (by decide)).entry_plateau
  justified_preceq_entry := (Window.windowHeightLaws E cfg 2 (by decide)).justified_preceq_entry
  justified_below_height := (Window.windowHeightLaws E cfg 2 (by decide)).justified_below_height
  target_sub_progress := (Window.windowHeightLaws E cfg 2 (by decide)).target_sub_progress
  target_origin := (Window.windowHeightLaws E cfg 2 (by decide)).target_origin
  progress_origin := (Window.windowHeightLaws E cfg 2 (by decide)).progress_origin
  height_crossing := (Window.windowHeightLaws E cfg 2 (by decide)).height_crossing
  justification_certificate :=
    (Window.windowHeightLaws E cfg 2 (by decide)).justification_certificate

#print axioms nonempty_quorum
#print axioms inhabited_window
#print axioms inhabited_cover
#print axioms empty_quorum_control
#print axioms p0b2h_generic_complete_refinement
#print axioms p0b2h_generic_complete_height

end AvailableChain.KitFG.Tests.P0b2H
