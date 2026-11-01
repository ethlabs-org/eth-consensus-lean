module
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.HeightHistoryTransfer
public import AvailableChainKitFG.HeightConsumeTransfer
public import AvailableChainKitFG.HeightFold
public import AvailableChainKitFG.HeightLaws
public import AvailableChainKitFG.FrameGeometry

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.HeightHistoryTransfer

open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3: use a closed finite table for both ancestor chains. -/
theorem finite_chain_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y)
    (A B : FGBlock V) (hA : A ∈ T) (hB : B ∈ T) : RootInjectiveOn A B := by
  intro X Y hX hY hr
  have mem : ∀ Z, (FGBlock.Preceq Z A ∨ FGBlock.Preceq Z B) → Z ∈ T := by
    intro Z hZ
    rcases hZ with hZ | hZ
    · exact ancestor_closed_of_parent_closed T hcl A hA Z hZ
    · exact ancestor_closed_of_parent_closed T hcl B hB Z hZ
  exact hinj X (mem X hX) Y (mem Y hY) hr

set_option maxRecDepth 4096

def historyView (cfg : FGConfig) : FGHeightView (Fin 4) :=
  fun B => heightOf (deriveWithSelector E4 cfg selectHeightRows B)

/-- History tests use the selected evaluator on the original block tree. -/
theorem heightHistoryTransfer_view_bridge (cfg : FGConfig) :
    HeightBridge E4 cfg (historyView cfg) :=
  deriveWithSelector_height E4 cfg selectHeightRows heightSelector_selectHeightRows

-- A target crossing before maturity must justify the entry.
theorem heightHistoryTransfer_early_target :
    (historyView ⟨5⟩ B1).J = .genesis ∧ (historyView ⟨5⟩ B1).h_j = 1 := by
  exact no_mixed_cross_before_maturity_of_bridge E4 ⟨5⟩ _
    (heightHistoryTransfer_view_bridge _) 1 (by decide +kernel) (preceq_refl _)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

def historyEarly : FGBlock (Fin 4) := .node .genesis 4 ⟨100⟩ 0 [rowX 0, rowX 1, rowX 2]
def historyBoundary : FGBlock (Fin 4) := .node .genesis 5 ⟨101⟩ 0 [rowX 0, rowX 1, rowX 2]

-- Progress stays at height one before maturity and crosses at equality.
-- At equality, the early-crossing justification conclusion is false.
theorem heightHistoryTransfer_exact_boundary :
    (historyView ⟨5⟩ historyEarly).h = 1 ∧
    (historyView ⟨5⟩ historyBoundary).h = 2 ∧
    (historyView ⟨5⟩ historyBoundary).h_j = 0 ∧
    ¬ (historyView ⟨5⟩ historyBoundary).h_j = 1 ∧
    ¬ historyBoundary.slot < (FGBlock.genesis (V := Fin 4)).slot + 5 := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  exact derive_progress_of_cover_of_bridge E4 ⟨5⟩ _ (heightHistoryTransfer_view_bridge _)
    .genesis 5 ⟨101⟩ 0 [rowX 0, rowX 1, rowX 2] {0, 1, 2}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel) (by decide +kernel)

-- The first crossing interface applies to the view without new induction.
theorem heightHistoryTransfer_first_edge :
    ∃ C : FGBlock (Fin 4), C ≠ .genesis ∧
      FGBlock.Preceq .genesis C.parent ∧ FGBlock.Preceq C historyBoundary ∧
      (historyView ⟨5⟩ C.parent).h = 1 ∧ (historyView ⟨5⟩ C).h = 2 := by
  exact first_height_crossing_edge_of_bridge E4 ⟨5⟩ _ (heightHistoryTransfer_view_bridge _)
    1 (genesis_preceq _) (by decide +kernel) (by decide +kernel)

def historyTimeoutCarrier : FGBlock (Fin 4) :=
  .node .genesis 1 ⟨102⟩ 0 [rowX 0, rowX 1, rowX 2]
def historyRetainedCrossing : FGBlock (Fin 4) := .node historyTimeoutCarrier 5 ⟨103⟩ 0 []

-- A crossing with no new rows still has an honest row in a strict ancestor.
theorem heightHistoryTransfer_honest_ancestor :
    ∃ (W : FGBlock (Fin 4)) (a : Row (Fin 4)),
      FGBlock.Preceq W historyRetainedCrossing ∧ a ∈ W.rows ∧ a.signer ∉ ({3} : Finset _) ∧
      a.height_pair.matchesEntry 1
        (historyView ⟨5⟩ historyRetainedCrossing.parent).T_h.root = true ∧
      W ≠ historyRetainedCrossing := by
  obtain ⟨W, a, hW, ha, hhonest, hmatch⟩ := crossing_honest_matching_row_of_bridge E4 ⟨5⟩ _
    (heightHistoryTransfer_view_bridge _) {3} (C := historyRetainedCrossing) 1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨W, a, hW, ha, hhonest, hmatch, ?_⟩
  intro heq
  subst W
  simp only [historyRetainedCrossing, FGBlock.rows, List.not_mem_nil] at ha

def historyCarrier : FGBlock (Fin 4) := .node .genesis 1 ⟨104⟩ 0 [rowX 0]
def historyTail : FGBlock (Fin 4) := .node historyCarrier 2 ⟨105⟩ 0 []

-- A nonempty plateau keeps the latest justification.
theorem heightHistoryTransfer_plateau :
    (historyView ⟨5⟩ historyTail).J = (historyView ⟨5⟩ historyCarrier).J ∧
    (historyView ⟨5⟩ historyTail).h_j = (historyView ⟨5⟩ historyCarrier).h_j := by
  exact justification_eq_on_plateau_of_bridge E4 ⟨5⟩ _ (heightHistoryTransfer_view_bridge _)
    (preceq_parent_node historyCarrier 2 ⟨105⟩ 0 []) (by decide +kernel)

-- A matching occurrence keeps its parent's keys through the endpoint.
theorem heightHistoryTransfer_occurrence :
    FGBlock.Preceq .genesis historyCarrier.parent ∧
    (historyView ⟨5⟩ historyCarrier.parent).h = (historyView ⟨5⟩ historyTail).h ∧
    (historyView ⟨5⟩ historyCarrier.parent).T_h.root =
      (historyView ⟨5⟩ historyTail).T_h.root := by
  exact height_occurrence_keys_of_bridge E4 ⟨5⟩ _ (heightHistoryTransfer_view_bridge _)
    (u := rowX 0) (y := 1) (χ := true)
    (finite_chain_roots {.genesis, historyCarrier, historyTail}
      (by decide +kernel) (by decide +kernel) _ _ (by decide +kernel) (by decide +kernel))
    (List.mem_singleton_self _)
    (preceq_parent_node historyCarrier 2 ⟨105⟩ 0 []) rfl rfl
    (by decide +kernel) (by decide +kernel)

def historyStaleCarrier : FGBlock (Fin 4) := .node B1 2 ⟨106⟩ 0 [rowT 0]

-- The stale row occurs, but it has a lower height and sets neither height bit.
-- Thus it cannot supply heightMatch for height_occurrence_keys_of_bridge.
theorem heightHistoryTransfer_stale_not_witness :
    rowT 0 ∈ historyStaleCarrier.rows ∧
    1 < (historyView cfg1 historyStaleCarrier.parent).h ∧
    (historyView cfg1 historyStaleCarrier).target_participation = ∅ ∧
    (historyView cfg1 historyStaleCarrier).progress = ∅ ∧
    ¬ ∃ χ, (rowT 0).height_pair =
      .vote (historyView cfg1 historyStaleCarrier.parent).h
        (historyView cfg1 historyStaleCarrier.parent).T_h.root χ := by
  refine ⟨List.mem_singleton_self _, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  rintro ⟨χ, hmatch⟩
  have hh := (NamedHeightPair.vote.inj hmatch).1
  have hparent : (historyView cfg1 historyStaleCarrier.parent).h = 2 := by decide +kernel
  rw [hparent] at hh
  change 1 = 2 at hh
  exact (by decide +kernel : (1 : Height) ≠ 2) hh

-- The generic cross cases hold at a concrete first crossing from genesis.
theorem heightHistoryTransfer_cross_cases :
    ((historyView ⟨5⟩ B1.parent).h = 1 ∧ (historyView ⟨5⟩ B1).h = 2 ∧
      (historyView ⟨5⟩ B1).J = .genesis ∧ (historyView ⟨5⟩ B1).h_j = 1) ∨
    ((historyView ⟨5⟩ B1.parent).h = 1 ∧ (historyView ⟨5⟩ B1).h = 2 ∧
      (historyView ⟨5⟩ B1).h_j < 1) := by
  exact cross_cases_of_laws
    (heightLaws_of_bridge E4 ⟨5⟩ _ (heightHistoryTransfer_view_bridge _))
    (FGJustificationLaws.of_bridge (heightHistoryTransfer_view_bridge _))
    (U := .genesis) (y := 1) (by decide +kernel) (genesis_preceq _)
    (by decide +kernel) (by decide +kernel)

#print axioms no_mixed_cross_before_maturity_of_bridge
#print axioms first_height_crossing_edge_of_bridge
#print axioms crossing_honest_matching_row_of_bridge
#print axioms justification_eq_on_plateau_of_bridge
#print axioms height_occurrence_keys_of_bridge
#print axioms heightHistoryTransfer_view_bridge
#print axioms heightHistoryTransfer_early_target
#print axioms heightHistoryTransfer_exact_boundary
#print axioms heightHistoryTransfer_first_edge
#print axioms heightHistoryTransfer_honest_ancestor
#print axioms heightHistoryTransfer_plateau
#print axioms heightHistoryTransfer_occurrence
#print axioms heightHistoryTransfer_stale_not_witness
#print axioms cross_cases_of_laws
#print axioms heightHistoryTransfer_cross_cases

end AvailableChain.KitFG.Tests.HeightHistoryTransfer
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.KitFG.Tests.HeightHistoryTransfer.finite_chain_roots
