module
public import AvailableChainKitFG.HeightConsumeTransfer
public import AvailableChainKitFG.HeightBridge

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.HeightConsumeTransfer

open AvailableChain.SimplexFG

set_option maxRecDepth 4096

def consumeView (cfg : FGConfig) : FGHeightView (Fin 4) :=
  fun B => heightOf (deriveWithSelector E4 cfg selectHeightRows B)

/-- The selected evaluator supplies the derive bridge used in these tests. -/
theorem heightConsumeTransfer_view_bridge (cfg : FGConfig) :
    HeightBridge E4 cfg (consumeView cfg) :=
  deriveWithSelector_height E4 cfg selectHeightRows heightSelector_selectHeightRows

-- The one-step tests use a state type with an extra field.
def consumeProject (w : ChainState (Fin 4) × Unit) : FGHeight (Fin 4) := heightOf w.1

def consumeStep (cfg : FGConfig) (w : ChainState (Fin 4) × Unit)
    (B : FGBlock (Fin 4)) (rs : List (Row (Fin 4))) : ChainState (Fin 4) × Unit :=
  (transition E4 cfg w.1 B rs, ())

/-- No recursive evaluator is needed for the one-step bridge. -/
theorem heightConsumeTransfer_step_bridge (cfg : FGConfig) :
    HeightStepBridge E4 cfg consumeProject (consumeStep cfg) := by
  intro w σ B rs heq
  exact (simplexHeightRefinement E4 cfg).step_height w.1 σ B rs heq

-- Both target and progress are ready. The target branch writes justification.
theorem heightConsumeTransfer_target_priority :
    (consumeView cfg0 B1).h = 2 ∧
    (consumeView cfg0 B1).J = .genesis ∧
    (consumeView cfg0 B1).h_j = 1 := by
  exact derive_target_of_cover_of_bridge E4 cfg0 _ (heightConsumeTransfer_view_bridge _)
    .genesis 1 ⟨1⟩ 0 [rowT 0, rowT 1, rowT 2] {0, 1, 2}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

def consumeCarrier : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 [rowX 0, rowX 1, rowX 2]
def consumeTail : FGBlock (Fin 4) := .node consumeCarrier 2 ⟨101⟩ 0 []

def consumeParent : FGBlock (Fin 4) := .node .genesis 0 ⟨102⟩ 0 [rowT 0, rowT 1]
def consumeTargetChild : FGBlock (Fin 4) := .node consumeParent 1 ⟨103⟩ 0 [rowT 2]
def consumeProgressChild : FGBlock (Fin 4) := .node consumeParent 5 ⟨104⟩ 0 [rowX 2]

-- Two target bits in the parent combine with one new row before maturity.
theorem heightConsumeTransfer_parent_target :
    (consumeView ⟨5⟩ consumeTargetChild).h = 2 ∧
    (consumeView ⟨5⟩ consumeTargetChild).J = .genesis ∧
    (consumeView ⟨5⟩ consumeTargetChild).h_j = 1 := by
  exact derive_target_of_cover_of_bridge E4 ⟨5⟩ _ (heightConsumeTransfer_view_bridge _)
    consumeParent 1 ⟨103⟩ 0 [rowT 2] {0, 1, 2}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

-- Two parent bits and one timeout row cross at the maturity boundary.
theorem heightConsumeTransfer_parent_progress :
    (consumeView ⟨5⟩ consumeProgressChild).h = 2 ∧
    (consumeView ⟨5⟩ consumeProgressChild).h_j = 0 := by
  constructor
  · exact derive_progress_of_cover_of_bridge E4 ⟨5⟩ _ (heightConsumeTransfer_view_bridge _)
      consumeParent 5 ⟨104⟩ 0 [rowX 2] {0, 1, 2}
      (by unfold Electorate.IsQuorum; decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

-- The finality fields need no invariant for a height transfer.
def consumeStored : ChainState (Fin 4) :=
  { ChainState.initial with
    target_participation := {0, 1}
    progress := {0, 1}
    F := B1
    h_F := 7
    finalize := {3} }

theorem heightConsumeTransfer_step_target :
    (consumeProject (consumeStep ⟨5⟩ (consumeStored, ()) .genesis [rowT 2])).h = 2 ∧
    (consumeProject (consumeStep ⟨5⟩ (consumeStored, ()) .genesis [rowT 2])).J = .genesis ∧
    (consumeProject (consumeStep ⟨5⟩ (consumeStored, ()) .genesis [rowT 2])).h_j = 1 := by
  exact transition_target_of_cover_of_bridge E4 ⟨5⟩ _ _
    (heightConsumeTransfer_step_bridge _) (consumeStored, ()) .genesis [rowT 2] {0, 1, 2}
    (by unfold Electorate.IsQuorum; decide +kernel) (by decide +kernel)

theorem heightConsumeTransfer_step_progress :
    (consumeProject (consumeStep ⟨5⟩ (consumeStored, ()) consumeProgressChild [rowX 2])).h =
      2 := by
  exact transition_progress_of_cover_of_bridge E4 ⟨5⟩ _ _
    (heightConsumeTransfer_step_bridge _) (consumeStored, ()) consumeProgressChild
    [rowX 2] {0, 1, 2} (by unfold Electorate.IsQuorum; decide +kernel)
    (by decide +kernel) (by decide +kernel)

-- Delay zero permits a timeout crossing at the entry slot.
theorem heightConsumeTransfer_zero_delay :
    (consumeView cfg0 (.node .genesis 0 ⟨105⟩ 0 [rowX 0, rowX 1, rowX 2])).h = 2 ∧
    (consumeView cfg0 (.node .genesis 0 ⟨105⟩ 0 [rowX 0, rowX 1, rowX 2])).h_j = 0 := by
  constructor
  · exact derive_progress_of_cover_of_bridge E4 cfg0 _ (heightConsumeTransfer_view_bridge _)
      .genesis 0 ⟨102⟩ 0 [rowX 0, rowX 1, rowX 2] {0, 1, 2}
      (by unfold Electorate.IsQuorum; decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · decide +kernel

-- Equal heights keep a carrier progress bit in a later block.
theorem heightConsumeTransfer_progress_persist :
    (consumeView ⟨5⟩ consumeCarrier).progress ⊆ (consumeView ⟨5⟩ consumeTail).progress := by
  exact progress_persist_of_bridge E4 ⟨5⟩ _ (heightConsumeTransfer_view_bridge _)
    (preceq_parent_node consumeCarrier 2 ⟨101⟩ 0 []) (by decide +kernel)

-- A matching timeout row keeps its signer bit through the later block.
theorem heightConsumeTransfer_progress_from_row :
    (1 : Fin 4) ∈ (consumeView ⟨5⟩ consumeTail).progress := by
  exact progress_from_row_of_bridge E4 ⟨5⟩ _ (heightConsumeTransfer_view_bridge _)
    (P := .genesis) (rs := [rowX 0, rowX 1, rowX 2]) (a := rowX 1)
    (by decide +kernel) (preceq_parent_node consumeCarrier 2 ⟨101⟩ 0 [])
    (by decide +kernel) (by decide +kernel)

#print axioms transition_target_of_cover_of_bridge
#print axioms transition_progress_of_cover_of_bridge
#print axioms derive_target_of_cover_of_bridge
#print axioms derive_progress_of_cover_of_bridge
#print axioms heightConsumeTransfer_view_bridge
#print axioms heightConsumeTransfer_step_bridge
#print axioms heightConsumeTransfer_target_priority
#print axioms heightConsumeTransfer_parent_target
#print axioms heightConsumeTransfer_parent_progress
#print axioms heightConsumeTransfer_step_target
#print axioms heightConsumeTransfer_step_progress
#print axioms heightConsumeTransfer_zero_delay
#print axioms progress_persist_of_bridge
#print axioms progress_from_row_of_bridge
#print axioms heightConsumeTransfer_progress_persist
#print axioms heightConsumeTransfer_progress_from_row

end AvailableChain.KitFG.Tests.HeightConsumeTransfer
end
