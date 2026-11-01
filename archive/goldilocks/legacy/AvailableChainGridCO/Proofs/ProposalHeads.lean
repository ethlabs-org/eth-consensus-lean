module
public import AvailableChainGridCO.Proofs.ProposerTransfer

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- An ordinary parent and roots below that parent after release suffice
for honest proposal adoption. The engine supplies delivery, all paths,
merged views, score equality, and current-slot proposal uniqueness.
These are proof invariants, not additional contract regime premises. -/
theorem honest_proposal_heads_of_ordinary_parent {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (hroot : RootInjective E (gridInterface p) rho)
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (hparent : B.parent = ordinaryProposalHead (proposalState p rho (r + 1)) (r + 1))
    (hroots : ∀ reader ∈ rho.honest,
      Block.Preceq (liveRoot (nextHeadState p rho r reader)) B.parent) :
    ∀ reader ∈ rho.honest, Block.Preceq B (nextHead p (nextHeadState p rho r reader) r) := by
  have hs := hsync.1.toScheduleWellFormed
  have hshape := honest_proposal_views p E rho hs (r + 1) B hB
  have hslot := (honest_proposal_contains_source_root p E rho hs (r + 1) B hB).1
  intro reader hr
  have hstored := honest_proposal_stored_at_head p E rho hΔ r (.of_synchronous hsync) B hB reader hr
  have hreaderBlocks := congrArg Prod.fst
    (clock_receiptData p (releaseInput p rho r reader) (releaseTime p r))
  change (nextHeadState p rho r reader).blocks =
    (releaseInput p rho r reader).blocks at hreaderBlocks
  have hreaderRoot : RootInjectiveBelow (nextHeadState p rho r reader).blocks := by
    rw [hreaderBlocks]
    exact time_input_rootInjectiveBelow p E rho hs hroot _ reader
  have hsourceClosed : StoredPrefixClosed (proposalState p rho (r + 1)) :=
    clock_stored_prefix_closed p _ _ (run_time_stored_prefix_closed p rho _ _)
  have hreaderClosed : StoredPrefixClosed (nextHeadState p rho r reader) :=
    clock_stored_prefix_closed p _ _ (run_time_stored_prefix_closed p rho _ _)
  apply forkChoice_adopts_stored_proposal p (proposalState p rho (r + 1))
    (nextHeadState p rho r reader) (r + 1) B B.parent _ _ _ hstored.2 rfl hstored.1 hslot
    (proposalState_rootInjectiveBelow p E rho hs hroot (r + 1)) hreaderRoot
    hsourceClosed hreaderClosed
  · exact hparent.symm
  · exact hroots reader hr
  · rw [hshape.2.1]; rfl
  · exact proposalViewTransport_from_engine p E rho hΔ r hsync hready B hB reader hr

end AvailableChain.GridCO
end
