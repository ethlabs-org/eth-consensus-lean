module
public import AvailableChainFGSARun.Proofs.TestSupport.EmissionFreshness
public import AvailableChainFGSARun.Proofs.NamedDelivery -- shake: keep (axioms)

#print axioms AvailableChain.FGSA.Run.EmissionFreshnessTests.valid
#print axioms AvailableChain.FGSA.Run.EmissionFreshnessTests.emitted_proposal_already_processed

#print axioms AvailableChain.FGSA.Run.EmissionFreshnessTests.roots

public section

namespace AvailableChain.FGSA.Run.EmissionFreshnessTests

/-- [P23-A] The delivered slot-1 body and emitted slot-2 body collide in receipt scope. -/
theorem receipt_roots_false : ¬ NamedReceiptRootCollisionFree p unitCodec env run := by
  intro hr
  have hfirst : NamedProposalReceiptScope p unitCodec env run
      (namedProposal p .genesis 1 0 [] [] []) :=
    Or.inl (namedScope_delivered env run (x := 0) (o := first) (t := 8)
      (List.mem_of_getElem? (show run.events[5]? = some (.deliver 0 first 8) from rfl)) rfl)
  have hsecond : NamedProposalReceiptScope p unitCodec env run
      (namedProposal p .genesis 2 0 [] [] []) :=
    namedReceiptScope_emitted env run (v := 0) (by decide)
      ⟨9, rfl, emitted_proposal_already_processed.1⟩ rfl (named_preceq_refl _)
  have he := hr _ _ hfirst hsecond (by rfl)
  exact (by decide : (namedProposal p .genesis 1 0 [] [] []) ≠
    namedProposal p .genesis 2 0 [] [] []) he

end AvailableChain.FGSA.Run.EmissionFreshnessTests
end

#print axioms AvailableChain.FGSA.Run.EmissionFreshnessTests.receipt_roots_false
