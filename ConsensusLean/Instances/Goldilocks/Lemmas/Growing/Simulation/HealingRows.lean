module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingEdges

public section

/-! # Healing suppliers at the canonical Goldilocks run map -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Canonical high entries come from the healing leaves, not from `heal_after_reset`.
No Goldilocks local-data equation is needed for this field. -/
theorem goldilocks_highCanonicalSupply (S : Setup) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) (K : Contract ProgressReq)
    (C : ACCorrectLocal (goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))
      (goldilocksRunMap S rho hn hv).signer) :
    HighCanonicalSupply (goldilocksRunMap S rho hn hv) K C := by
  intro hβ _ _ _ _ _ hr hp ha hab
  exact highCanonical C.healing hβ hr hp ha hab

end Consensus.Goldilocks.Simulation

end
