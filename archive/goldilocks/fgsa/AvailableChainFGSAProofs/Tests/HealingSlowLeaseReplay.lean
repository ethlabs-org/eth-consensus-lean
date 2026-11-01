module
public import AvailableChainFGSAProofs.Proofs.Healing.RegressionFixture

public section

namespace AvailableChain.FGSA.Run.Tests.SlowLeaseReplay
open AvailableChain.SimplexFG StaleLeaseReplay

theorem certificate_prepared :
    prepared.proposals.length = 3 ∧ prepared.fg.h_max = 3 ∧ prepared.fg.h_j = 2 ∧
    eraseFG prepared.fg.J = J.erase ∧ prepared.fg.F = .genesis ∧
    (controls params prepared).contest = false ∧
    ([B, J, A].map (fun N => wellFormed params ⟨.proposer N.slot, .proposal N⟩)).all
      id = true := by
  decide +kernel

theorem slow_write_after_incompatible_head :
    GridCO.savedGenuine saved.base 250 = some (some B.erase) ∧
    saved.base.obligations = [] ∧ joinedNow params beforeWrite = true ∧
    ¬ Block.Preceq B.erase (headVote params beforeWrite 252) ∧
    GridCO.savedGenuine afterWrite.base 251 = some (some B.erase) ∧
    afterWrite.base.obligations = [(B.erase, 4, 1017)] ∧
    fastWriteAt afterWrite 251 = some [] := by
  decide +kernel

end AvailableChain.FGSA.Run.Tests.SlowLeaseReplay
end

#print axioms AvailableChain.FGSA.Run.Tests.SlowLeaseReplay.certificate_prepared
#print axioms AvailableChain.FGSA.Run.Tests.SlowLeaseReplay.slow_write_after_incompatible_head
