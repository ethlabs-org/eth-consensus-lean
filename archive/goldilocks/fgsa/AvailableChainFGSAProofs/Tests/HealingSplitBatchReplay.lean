module
public import AvailableChainFGSAProofs.Proofs.Healing.RegressionFixture

public section

set_option maxRecDepth 10000

namespace AvailableChain.FGSA.Run.Tests.SplitBatchReplay
open AvailableChain.SimplexFG StaleLeaseReplay

theorem certificate_prepared :
    prepared.proposals.length = 6 ∧ prepared.fg.h_max = 3 ∧ prepared.fg.h_j = 2 ∧
    prepared.fg.F = .genesis ∧ (controls params prepared).contest = true ∧
    wellFormed params ⟨.proposer WB.slot, .proposal WB⟩ = true := by
  decide +kernel

theorem strict_freeze_split :
    GridCO.stampBlock early.base WB.erase = 2013 ∧
    GridCO.stampBlock late.base WB.erase = 2014 ∧
    joinedNow params earlyHead = true ∧ joinedNow params lateHead = true ∧
    Block.Preceq B.erase (headVote params earlyHead 252) ∧
    ¬ Block.Preceq B.erase (headVote params lateHead 252) := by
  decide +kernel

theorem split_release_keeps_live_lease :
    slowWrite.base.obligations = [(B.erase, 4, 2034)] ∧
    GridCO.releaseCount params.toParams.engine (actView fullBatch) 252 B.erase = 3 ∧
    fullBatch.base.obligations = [(B.erase, 4, 2034)] ∧
    repairRead.base.obligations = [(B.erase, 4, 2034)] ∧
    liveRoot params repairRead = B.erase ∧
    ¬ Block.Preceq B.erase (headVote params otherBatch 253) := by
  decide +kernel

theorem earliest_repair_parent_and_expiry :
    joinedNow params repairRead = true ∧
    Block.Preceq B.erase (getHead params repairRead (proposerVotes repairRead 254)
      (proposerSupport repairRead 254)) ∧
    expiryRead.base.obligations = [] ∧
    ¬ Block.Preceq B.erase (headVote params expiryRead 254) := by
  decide +kernel

end AvailableChain.FGSA.Run.Tests.SplitBatchReplay
end

#print axioms AvailableChain.FGSA.Run.Tests.SplitBatchReplay.certificate_prepared
#print axioms AvailableChain.FGSA.Run.Tests.SplitBatchReplay.strict_freeze_split
#print axioms AvailableChain.FGSA.Run.Tests.SplitBatchReplay.split_release_keeps_live_lease

#print axioms AvailableChain.FGSA.Run.Tests.SplitBatchReplay.earliest_repair_parent_and_expiry
