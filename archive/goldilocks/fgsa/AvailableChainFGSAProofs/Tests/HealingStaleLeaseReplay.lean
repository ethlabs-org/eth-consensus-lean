module
public import AvailableChainFGSAProofs.Proofs.Healing.RegressionFixture

public section

namespace AvailableChain.FGSA.Run.Tests.StaleLeaseReplay
open AvailableChain.SimplexFG

-- These are actual local handler folds. The global execution certificate stays open.
theorem k3_write_and_skipped_release :
    (oldWrite p3 seats).base.obligations = [((bodyD p3).erase, 2, 29)] ∧
    (source p3 seats).fastWrite.contains (5, [(bodyB p3).erase]) = true ∧
    joinedNow p3 (reader p3 seats) = false ∧
    (reader p3 seats).base.obligations = [((bodyD p3).erase, 2, 29)] ∧
    headVote p3 (reader p3 seats) 6 = (bodyD p3).erase ∧
    ¬ Block.Preceq (bodyB p3).erase (headVote p3 (reader p3 seats) 6) := by
  decide +kernel

theorem k4_three_failed_reads :
    (oldWrite p4 seats).base.obligations = [((bodyD p4).erase, 2, 33)] ∧
    (source p4 seats).fastWrite.contains (5, [(bodyB p4).erase]) = true ∧
    joinedNow p4 proposalRead = true ∧ joinedNow p4 headRead = true ∧
    ¬ Block.Preceq (bodyB p4).erase
      (getHead p4 proposalRead (proposerVotes proposalRead 7)
        (proposerSupport proposalRead 7)) ∧
    ¬ Block.Preceq (bodyB p4).erase (headVote p4 headRead 7) ∧
    ¬ Block.Preceq (bodyB p4).erase outputRead.base.stableRecord := by
  decide +kernel

end AvailableChain.FGSA.Run.Tests.StaleLeaseReplay
end

#print axioms AvailableChain.FGSA.Run.Tests.StaleLeaseReplay.k3_write_and_skipped_release
#print axioms AvailableChain.FGSA.Run.Tests.StaleLeaseReplay.k4_three_failed_reads
