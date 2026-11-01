module
public import AvailableChainGridCO.Proofs.LegacyMode -- shake: keep (axioms)
public import AvailableChainGridCO.Proofs.StoreFacts -- shake: keep (axioms)

public section


-- ROOT-DIGEST-2: new public W1 declarations from the signed checkpoint inventory.
namespace AvailableChain.GridCO
#print axioms HeadMode
#print axioms HeadTarget
#print axioms goldfishScoreOn
#print axioms goldfishScore_block_eq
#print axioms instDecidableEqHeadMode
#print axioms instDecidableEqHeadTarget
#print axioms instReprHeadMode
#print axioms instReprHeadTarget
#print axioms prefixSupport_block_eq
#print axioms resolutionTree
#print axioms resolveTarget
#print axioms resolvedBefore_block
#print axioms resolvedHead?
#print axioms targetOfBlock
end AvailableChain.GridCO

namespace AvailableChain.GridCO.HeadMode
#print axioms block
#print axioms root
end AvailableChain.GridCO.HeadMode

namespace AvailableChain.GridCO.Legacy
#print axioms State
#print axioms act
#print axioms act_embed
#print axioms admissionLevels
#print axioms admissionLevels_embed
#print axioms admitProposal
#print axioms admitProposal_embed
#print axioms admitVote
#print axioms admitVote_embed
#print axioms advance
#print axioms block
#print axioms blockKnown
#print axioms carriedRaw
#print axioms carriedRaw_embed
#print axioms carriedSupport
#print axioms carriedSupport_embed
#print axioms carries
#print axioms cleanSupport
#print axioms cleanSupport_embed
#print axioms clock
#print axioms clockFrom
#print axioms clockFrom_embed
#print axioms clock_embed
#print axioms clock_eq_from_genesis
#print axioms confirmation
#print axioms confirmationFrom
#print axioms confirmationFrom_embed
#print axioms confirmation_eq_from_genesis
#print axioms confirmed
#print axioms deadlineOf
#print axioms deliveries_embed
#print axioms depsPresent
#print axioms duties
#print axioms duties_nodup
#print axioms duties_spec
#print axioms earlyVotes
#print axioms earlyVotes_embed
#print axioms embed
#print axioms embed_early
#print axioms embed_ite
#print axioms embed_now
#print axioms equivocates
#print axioms equivocates_block
#print axioms event_fold_embed
#print axioms excludes
#print axioms excludes_embed
#print axioms expire
#print axioms expire_embed
#print axioms forkChoice
#print axioms forkChoice_embed
#print axioms freeze
#print axioms freeze_embed
#print axioms fromHead
#print axioms frozenAt
#print axioms frozenAt_embed
#print axioms gate
#print axioms gateFrom
#print axioms gateFrom_embed
#print axioms gate_eq_from_genesis
#print axioms goldfishEligible
#print axioms goldfishEligible_block
#print axioms goldfishScore
#print axioms goldfishScore_block
#print axioms gridCO
#print axioms handles
#print axioms headLabel?
#print axioms headLabel_block
#print axioms headSeat?
#print axioms headSeat_block
#print axioms headTarget?
#print axioms headTarget_block
#print axioms initial
#print axioms instReprState
#print axioms lateVotes
#print axioms lateVotes_embed
#print axioms liveRoot
#print axioms liveRoot_embed
#print axioms prefixSupport
#print axioms prefixSupport_embed
#print axioms process
#print axioms process_embed
#print axioms processed
#print axioms proposalsAt
#print axioms proposalsAt_embed
#print axioms propose
#print axioms propose_embed
#print axioms proposerSupportView
#print axioms proposerSupportView_embed
#print axioms proposerView
#print axioms proposerView_embed
#print axioms recordGenuine
#print axioms recordGenuine_embed
#print axioms release
#print axioms releaseCount
#print axioms releaseCount_embed
#print axioms releaseThreshold
#print axioms release_embed
#print axioms resolvedBefore
#print axioms resolvedBefore_embed
#print axioms resolvedHead_embed
#print axioms resolvedHead_of_before
#print axioms sameSeat
#print axioms sameSeat_block
#print axioms savedEarly
#print axioms savedGenuine
#print axioms savedGenuine_embed
#print axioms seatVotes
#print axioms seatVotes_block
#print axioms seats
#print axioms seats_block
#print axioms slotsAt
#print axioms slotsAt_nodup
#print axioms slotsAt_spec
#print axioms slowEligible
#print axioms slowEligible_embed
#print axioms stable
#print axioms stampBlock
#print axioms stampBlock_embed
#print axioms stampVote
#print axioms stampVote_embed
#print axioms toHead?
#print axioms toHead_block
#print axioms voterCount
#print axioms voterCount_block
#print axioms voterSupportView
#print axioms voterSupportView_embed
#print axioms voterTree
#print axioms voterTree_embed
#print axioms voterView
#print axioms voterView_embed
#print axioms votesAt
#print axioms votesAt_embed
#print axioms votes_fold_embed
#print axioms wellFormed
#print axioms world_step_embed
#print axioms writeObligation
#print axioms writeObligation_embed
end AvailableChain.GridCO.Legacy

namespace AvailableChain.GridCO.Legacy.State
#print axioms blockStamp
#print axioms blocks
#print axioms early
#print axioms frozen
#print axioms genuine
#print axioms goldfishRecord
#print axioms mk
#print axioms now
#print axioms obligations
#print axioms proposals
#print axioms releaseSnapshots
#print axioms stableRecord
#print axioms voteStamp
#print axioms votes
end AvailableChain.GridCO.Legacy.State

namespace AvailableChain.GridCO.Legacy.instReprState
#print axioms repr
end AvailableChain.GridCO.Legacy.instReprState

namespace AvailableChain.GridCO.State
#print axioms headDomain
end AvailableChain.GridCO.State

namespace AvailableChain.GridCO.instReprHeadMode
#print axioms repr
end AvailableChain.GridCO.instReprHeadMode
