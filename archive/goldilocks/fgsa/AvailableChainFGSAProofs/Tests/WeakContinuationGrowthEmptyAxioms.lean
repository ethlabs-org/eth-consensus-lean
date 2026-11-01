module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Empty -- shake: keep (axiom audit)

public section

open AvailableChain.FGSA.Run

#print axioms wcg_readAt_clamp
#print axioms wcg_empty_outputReplay
#print axioms wcg_cut_read_time
#print axioms wcg_empty_outputDomain
#print axioms wcg_proposalSourceReplay
#print axioms wcg_empty_inclusion
#print axioms wcg_growthOfOutputs
#print axioms wcg_localPrefixReplay
#print axioms wcg_empty_stateMap
#print axioms wcg_empty_stateMap_timed
#print axioms wcg_cut_before_prefix_event
#print axioms wcg_empty_stateSafety
#print axioms wcg_empty_live_of_finalBelow
#print axioms wcg_empty_finalBelow

end

#print axioms AvailableChain.FGSA.Run.wcg_empty_readerReplay
