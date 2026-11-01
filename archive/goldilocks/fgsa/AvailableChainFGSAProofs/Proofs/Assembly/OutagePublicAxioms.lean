module
public import AvailableChainFGSAProofs.Proofs.Outage.Export -- shake: keep (#print axioms targets)
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAProofs.Proofs.OutageContinuation.Export -- shake: keep

public section

#print axioms AvailableChain.FGSA.Run.OutageRepairReady

#print axioms AvailableChain.FGSA.Run.outage_caught_up_gate_rows
#print axioms AvailableChain.FGSA.Run.outage_cut_pos
#print axioms AvailableChain.FGSA.Run.outage_scoped_arming
#print axioms AvailableChain.FGSA.Run.outage_protected_read
#print axioms AvailableChain.FGSA.Run.outage_compat_body
#print axioms AvailableChain.FGSA.Run.fast_p1_body
#print axioms AvailableChain.FGSA.Run.slow_p1_body
#print axioms AvailableChain.FGSA.Run.outage_outageCompatClaim_of
#print axioms AvailableChain.FGSA.Run.outage_fastP1Claim_of
#print axioms AvailableChain.FGSA.Run.outage_slowP1Claim_of
#print axioms AvailableChain.FGSA.Run.outage_compat_body_of_cut
#print axioms AvailableChain.FGSA.Run.outage_continuation_scoped_body
#print axioms AvailableChain.FGSA.Run.outageContinuation_claim_of
