module
public import AvailableChainFGSAProofs.Proofs.Assembly.Clean -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Assembly.Foundations -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Shared.Claims -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Assembly.ProgressAttempt -- shake: keep (audit)
public import AvailableChainFGSAProofs.Proofs.Assembly.ResetSource -- shake: keep (audit)

/-! Strict checks for the prepared P-As supplier slice. -/

#print axioms AvailableChain.FGSA.Run.assembly_sleep_channels
#print axioms AvailableChain.FGSA.Run.assembly_rows_of_healingSet
#print axioms AvailableChain.FGSA.Run.fgsa_finalityKernel_W
#print axioms AvailableChain.FGSA.Run.fgsa_finalityKernelJoined_W
#print axioms AvailableChain.FGSA.Run.fgsa_tailKernel_W
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLivenessRecFE_W
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLivenessRecF4_W
#print axioms AvailableChain.FGSA.Run.fgsa_proposalFinalRecFE_W
#print axioms AvailableChain.FGSA.Run.fgsa_proposalFinalRecF4_W
#print axioms AvailableChain.FGSA.Run.fgsa_aboveFrontierRecFE_W
#print axioms AvailableChain.FGSA.Run.fgsa_aboveFrontierRecF4_W
#print axioms AvailableChain.FGSA.Run.clientSafety_base
#print axioms AvailableChain.FGSA.Run.cleanHistory_of_cut
#print axioms AvailableChain.FGSA.Run.cleanPrefixTruncation_of_cut
#print axioms AvailableChain.FGSA.Run.cleanSafety_outputs
#print axioms AvailableChain.FGSA.Run.uniformHealing_of_hTimeConcl
#print axioms AvailableChain.FGSA.Run.fgsa_firstFinality_recFE
#print axioms AvailableChain.FGSA.Run.fgsa_firstFinality_recF4
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recFE
#print axioms AvailableChain.FGSA.Run.fgsa_finalityLivenessGST_recF4
#print axioms AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recFE
#print axioms AvailableChain.FGSA.Run.fgsa_proposalFinalGST_recF4
#print axioms AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recFE
#print axioms AvailableChain.FGSA.Run.fgsa_aboveFrontierGST_recF4
#print axioms AvailableChain.FGSA.Run.fgsa_availableGST
#print axioms AvailableChain.FGSA.Run.outageContinuation_of_body
#print axioms AvailableChain.FGSA.Run.fgsa_availableGrowthGST
#print axioms AvailableChain.FGSA.Run.weakContinuation_of_live

#print axioms AvailableChain.FGSA.Run.ProgressAttemptRows
#print axioms AvailableChain.FGSA.Run.healing_progressAttemptStatement
#print axioms AvailableChain.FGSA.Run.assembly_reset_emittedName

#print axioms AvailableChain.FGSA.Run.fgsa_recovery_gate_readers

#print axioms AvailableChain.FGSA.Run.assembly_clean_state
#print axioms AvailableChain.FGSA.Run.fgsa_cleanSafetyClaim
