module
public import AvailableChainFGSAProofs.Proofs.Shared.FGCompose -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Finality.MiddleSupport -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Finality.Rows -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Assembly.Root -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.FGSA.Run.fgsaCoreReads
#print axioms AvailableChain.FGSA.Run.fgsaCoreReads_def
#print axioms AvailableChain.FGSA.Run.fgsaCoreLaws
#print axioms AvailableChain.FGSA.Run.fgsaHeadLaws
#print axioms AvailableChain.FGSA.Run.fgsa_eventReads_eq_compose
#print axioms AvailableChain.FGSA.Run.fgsa_chainRows_eq_compose
#print axioms AvailableChain.FGSA.Run.kmid_tick_lt_afterTicks
#print axioms AvailableChain.FGSA.Run.kmid_head_held
#print axioms AvailableChain.FGSA.Run.kmid_source_mem_TF
#print axioms AvailableChain.FGSA.Run.kmid_chainRows_of_head
#print axioms AvailableChain.FGSA.Run.kmid_head_held_from
#print axioms AvailableChain.FGSA.Run.finality_action_source
#print axioms AvailableChain.FGSA.Run.fgsaClaims

example (p : AvailableChain.FGSA.Params) : AvailableChain.FGSA.Run.FGSAClaims p :=
  AvailableChain.FGSA.Run.fgsaClaims p

end
