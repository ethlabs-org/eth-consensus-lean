module
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyStore -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Shared.FGSafetyScope -- shake: keep (#print axioms)
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.FGSA.Run.fgsaSafetyReads
#print axioms AvailableChain.FGSA.Run.fgsaSafetyWireLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyClientLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyUnitLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyReads_def
#print axioms AvailableChain.FGSA.Run.fgsaSafetyStoreLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyOrderLaws
#print axioms AvailableChain.FGSA.Run.fgsaSafetyScopeLaws
#print axioms AvailableChain.FGSA.Run.fgsa_safetyScopedRoots
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_runAccountable
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_parent_scope
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_read_scope
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_stores_accountable
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_reads_accountable
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_event_agreement
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_read_agreement
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_pool_count
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_slashableBound_of_faults
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_finalizedMonotone
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_clientSafeAll
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_read_row_origin
#print axioms AvailableChain.FGSA.Run.fgsa_safetySlashesRead
#print axioms AvailableChain.FGSA.Run.fgsa_bridge_honestNeverSlashed
#print axioms AvailableChain.FGSA.Run.fgsa_safetyProposalErase_def
#print axioms AvailableChain.FGSA.Run.fgsa_safetyProposalRows_def
#print axioms AvailableChain.FGSA.Run.safetyProposalErase
#print axioms AvailableChain.FGSA.Run.safetyProposalRows

namespace AvailableChain.FGSA.Run
open AvailableChain.FGCompose
example (p : Params) {In : Type} (c : AppCodec In) :
    FGCoreLaws (fgsaCoreReads p c) := fgsaCoreLaws p c
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyWireLaws (fgsaSafetyReads p c)
example (p : Params) {In : Type} (c : AppCodec In) : Prop :=
  FGSafetyClientLaws (fgsaSafetyReads p c) p.E p.cfg
example (p : Params) {In : Type} (c : AppCodec In) :
    FGSafetyOrderLaws (fgsaCoreReads p c) (fgsaSafetyReads p c) := fgsaSafetyOrderLaws p c
end AvailableChain.FGSA.Run

end

#print axioms AvailableChain.FGSA.Run.fgsaSafetyRestartLaws
#print axioms AvailableChain.FGSA.Run.fgsa_restore_finality_fields

#print axioms AvailableChain.FGSA.Run.fgsa_bridge_finalizedMonotone_restart
