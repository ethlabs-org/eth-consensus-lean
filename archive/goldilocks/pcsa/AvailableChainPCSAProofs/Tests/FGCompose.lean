module
public import AvailableChainPCSAProofs.Proofs.Shared.FGCompose -- shake: keep (#print axioms)

public section

#print axioms AvailableChain.PCSA.Run.pcsaCoreReads
#print axioms AvailableChain.PCSA.Run.pcsaCoreReads_def
#print axioms AvailableChain.PCSA.Run.pcsa_eraseFG_eq
#print axioms AvailableChain.PCSA.Run.pcsa_eventReads_eq_compose
#print axioms AvailableChain.PCSA.Run.pcsa_source_mem_TF

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG
example (p : Params) {In : Type} (c : AppCodec In) (nd : Node p) (o : (pcsa p c).Object) :
    (pcsaCoreReads p c).core ((pcsa p c).recordOwn nd o) = (pcsaCoreReads p c).core nd := by
  rw [pcsaCoreReads_def]
  rfl
example {n : Nat} : Function.Injective (PCSA.eraseFG : FGBlock (Fin n) → Block) := by
  rw [pcsa_eraseFG_eq]
  exact FGSA.eraseFG_injective
end AvailableChain.PCSA.Run

end
