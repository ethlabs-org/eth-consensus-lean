module
public import AvailableChainFGSAProofs.Proofs.Assembly.Finality -- shake: keep (axiom audit)
public import AvailableChainFGSAProofs.Proofs.Assembly.Root -- shake: keep (closure audit)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d7bb
open AvailableChain.SimplexFG

/-! P0d7b-b: the frozen exporters keep their types; `forward_witness_FE_of` takes its round
from the generic `FGCompose.forward_round_FE` at the SA slot clock. This file checks the
fieldwise correspondence that the private wrapper adapter uses, and audits the old
Export/Assembly closure. -/

private def d7bbt_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

/-- The generic window and recurrence read the FG-SA ones exactly. -/
private theorem d7bbt_window (p : Params) (ΔF start horizon : Time) (g : Nat)
    (H : Slot → Prop) :
    FGCompose.W_W (d7bbt_timing p) ΔF g = W_W p ΔF g ∧
      (FGCompose.FE_W (d7bbt_timing p) ΔF H start horizon g ↔ FE_W p ΔF H start horizon g) :=
  ⟨rfl, Iff.rfl⟩

#print axioms d7bbt_window
#print axioms AvailableChain.FGSA.Run.finality_kernel_prem_W_of_joined
#print axioms AvailableChain.FGSA.Run.finality_kernel_joined_W_of
#print axioms AvailableChain.FGSA.Run.forward_witness_FE_of
#print axioms AvailableChain.FGSA.Run.finality_liveness_of_forward_W
#print axioms AvailableChain.FGSA.Run.finality_liveness_FE_W_of
#print axioms AvailableChain.FGSA.Run.fgsa_finalityKernel_W
#print axioms AvailableChain.FGSA.Run.fgsaClaims

end AvailableChain.FGSA.Run.Tests.P0d7bb
end
