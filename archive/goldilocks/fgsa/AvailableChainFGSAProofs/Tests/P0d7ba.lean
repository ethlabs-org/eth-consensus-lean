module
public import AvailableChainFGSAProofs.Proofs.Finality.Kernel -- shake: keep (axiom audit)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.P0d7ba
open AvailableChain.SimplexFG

/-! P0d7b-a: the FG-SA kernel keeps its type; its terminal bounds use the generic
`FGCompose.kernel_terminal_bounds_W` at the SA slot clock. This file checks the fieldwise
clock correspondence that the private wrapper adapter uses. -/

private def d7bt_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

/-- The generic κ, deadline and bound read the FG-SA ones exactly. -/
private theorem d7bt_bounds (p : Params) (ΔF : Time) (r : Nat) :
    FGCompose.kappaF (d7bt_timing p) ΔF = kappaF p ΔF ∧
      FGCompose.kernelDeadlineW (d7bt_timing p) ΔF r = kernelDeadlineW p ΔF r ∧
      (LivenessBoundW p ΔF → FGCompose.LivenessBoundW (d7bt_timing p) ΔF) :=
  ⟨rfl, rfl, fun h => ⟨h.kappa_le_R⟩⟩

#print axioms d7bt_bounds
#print axioms AvailableChain.FGSA.Run.finality_kernel_W_of

end AvailableChain.FGSA.Run.Tests.P0d7ba
end
