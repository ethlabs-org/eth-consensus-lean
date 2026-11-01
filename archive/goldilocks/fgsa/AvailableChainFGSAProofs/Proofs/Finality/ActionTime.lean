module
public import AvailableChainFGSA.Model.Objects
public import AvailableChainFGCompose.Proofs.Timing

public section

namespace AvailableChain.FGSA.Run

private def p0c1_finality_timing (p : Params) : FGCompose.FGTiming where
  delta := p.Δ
  roundSlots := p.R
  proposal := SA.proposalTime p.toParams
  vote := SA.voteTime p.toParams
  early := SA.earlyTime p.toParams
  freeze := SA.freezeTime p.toParams
  release := SA.releaseTime p.toParams
  gate := SA.gateTime p.toParams
  action := p.actionTime

private theorem p0c1_finality_timing_laws (p : Params) :
    FGCompose.FGTimingLaws (p0c1_finality_timing p) where
  delta_pos := p.deltaPos
  rounds := p.RLarge
  proposal_eq s := by
    change 4 * p.Δ * (s : Time) = 4 * (s : Time) * p.Δ
    ring
  vote_eq _ := rfl
  early_eq _ := rfl
  freeze_eq _ := rfl
  release_eq _ := rfl
  gate_eq _ := rfl
  action_eq _ := rfl

/-- Paper 22:217–220,1228–1234,1985–1989: bound the HEAD read at an action.
DC: INTENTIONAL: SA clocks use Δ; the action read is at label qR+1. -/
theorem finality_action_time_bounds (p : Params) (r q : Nat) (hrq : r ≤ q)
    (G Δ horizon : Time) (hGST : G ≤ SA.proposalTime p.toParams (r * p.R))
    (hΔ : Δ = p.Δ) (hhor : p.actionTime q ≤ horizon) :
    G ≤ SA.voteTime p.toParams (q * p.R + 1) ∧
      SA.voteTime p.toParams (q * p.R + 1) + Δ ≤ SA.earlyTime p.toParams (q * p.R + 1) ∧
      SA.earlyTime p.toParams (q * p.R + 1) ≤ horizon ∧
      SA.voteTime p.toParams (q * p.R + 1) ≤ horizon := by
  exact FGCompose.finality_action_time_bounds (p0c1_finality_timing p)
    (p0c1_finality_timing_laws p) r q hrq G Δ horizon hGST hΔ hhor

end AvailableChain.FGSA.Run
end
