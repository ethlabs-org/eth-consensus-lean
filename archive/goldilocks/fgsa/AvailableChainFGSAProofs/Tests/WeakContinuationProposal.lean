module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Proposal

public section

/-! WC J3, plan §6.9; DC first proposal comparison prefix.
At s=u+2, the cutoff is u. No pending suffix result enters the maximum. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationProposal

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}
    {w : HealingWitness} {iStar : Nat}

/-- WC J3, plan §6.9; DC first eligible proposal: its maximum is exactly the seed. -/
theorem firstEligibleMaximum (hS : V2.D.ScheduleWellFormed E rho)
    (hi : WCInv p c E rho w iStar rho.events.length) :
    ∃ D, D = w.QStar ∧ Block.Preceq w.QStar D := by
  obtain ⟨D, hD, hQD, _⟩ := wc_historyMax hS hi ((w.u + 2) - 2)
  refine ⟨D, ?_, hQD⟩
  rcases hD with h | ⟨j, x, s, hresult, hs⟩
  · exact h
  · have hu := hresult.label
    simp only [Slot] at hu hs
    omega

/-- WC J3, plan §6.9; DC first HEAD batch: the seed supplies the previous-label read. -/
theorem firstEligibleHeads
    (_hs : V2.D.ScheduleWellFormed E rho) (_hdelta : E.Δ = p.Δ)
    (hseed : WCSeed p c E rho w iStar)
    (_hi : WCInv p c E rho w iStar rho.events.length)
    (_hgate : SA.gateTime p.toParams (w.u + 2) ≤ rho.horizon) :
    ∀ y ∈ rho.honest, ∃ k, WCHeadRead p c E rho k y ((w.u + 2) - 1) w.QStar :=
by
  intro y hy
  obtain ⟨k, _, hk⟩ := hseed.nextHeads y hy
  refine ⟨k, ?_⟩
  have he : w.u + 2 - 1 = w.u + 1 := by simp only [Slot]; omega
  rw [he]
  exact hk

/-- WC J3, plan §6.9; DC pivot contract: all path and walk fields are present. -/
theorem pivotContract [Fintype V] (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframe : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCProposalPivotStatement p c E rho ΔF w iStar :=
  wc_proposalPivot ΔF w iStar hframe

#print axioms firstEligibleMaximum
#print axioms firstEligibleHeads
#print axioms pivotContract

end AvailableChain.FGSA.Run.Tests.WeakContinuationProposal
end
