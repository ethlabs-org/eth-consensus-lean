module
public import AvailableChainPCSAClaims.Statements.Premises

public section

/-! Formation through the freeze (C9 ruling, 2026-10-07).
The fields agree with FormationPrem except for the horizon and delivery cut.
The formation lane supplies parts 1–4 for this window.
-/

namespace AvailableChain.PCSA.Run

open AvailableChain.SimplexFG

variable (p : Params) {In : Type} (c : AppCodec In) {V : Type}
    [DecidableEq V] [Fintype V] {m : FGMode} (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c))

/-- The Formation premises with a horizon and delivery cut at the freeze. -/
structure FormationPreFreezePrem (s : Slot) (N : NamedProposal p.n) (ΔF : Time) : Prop where
  base : Base₂ p c E rho
  quarterCap : QuarterCap p c rho
  frame : StageOneFrame p c E rho
  slotPos : 0 < s
  horizon : SA.freezeTime p.toParams s ≤ rho.horizon
  deltaF : E.Δ ≤ ΔF
  proposal : HonestNamedProposal p c E rho s N
  delivery : Gen.V2.Duty.DeliveryWithinOn E rho IsNonRow
    (fun t => max t (SA.freezeTime p.toParams (s - 1)) + E.Δ) (SA.freezeTime p.toParams s)
  participation : nQuorum p.n ≤ (awakeHonestLabel p c E rho s).card
  commonView : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
    (viewAt p c E rho y s).map (Option.map PC.target) = some (N.pc.map PC.target)
  proposerRootReachable : FormationRootReachable p c E rho s
  leases : ∀ y ∈ rho.honest, E.awake y (SA.voteTime p.toParams s) = true →
    ∀ nd, pcsa_postClock E rho y (SA.voteTime p.toParams s) = some nd →
    ∀ B, LiveLease nd.st B →
      Block.Compatible B ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)) →
      ((N.pc.map PC.target).getD (eraseFG (controls p nd.st).Z)).depth < B.depth →
      Block.Preceq B N.erase.parent


/-- A gate window supplies the shorter freeze window. -/
theorem FormationPrem.toPreFreeze {s : Slot} {N : NamedProposal p.n} {ΔF : Time}
    (h : FormationPrem p c E rho s N ΔF) : FormationPreFreezePrem p c E rho s N ΔF := by
  have hcut : SA.freezeTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) + 3 * p.Δ ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have hd : (0 : Int) < p.Δ := p.deltaPos
    nlinarith
  refine ⟨h.base, h.quarterCap, h.frame, h.slotPos, le_trans hcut h.horizon,
    h.deltaF, h.proposal, ?_, h.participation, h.commonView,
    h.proposerRootReachable, h.leases⟩
  constructor
  · intro v hv o ho t hem w hw ht hNX
    exact h.delivery.broadcast v hv o ho t hem w hw (le_trans ht hcut) hNX
  · intro v hv i o ho t hacc w hw hNeed ht hNX
    exact h.delivery.relay v hv i o ho t hacc w hw hNeed (le_trans ht hcut) hNX

end AvailableChain.PCSA.Run
end
