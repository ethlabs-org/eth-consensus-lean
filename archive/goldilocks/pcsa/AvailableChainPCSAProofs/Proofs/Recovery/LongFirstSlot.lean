module
public import AvailableChainPCSAProofs.Proofs.Recovery.ProposalPaths
public import AvailableChainPCSAProofs.Proofs.Recovery.FirstSlot

public section

namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- Long-break first-slot inputs with the explicit proposer-root walk conjunct.
Recovery/Export converts the root conjunct with RecoveryRootReachable_def. -/
theorem recovery_firstSlot_long_body (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {G ΔF : Time}
    (h : Recovery₂ p c E rho G ΔF) (hF : StageOneFrame p c E rho)
    (g s : Slot) (transport : RecoveryLockTransport p c E rho g)
    (hgst : E.t_GST ≤ SA.voteTime p.toParams g)
    (hmix : SA.voteTime p.toParams (g + 2 * p.k - 1) ≤ SA.proposalTime p.toParams s)
    (hafter : E.t_GST + p.Δ ≤ SA.proposalTime p.toParams s)
    (hprop : Gen.V2.Duty.HonestAwakeProposer E
      (pcsaInterface p c (m := m)).toInterface rho s)
    (horizon : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ N : NamedProposal p.n, FormationPrem p c E rho s N ΔF ∧
  ∀ nd, pcsa_postClock E rho
      (V2.D.proposerOf rho (pcsaInterface p c (m := m)).toInterface s)
      (V2.D.proposalTime (pcsaInterface p c (m := m)).toInterface s) = some nd →
    let st := nd.st
    let pc := proposerPC p st
    let root := (pc.map PC.target).getD (eraseFG (controls p st).Z)
    Block.Preceq (liveRoot p st pc)
      (GridCO.ghost root (erasedList st (fullTree p st))
        (GridCO.goldfishScore st.base.blocks (proposerVotes st s) (proposerSupport st s))
        (eligible p st (proposerVotes st s) (proposerSupport st s))) := by
  have hpos := (recovery_long_slot_bounds p g s hmix).1
  have hd := p.deltaPos
  have htime : SA.proposalTime p.toParams s ≤ SA.gateTime p.toParams s := by
    change 4 * p.Δ * (s : Int) ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    linarith
  obtain ⟨N, hN⟩ := recovery_named_proposal_exists E rho h.base hF s hpos hprop
    (htime.trans horizon)
  have hroot := recovery_long_proposer_root E rho h hF g s transport hgst hmix hprop.1 horizon
  refine ⟨N, ?_, hroot⟩
  exact {
    base := h.base
    quarterCap := h.quarterCap
    frame := hF
    slotPos := hpos
    horizon := horizon
    deltaF := h.deltaF
    proposal := hN
    delivery := recovery_delivery_from_run E rho h s hpos hafter horizon
    participation := (recovery_participation E rho h s hafter horizon).1
    proposerRootReachable := hroot
    commonView := recovery_commonView E rho h hF s hpos hafter horizon N hN
    leases := fun y hy _ nd hnd B hB hcompat _ =>
      recovery_long_voter_leases E rho h hF g s transport hgst hmix horizon N hN
        y hy nd hnd B hB hcompat }

end AvailableChain.PCSA.Run
end
