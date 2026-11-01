module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Healing.SupportTicks -- shake: keep

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Schedule. DC: SAME an awake honest node ticks at each opening inside the horizon. -/
theorem opening_action_tick (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hs : V2.D.ScheduleWellFormed E rho) (hDelta : E.Δ = p.Δ) {x : V} (hx : x ∈ rho.honest)
    (r : Nat) (hh : p.actionTime r ≤ rho.horizon)
    (hawake : E.awake x (p.actionTime r) = true) :
    ∃ i : Nat, rho.events[i]? = some (.tick x (p.actionTime r)) := by
  have hktime : ((4 * (r * p.R) + 6 : Nat) : Time) * p.Δ = p.actionTime r := by
    change ((4 * (r * p.R) + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * ((r * p.R : Nat) : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨i, hi, _⟩ := fgsa_tick_total E rho hs hDelta x hx (4 * (r * p.R) + 6)
    (hktime ▸ hh) (hktime ▸ hawake)
  rw [hktime] at hi
  exact ⟨i, hi⟩

/-- Recovery supplies awake at a later vote with its exact horizon bound. -/
theorem healing_vote_awake_of_recovery [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {G ΔF : Time} (hrec : Recovery₂ p c E rho G ΔF)
    {x : V} (hx : x ∈ rho.honest) {r s : Slot}
    (hgst : E.t_GST ≤ SA.voteTime p.toParams r) (hrs : r ≤ s)
    (hh : SA.voteTime p.toParams s ≤ rho.horizon) :
    E.awake x (SA.voteTime p.toParams s) = true := by
  apply hrec.awake x hx _ _ hh
  apply hgst.trans
  have hrsI : (r : Int) ≤ (s : Int) := by exact_mod_cast hrs
  change 4 * p.Δ * (r : Int) + p.Δ ≤ 4 * p.Δ * (s : Int) + p.Δ
  nlinarith [p.deltaPos]

end AvailableChain.FGSA.Run
end
