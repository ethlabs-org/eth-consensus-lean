module
public import AvailableChainPCSAProofs.Proofs.Clean.RestartStep
public import AvailableChainPCSAProofs.Proofs.Clean.StampFrom

public section

/-! Stamps for later honest proposals in a restarted clean window. -/
namespace AvailableChain.PCSA.Run
variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V]
    {c : AppCodec In} {m : FGMode}

/-- A later honest proposal is stamped by its freeze, without a current gate bound. -/
theorem pcsa_restart_honestProposal_stamped (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) {T₀ cut : Time} {a : Slot} {A : Block}
    (hW : CleanWindow E rho a T₀ cut) (hF : StageOneFrame p c E rho)
    (hFault : FaultsBelowQA p c rho) (hSeed : CleanRestartSeed p c E rho a A)
    (hSeedResult : ∃ w ∈ rho.honest, gateResultAt p c E rho w a = some (some A))
    (u : Slot) (N : NamedProposal p.n) (hu : a + 1 ≤ u)
    (hN : HonestNamedProposal p c E rho u N)
    (hQ : nQuorum p.n ≤ (awakeHonestLabel p c E rho u).card)
    (hz : SA.freezeTime p.toParams u ≤ cut) :
    ∀ x ∈ rho.honest,
      PCStampedBefore p c E rho x (SA.freezeTime p.toParams u) u N.erase := by
  try delta Slot Time at *
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  have har : a ≤ r := by omega
  have hgate : SA.gateTime p.toParams r ≤ cut := by
    apply le_trans _ hz
    have hd := p.deltaPos
    change 4 * p.Δ * (r : Int) + 6 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Int) + 3 * p.Δ
    push_cast
    linarith
  have hstate := pcsa_restart_state_from E rho hW hF hFault hSeed r har hgate
  have hseed : ∃ w ∈ rho.honest, ∃ W, gateResultAt p c E rho w a = some (some W) := by
    obtain ⟨w, hw, hr⟩ := hSeedResult
    exact ⟨w, hw, A, hr⟩
  have hheads := pcsa_restart_emitted_heads_equal E rho hW hF hFault hSeed r har
    hstate hseed hgate N hN.1 hN.2
  apply pcsa_clean_honestProposal_stamped_from E rho hW.base hF hFault hW.strict
    hW.cut.2 r _ N hN hheads hQ hz
  apply le_trans (pcsa_cleanWindow_floor E rho hW r har)
  have hd := p.deltaPos
  change 4 * p.Δ * (r : Int) ≤ 4 * p.Δ * (r : Int) + 3 * p.Δ
  linarith

end AvailableChain.PCSA.Run
end
