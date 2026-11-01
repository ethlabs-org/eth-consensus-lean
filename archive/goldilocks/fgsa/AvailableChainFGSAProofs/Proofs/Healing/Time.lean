module
public import AvailableChainFGSAClaims.Statements.ComposeStmt
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW

public section

namespace AvailableChain.FGSA.Run

/-- H.18 producer interface for J7 H.18 / J10 HealingInput.
The full reset horizon permits the same H0 witness to supply HealingInput
and its time bound. No additional field is required. -/
def HealingInputOfH0Statement (p : Params) (G ΔF : Time) : Prop :=
  p.δt = 2 * p.R →
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
    recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
    ∀ w, H0 p c E rho w →
      HealingInput p c E rho w ΔF ∧
        tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ

theorem HealingInputOfH0Statement_def (p : Params) (G ΔF : Time) :
    HealingInputOfH0Statement p G ΔF =
      (p.δt = 2 * p.R →
      ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
        (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
        HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
        recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
        ∀ w, H0 p c E rho w →
          HealingInput p c E rho w ΔF ∧
            tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ) := by
  apply propext
  exact Iff.rfl

/-- The full reset budget is the healing budget. -/
theorem healing_resetF_budget_eq (p : Params) (G ΔF : Time) :
    B'_resetF p ΔF G + Γ p G + 4 * p.Δ = B_HF p ΔF G := by
  linarith [resetF_healing_eq p ΔF G]

/-- A healing horizon includes the full reset horizon. -/
theorem healing_resetFull_horizon (p : Params) (G ΔF GST horizon : Time)
    (h : GST + B_HF p ΔF G ≤ horizon) :
    GST + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ horizon := by
  linarith [healing_resetF_budget_eq p G ΔF]

/-- A strict reset arrival gives the strict upper H-time bound. -/
theorem healing_time_strict_of_reset (p : Params) (G ΔF GST t : Time)
    (h : t < GST + B'_resetF p ΔF G) :
    t + Γ p G + 4 * p.Δ < GST + B_HF p ΔF G := by
  linarith [healing_resetF_budget_eq p G ΔF]

/-- The recovery start is at or after GST, including a negative GST. -/
theorem healing_recoveryStart_ge (p : Params) {V : Type} (E : Generic.Env V) :
    E.t_GST ≤ recoveryStart p E := by
  let a := max 0 E.t_GST + 4 * p.Δ - 1
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hdelta : 1 ≤ p.Δ := by
    have hp := p.deltaPos
    change (0 : Int) < p.Δ at hp
    change (1 : Int) ≤ p.Δ
    omega
  have ha : 0 ≤ a := by dsimp [a]; linarith [le_max_left 0 E.t_GST]
  have hq := Int.ediv_nonneg ha hd.le
  have hm := Int.emod_lt_of_pos a hd
  have he := Int.mul_ediv_add_emod a (4 * p.Δ)
  change E.t_GST ≤ 4 * p.Δ * ((a / (4 * p.Δ)).toNat : Int) + 6 * p.Δ
  rw [Int.toNat_of_nonneg hq]
  dsimp [a] at he hm
  nlinarith [le_max_right 0 E.t_GST]

/-- Compose full reset arrival with the J7 / J10 H.18 producer.
The witness supplied by full reset arrival is used in both time bounds. -/
theorem healing_hTime_of (p : Params) (G ΔF : Time)
    (hReset : ResetArrivalFullStatement p G ΔF)
    (hInput : HealingInputOfH0Statement p G ΔF) : HTimeStatement p G ΔF := by
  intro hClock V _ _ In c E rho hSet hLive hHorizon
  have hFull := healing_resetFull_horizon p G ΔF (recoveryStart p E) rho.horizon hHorizon
  obtain ⟨w, h0, hResetTime⟩ := hReset hClock c E rho hSet hLive hFull
  obtain ⟨hHealing, hTime⟩ := hInput hClock c E rho hSet hLive hFull w h0
  exact ⟨w, hHealing, hTime,
    (healing_time_strict_of_reset p G ΔF (recoveryStart p E)
      (p.actionTime w.rStar) hResetTime)⟩

end AvailableChain.FGSA.Run
end
