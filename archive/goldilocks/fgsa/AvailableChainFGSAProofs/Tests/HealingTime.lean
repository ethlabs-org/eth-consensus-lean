module
public import AvailableChainFGSAProofs.Proofs.Healing.Time -- shake: keep (J11 statement examples)

public section

namespace AvailableChain.FGSA.Run.Tests.HealingTime

variable (p : Params) (G ΔF : Time)

-- The composition has exactly the two statement inputs.
example (hReset : ResetArrivalFullStatement p G ΔF)
    (hInput : HealingInputOfH0Statement p G ΔF) : HTimeStatement p G ΔF :=
  healing_hTime_of p G ΔF hReset hInput

-- Apply the statement on a run, with the approved recovery-start horizon.
example (hReset : ResetArrivalFullStatement p G ΔF)
    (hInput : HealingInputOfH0Statement p G ΔF) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hSet : HealingSet p c E rho G ΔF) (hLive : LivenessBoundW p ΔF)
    (hHorizon : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon) :
    ∃ w, HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ ∧
      p.actionTime w.rStar + Γ p G + 4 * p.Δ < recoveryStart p E + B_HF p ΔF G :=
  healing_hTime_of p G ΔF hReset hInput hClock c E rho hSet hLive hHorizon

-- The horizon bound includes equality; the reset arrival remains strict.
example (GST : Time) :
    GST + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ GST + B_HF p ΔF G :=
  healing_resetFull_horizon p G ΔF GST (GST + B_HF p ΔF G) le_rfl

example (GST t : Time) (h : t < GST + B'_resetF p ΔF G) :
    t + Γ p G + 4 * p.Δ < GST + B_HF p ΔF G :=
  healing_time_strict_of_reset p G ΔF GST t h

#print axioms healing_hTime_of

end AvailableChain.FGSA.Run.Tests.HealingTime
end
