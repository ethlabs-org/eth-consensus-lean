module
public import AvailableChainFGSAProofs.Proofs.Healing.HealingInputExport
-- shake: keep (J10 fixtures)

public section

/-! S5 J10: apply both exports with separate hypothetical field inputs.
These tests do not import NonVacuity modules. -/

namespace AvailableChain.FGSA.Run.Tests.HealingInputExport

variable (p : Params) (G ΔF : Time)

variable (healed : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → Healed p c E rho (tstar p w))

variable (sourcePrefix : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → Block.Preceq w.CStar w.QStar)

variable (tHigh : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → THigh p c E rho w)

variable (tCarrier : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → TCarrier p c E rho w)

variable (rows : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      TRows p c E rho ΔF)

variable (h2A : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H2A p c E rho w)

variable (h2Prime : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H2Prime p c E rho w)

variable (h3 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H3 p c E rho w)

variable (h4 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H4 p c E rho w)

variable (h5 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H5RawTransfer p c E rho w)

variable (h6 : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → H6GateService p c E rho w)

variable (timeBound : p.δt = 2 * p.R →
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      HealingSet p c E rho G ΔF → LivenessBoundW p ΔF →
      recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon →
      ∀ w, H0 p c E rho w → tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ)

include healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound

-- E1 exports the full statement from the twelve separate named inputs.
example : HealingInputOfH0Statement p G ΔF :=
  healing_healingInputOfH0 p G ΔF
    healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound

-- E2 has the same inputs, plus full reset arrival.
example (hReset : ResetArrivalFullStatement p G ΔF) : HTimeStatement p G ΔF :=
  healing_hTime_of_inputs p G ΔF
    healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound hReset

-- Apply E1 to a supplied H0 witness; consume every package field and the bound.
example (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hSet : HealingSet p c E rho G ΔF) (hLive : LivenessBoundW p ΔF)
    (hHorizon : recoveryStart p E + B'_resetF p ΔF G + Γ p G + 4 * p.Δ ≤ rho.horizon)
    (w : HealingWitness) (h0 : H0 p c E rho w) :
    Healed p c E rho (tstar p w) ∧ H0 p c E rho w ∧
      THigh p c E rho w ∧ TCarrier p c E rho w ∧ TRows p c E rho ΔF ∧
      H2A p c E rho w ∧ H2Prime p c E rho w ∧ H3 p c E rho w ∧
      H4 p c E rho w ∧ H5RawTransfer p c E rho w ∧ H6GateService p c E rho w ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ := by
  have hInput := healing_healingInputOfH0 p G ΔF
    healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound
  rw [HealingInputOfH0Statement_def] at hInput
  obtain ⟨input, bound⟩ := hInput hClock c E rho hSet hLive hHorizon w h0
  exact ⟨input.healed, input.wit, input.t.h1, input.t.h2, input.t.rows,
    input.ac.h2A, input.ac.h2', input.ac.h3, input.ac.h4, input.ac.h5, input.ac.h6, bound⟩

-- Apply E2 at the healing horizon and retain both time bounds on the same witness.
example (hReset : ResetArrivalFullStatement p G ΔF) (hClock : p.δt = 2 * p.R)
    {V In : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hSet : HealingSet p c E rho G ΔF) (hLive : LivenessBoundW p ΔF)
    (hHorizon : recoveryStart p E + B_HF p ΔF G ≤ rho.horizon) :
    ∃ w, HealingInput p c E rho w ΔF ∧
      tstar p w ≤ p.actionTime w.rStar + Γ p G + 4 * p.Δ ∧
      p.actionTime w.rStar + Γ p G + 4 * p.Δ < recoveryStart p E + B_HF p ΔF G :=
  healing_hTime_of_inputs p G ΔF
    healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound
    hReset hClock c E rho hSet hLive hHorizon

-- The new projection preserves the reset witness and first-proposal data.
omit healed sourcePrefix tHigh tCarrier rows h2A h2Prime h3 h4 h5 h6 timeBound in
example {V In : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    {w : HealingWitness} (h0 : H0 p c E rho w) : PostResetStart p c E rho w :=
  healing_postResetStart_of_h0 p c E rho h0

#print healing_healingInputOfH0
#print healing_hTime_of_inputs
#print axioms healing_postResetStart_of_h0
#print axioms healing_healingInputOfH0
#print axioms healing_hTime_of_inputs

end AvailableChain.FGSA.Run.Tests.HealingInputExport
end
