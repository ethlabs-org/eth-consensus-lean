module
public import AvailableChainFGSAProofs.Proofs.Shared.BoundsW
-- shake: keep (own-library route)

@[expose] public section

namespace AvailableChain.FGSA.Run.Tests.NonVacuity.HealingParams

/-- ROOT-DIGEST W3b. S5 fixture: one honest node, positive horizon, and unchanged SA clocks. -/
def params : Params :=
  ⟨⟨1, 1, 2, 0, by decide, by decide, by decide, by decide⟩,
    3, 6, by decide, 2, by decide, fun d => ⟨d.slot + 1⟩⟩

def env : Generic.Env (Fin 1) := ⟨1, by decide, 0, le_rfl, fun _ _ => true⟩
def deltaF : Time := 3
def gap : Time := 4
def horizon : Time := 304

theorem params_delta : params.Δ = 1 := rfl
theorem params_n : params.n = 1 := rfl
theorem params_k : params.k = 2 := rfl
theorem params_eta : params.η = 0 := rfl
theorem params_R : params.R = 3 := rfl
theorem params_timeout : params.δt = 6 := rfl
theorem params_window : params.K_W = 2 := rfl
theorem env_delta : env.Δ = params.Δ := rfl
theorem env_gst : env.t_GST = 0 := rfl
theorem env_awake (v : Fin 1) (t : Time) : env.awake v t = true := rfl
theorem deltaF_value : deltaF = 3 := rfl
theorem gap_value : gap = 4 := rfl
theorem horizon_value : horizon = 304 := rfl
theorem horizon_pos : 0 < horizon := by decide
theorem deltaF_lower : env.Δ ≤ deltaF := by decide
theorem gap_lower : 4 * params.Δ ≤ gap := by decide

theorem kappaF_value : kappaF params deltaF = 3 := by decide
theorem betaF_value : betaF params deltaF = 12 := by decide
theorem epsF_value : epsF params deltaF = 4 := by decide
theorem period_value : P params = 12 := by decide
theorem gamma_value : Γ params gap = 4 := by decide
theorem lease_value : L params = 7 := by decide
theorem rhoGamma_value : ρΓ params gap = 26 := by decide
theorem rhoOne_value : ρ₁ params gap = 21 := by decide
theorem short_k : params.k ≤ 2 * params.R + 1 := by decide
theorem Eg_two_value : E_gF params deltaF gap (ρΓ params gap) = 53 := by decide
theorem Eg_one_value : E_gF params deltaF gap (ρ₁ params gap) = 48 := by decide
theorem Ej_two_value : E_jF params deltaF gap (ρΓ params gap) = 49 := by decide
theorem Ej_one_value : E_jF params deltaF gap (ρ₁ params gap) = 44 := by decide
theorem Bc_two_value : B_cF params deltaF gap (ρΓ params gap) = 48 := by decide
theorem Bc_one_value : B_cF params deltaF gap (ρ₁ params gap) = 43 := by decide
theorem Dc_two_value : D_cF params (ρΓ params gap) = 37 := by decide
theorem Dc_one_value : D_cF params (ρ₁ params gap) = 32 := by decide
theorem reset_two_value : B_resetF params deltaF gap (ρΓ params gap) = 325 := by decide
theorem reset_one_value : B_resetF params deltaF gap (ρ₁ params gap) = 295 := by decide
theorem reset_value : B'_resetF params deltaF gap = 295 := by decide
theorem healing_two_value : B_H2F params deltaF gap = 333 := by decide
theorem healing_one_value : B_H1F params deltaF gap = 303 := by decide
theorem healing_value : B_HF params deltaF gap = 303 := by decide

theorem healing_strict_horizon : B_HF params deltaF gap < horizon := by decide
theorem healing_horizon : env.t_GST + B_HF params deltaF gap ≤ horizon := by decide
theorem reset_horizon : env.t_GST + B'_resetF params deltaF gap ≤ horizon := by decide
theorem reset_full_horizon :
    env.t_GST + B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ ≤ horizon := by
  decide
theorem reset_full_budget : B'_resetF params deltaF gap + Γ params gap + 4 * params.Δ = 303 := by
  decide
theorem action_three_value : params.actionTime 3 = 42 := by decide
theorem renewed_three_budget :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ = 66 := by decide
theorem renewed_three_horizon :
    params.actionTime 3 + 2 * P params + Γ params gap - 4 * params.Δ ≤ horizon := by decide

theorem livenessBound : LivenessBoundW params deltaF := ⟨by decide⟩

end AvailableChain.FGSA.Run.Tests.NonVacuity.HealingParams
end
