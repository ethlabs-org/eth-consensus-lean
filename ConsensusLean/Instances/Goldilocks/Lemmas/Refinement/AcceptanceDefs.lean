module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Instances.Goldilocks.Statements.Refinement.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetCoefficients

public section

/-! # Goldilocks Refinement: the acceptance contract and its coefficients

The characterising lemmas of the fixed assumptions (`AcceptanceAssumptions`: row ratio and
timeout), the final pattern (`finalWindow`, gap `cF r`), the coefficients (`accepted_catchUp`,
`accepted_heal`, `accepted_latency`) and the contract `acceptanceContract`, all defined in the
statement module `Statements/Refinement/Accepted`, and the abbreviation `K`. The row transport is
instantiated at the actual protocol row delay `rowDelay` (HSSharedRun, HSSharedOfQuery); the
monotone lift `PSyncFGRowTransport.mono` exists, but Accepted's chain uses it only at `le_rfl`. -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- The row gap is at least `2` at every ratio (`cF_ceil`: `4·cF r ≥ r + 6 ≥ 7`). -/
theorem AcceptanceAssumptions.two_le_cF {S : Setup} (A : AcceptanceAssumptions S) :
    2 ≤ cF A.rowRatio := by
  have := (cF_ceil A.rowRatio).1
  have := A.rowRatio.pos
  omega

/-- The timeout covers the gap-2 bound `6 ≤ δ_t` at every ratio. -/
theorem AcceptanceAssumptions.six_le_δt {S : Setup} (A : AcceptanceAssumptions S) :
    6 ≤ S.δt := by
  have := A.timeout
  have := A.two_le_cF
  omega

theorem finalWindow_offsets {S : Setup} (A : AcceptanceAssumptions S) :
    (finalWindow A).offsets = [0, cF A.rowRatio, 2 * cF A.rowRatio, 3 * cF A.rowRatio] := by rfl

theorem finalWindow_span {S : Setup} (A : AcceptanceAssumptions S) :
    (finalWindow A).span = 3 * cF A.rowRatio := by
  unfold Pattern.span
  rw [finalWindow_offsets]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

theorem accepted_catchUp_val (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_catchUp S A : Nat) = 19 := by rfl

theorem accepted_heal_val (S : Setup) (A : AcceptanceAssumptions S) (cap : Capability) (X : ℕ+) :
    accepted_heal S A cap X = (accepted_catchUp S A : Nat) + healMargin S X := by rfl

/-- **The coefficient inequality (★)** of the nonfinal reset envelope, at every capability: the
heal budget of `healthy_reset_fit` (`HealthyResetEnvelope`) at the named `R = healthyResetCoeff` and
`r = healthyResetSlack`. -/
theorem accepted_heal_ge_reset (S : Setup) (A : AcceptanceAssumptions S) (cap : Capability)
    (X : ℕ+) :
    (accepted_catchUp S A : Nat) + (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 26) +
      healthyResetSlack S X + 3 ≤ accepted_heal S A cap X := by
  rw [accepted_heal_val, healthyResetSlack_val]
  have := healMargin_ge_reset S X A.six_le_δt
  omega

/-- The final route's coefficient form `accepted_heal(final, X) ≥ C + M_f`,
`M_f = 20 L_drain + 8k + 28δ_t + 28X + 56` at `λ = 2Δ` and `L_drain = healthyDrainLen` (the
rise-round route, `healBoundCoeffRounds_at_two`). A budget for the final route, not a proof of its
reset. -/
theorem accepted_heal_ge_final (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    (accepted_catchUp S A : Nat) +
        (20 * healthyDrainLen S X + 8 * S.k + 28 * S.δt + 28 * (X : Nat) + 56) ≤
      accepted_heal S A .final X := by
  rw [accepted_heal_val, healMargin_val]

theorem accepted_latency_available (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .available X = 4 * (X : Nat) + 6 := by rfl

theorem accepted_latency_stable (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .stable X = 4 * (X : Nat) + 6 := by rfl

theorem accepted_latency_final (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .final X = 4 * ((X : Nat) + 3 * cF A.rowRatio) + 1 := by rfl

/-- For `Δ ≥ 1`, `19Δ` covers `18Δ + 1`, including safety's literal `+1`. -/
theorem accepted_catchUp_ge_sleepy (S : Setup) (A : AcceptanceAssumptions S) :
    19 ≤ (accepted_catchUp S A : Nat) := by
  rw [accepted_catchUp_val]

/-- The nonfinal latency covers `(4idx + 6)Δ`. -/
theorem accepted_latency_ge_sleepy (S : Setup) (A : AcceptanceAssumptions S)
    (cap : Capability) (idx : ℕ+) (hcap : cap = .available ∨ cap = .stable) :
    4 * (idx : Nat) + 6 ≤ accepted_latency S A cap idx := by
  rcases hcap with rfl | rfl
  · rw [accepted_latency_available]
  · rw [accepted_latency_stable]

theorem acceptanceContract_params_eq {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) :
    (acceptanceContract A C).params =
      { Params.standard C.catchUp (4 * S.k + 6)
        (4 * S.k - 5) C.heal C.latency with
        noSleep := 4 * S.k + 6, recovery := 9,
        rowRatio := A.rowRatio } := by rfl

theorem accepted_coefficients_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).catchUp = accepted_catchUp S A := by rfl

theorem accepted_coefficients_heal (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).heal = accepted_heal S A := by rfl

theorem accepted_coefficients_latency (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).latency = accepted_latency S A := by rfl

noncomputable abbrev K (S : Setup) (A : AcceptanceAssumptions S) :=
  acceptanceContract A (accepted_coefficients S A)

/-- The readiness duration of an acceptance contract with catch-up `≥ 19` covers `18Δ + 1`, for
any coefficient record `C`, so that it also serves the witnesses over `acceptanceContract A C`.
At `K S A` the premise is `accepted_catchUp_ge_sleepy`. -/
theorem cDur_ge_of_catchUp {S : Setup} (A : AcceptanceAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (C : AcceptanceCoefficients) (hC : 19 ≤ (C.catchUp : Nat))
    (r : (Sys (family S) V).Run) :
    18 * r.1.Δ + 1 ≤ (Sys (family S) V).cDur (acceptanceContract A C) r := by
  have hd : (1 : Time) ≤ r.1.Δ := r.1.Δ_pos
  have hc : (19 : Time) ≤ (C.catchUp : Nat) := by exact_mod_cast hC
  change 18 * r.1.Δ + 1 ≤ ((C.catchUp : Nat) : Time) * r.1.Δ
  nlinarith

/-- **The snapshot fit at readiness** for any coefficient record with catch-up `≥ 19`:
`c_z + Δp + 1 ≤ max ready 0 + 4Δp`, the `lo` condition of `snapshotCall_of_awake` at the frame
base `max ready 0 + 4Δp`. Generic in `C` as `cDur_ge_of_catchUp`; its instance at `K S A` is
`C := accepted_coefficients S A`, `hC := accepted_catchUp_ge_sleepy S A`. -/
theorem cutZ_fit_of_catchUp {S : Setup} (A : AcceptanceAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (C : AcceptanceCoefficients) (hC : 19 ≤ (C.catchUp : Nat))
    (r : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V) (g : Time) :
    Healing.cutZ (S.params (Model.pubOf r.1) hn).toParams g +
        (S.params (Model.pubOf r.1) hn).Δ + 1 ≤
      max ((Sys (family S) V).ready (acceptanceContract A C) g r) 0 +
        4 * (S.params (Model.pubOf r.1) hn).Δ := by
  have h := cDur_ge_of_catchUp A V C hC r
  have hΔ : (S.params (Model.pubOf r.1) hn).Δ = r.1.Δ := rfl
  exact Healing.cutZ_add_lt_ready_add _ g _ (by have := r.1.Δ_pos; rw [hΔ]; linarith)

end Consensus.Goldilocks.Refinement
end
