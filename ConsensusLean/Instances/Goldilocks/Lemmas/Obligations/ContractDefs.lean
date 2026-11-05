module
public import ConsensusLean.Instances.Goldilocks.AsChainShape
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the obligations contract and its coefficients

The characterising lemmas of the fixed assumptions (`ContractAssumptions`: the FG delay in slots
`fgSlots`, its FG delay bound `fgDelay = 4·fgSlots − 6`, and the timeout), the final pattern
(`finalWindow`, gap `fgSlots`), the coefficients (`contract_catchUp`,
`contract_heal`, `contract_latency`) and the contract `goldilocksContract`, all defined in the
statement module `Statements/Obligations`, and the abbreviation `K`. The FG transport is
instantiated at the actual protocol FG delay `protoFGDelay` (HSSharedRun, HSSharedOfQuery); the
monotone lift `PSyncFGAttTransport.mono` exists, but the obligations proof uses it only at
`le_rfl`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Blocks Shape

/-- The contract's FG delay bound is `4·fgSlots − 6`. -/
theorem _root_.Consensus.Goldilocks.ContractAssumptions.fgDelay_val {S : Setup}
    (A : ContractAssumptions S) : (A.fgDelay : Nat) = 4 * A.fgSlots - 6 := by rfl

/-- The healthy regime's FG delay bound of `K S A`, read in slots: `ΔF ≤ (4·fgSlots − 6)·Δ` is
`6Δ + ΔF ≤ 4Δ·fgSlots`. -/
theorem fgDelay_bound_iff {S : Setup} (A : ContractAssumptions S) (Δ ΔF : Time) :
    ΔF ≤ (A.fgDelay : Time) * Δ ↔ 6 * Δ + ΔF ≤ 4 * Δ * (A.fgSlots : Time) := by
  have h : ((A.fgDelay : Nat) : Time) + 6 = 4 * (A.fgSlots : Time) := by
    have := A.two_le_fgSlots
    have : (A.fgDelay : Nat) + 6 = 4 * A.fgSlots := by rw [A.fgDelay_val]; omega
    exact_mod_cast this
  have h' : 4 * Δ * (A.fgSlots : Time) = ((A.fgDelay : Nat) : Time) * Δ + 6 * Δ := by
    rw [show 4 * Δ * (A.fgSlots : Time) = Δ * (4 * (A.fgSlots : Time)) by ring, ← h]
    ring
  change ΔF ≤ ((A.fgDelay : Nat) : Time) * Δ ↔ _
  rw [h']
  constructor <;> intro <;> linarith

/-- The timeout covers the gap-2 bound `6 ≤ δ_t` for every FG gap. -/
theorem _root_.Consensus.Goldilocks.ContractAssumptions.six_le_δt {S : Setup}
    (A : ContractAssumptions S) :
    6 ≤ S.δt := by
  have := A.timeout
  have := A.two_le_fgSlots
  omega

theorem finalWindow_offsets {S : Setup} (A : ContractAssumptions S) :
    (finalWindow A).offsets = [0, A.fgSlots, 2 * A.fgSlots, 3 * A.fgSlots] := by rfl

theorem finalWindow_span {S : Setup} (A : ContractAssumptions S) :
    (finalWindow A).span = 3 * A.fgSlots := by
  unfold Pattern.span
  rw [finalWindow_offsets]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

theorem contract_catchUp_val (S : Setup) (A : ContractAssumptions S) :
    (contract_catchUp S A : Nat) = 19 := by rfl

theorem contract_heal_val (S : Setup) (A : ContractAssumptions S) (cap : Capability) (X : ℕ+) :
    contract_heal S A cap X = (contract_catchUp S A : Nat) + healMargin S X := by rfl

/-- **The coefficient inequality (★)** of the nonfinal reset envelope, at every capability: the
heal budget of `healthy_reset_fit` (`HealthyResetEnvelope`) at the named `R = healthyResetCoeff` and
`r = healthyResetSlack`. -/
theorem contract_heal_ge_reset (S : Setup) (A : ContractAssumptions S) (cap : Capability)
    (X : ℕ+) :
    (contract_catchUp S A : Nat) + (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 26) +
      healthyResetSlack S X + 3 ≤ contract_heal S A cap X := by
  rw [contract_heal_val, healthyResetSlack_val]
  have := healMargin_ge_reset S X A.six_le_δt
  omega

/-- The final route's coefficient form `contract_heal(final, X) ≥ C + M_f`,
`M_f = 20 L_drain + 8k + 28δ_t + 28X + 56` at `λ = 2Δ` and `L_drain = healthyDrainLen` (the
rise-round route, `healBoundCoeffRounds_at_two`). A budget for the final route, not a proof of its
reset. -/
theorem contract_heal_ge_final (S : Setup) (A : ContractAssumptions S) (X : ℕ+) :
    (contract_catchUp S A : Nat) +
        (20 * healthyDrainLen S X + 8 * S.k + 28 * S.δt + 28 * (X : Nat) + 56) ≤
      contract_heal S A .final X := by
  rw [contract_heal_val, healMargin_val]

theorem contract_latency_available (S : Setup) (A : ContractAssumptions S) (X : ℕ+) :
    contract_latency S A .available X = 4 * (X : Nat) + 6 := by rfl

theorem contract_latency_stable (S : Setup) (A : ContractAssumptions S) (X : ℕ+) :
    contract_latency S A .stable X = 4 * (X : Nat) + 6 := by rfl

theorem contract_latency_final (S : Setup) (A : ContractAssumptions S) (X : ℕ+) :
    contract_latency S A .final X = 4 * ((X : Nat) + 3 * A.fgSlots) + 1 := by rfl

/-- For `Δ ≥ 1`, `19Δ` covers `18Δ + 1`, including safety's literal `+1`. -/
theorem contract_catchUp_ge_sleepy (S : Setup) (A : ContractAssumptions S) :
    19 ≤ (contract_catchUp S A : Nat) := by
  rw [contract_catchUp_val]

/-- The nonfinal latency covers `(4idx + 6)Δ`. -/
theorem contract_latency_ge_sleepy (S : Setup) (A : ContractAssumptions S)
    (cap : Capability) (idx : ℕ+) (hcap : cap = .available ∨ cap = .stable) :
    4 * (idx : Nat) + 6 ≤ contract_latency S A cap idx := by
  rcases hcap with rfl | rfl
  · rw [contract_latency_available]
  · rw [contract_latency_stable]

theorem goldilocksContract_params_eq {S : Setup} (A : ContractAssumptions S)
    (C : ContractCoefficients) :
    (goldilocksContract A C).params =
      { Params.standard C.catchUp (4 * S.k + 6)
        (4 * S.k - 5) C.heal C.latency with
        noSleep := 4 * S.k + 6, recovery := 9,
        fgDelay := A.fgDelay } := by rfl

theorem contract_coefficients_catchUp (S : Setup) (A : ContractAssumptions S) :
    (contract_coefficients S A).catchUp = contract_catchUp S A := by rfl

theorem contract_coefficients_heal (S : Setup) (A : ContractAssumptions S) :
    (contract_coefficients S A).heal = contract_heal S A := by rfl

theorem contract_coefficients_latency (S : Setup) (A : ContractAssumptions S) :
    (contract_coefficients S A).latency = contract_latency S A := by rfl

noncomputable abbrev K (S : Setup) (A : ContractAssumptions S) :=
  goldilocksContract A (contract_coefficients S A)

/-- The readiness duration of an obligations contract with catch-up `≥ 19` covers `18Δ + 1`, for
any coefficient record `C`, so that it also serves the witnesses over `goldilocksContract A C`.
At `K S A` the premise is `contract_catchUp_ge_sleepy`. -/
theorem cDur_ge_of_catchUp {S : Setup} (A : ContractAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (C : ContractCoefficients) (hC : 19 ≤ (C.catchUp : Nat))
    (r : (Sys (goldilocks S) V).Run) :
    18 * r.1.ΔAC + 1 ≤ (Sys (goldilocks S) V).cDur (goldilocksContract A C) r := by
  have hd : (1 : Time) ≤ r.1.ΔAC := r.1.ΔAC_pos
  have hc : (19 : Time) ≤ (C.catchUp : Nat) := by exact_mod_cast hC
  change 18 * r.1.ΔAC + 1 ≤ ((C.catchUp : Nat) : Time) * r.1.ΔAC
  nlinarith

/-- **The snapshot fit at readiness** for any coefficient record with catch-up `≥ 19`:
`c_z + Δp + 1 ≤ max ready 0 + 4Δp`, the `lo` condition of `snapshotCall_of_awake` at the frame
base `max ready 0 + 4Δp`. Generic in `C` as `cDur_ge_of_catchUp`; its instance at `K S A` is
`C := contract_coefficients S A`, `hC := contract_catchUp_ge_sleepy S A`. -/
theorem cutZ_fit_of_catchUp {S : Setup} (A : ContractAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (C : ContractCoefficients) (hC : 19 ≤ (C.catchUp : Nat))
    (r : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V) (g : Time) :
    Healing.cutZ (S.params (Model.pubOf r.1) hn).toParams g +
        (S.params (Model.pubOf r.1) hn).Δ + 1 ≤
      max ((Sys (goldilocks S) V).ready (goldilocksContract A C) g r) 0 +
        4 * (S.params (Model.pubOf r.1) hn).Δ := by
  have h := cDur_ge_of_catchUp A V C hC r
  have hΔ : (S.params (Model.pubOf r.1) hn).Δ = r.1.ΔAC := rfl
  exact Healing.cutZ_add_lt_ready_add _ g _ (by have := r.1.ΔAC_pos; rw [hΔ]; linarith)

end Consensus.Goldilocks.Obligations
end
