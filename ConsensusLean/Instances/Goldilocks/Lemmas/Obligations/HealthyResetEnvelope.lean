module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ProposerGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HSSharedRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Drain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyPreparationTiming
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the window fit of a healthy preparation query

`healthy_reset_fit`: for a `HealthyPreparationQuery`, `ready + R·Δ + ρ ≤ heal`, where
`R = healthyResetCoeff` and `ρ = healthyResetSlack` are the named parameter-only coefficients
(`ResetCoefficients`), from the coefficient inequality `contract_heal_ge_reset` alone. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The window fit before heal**: `ready + R·Δ + r ≤ heal` at every query, from the
coefficient inequality `contract_heal_ge_reset` alone. It gives `H ≥ C + (R + r) + 3`, so
`healthy_heal_margin` gives `ready + (R + r)·Δ + 2 ≤ heal`, and `r ≤ r·Δ` at `Δ ≥ 1`. -/
theorem healthy_reset_fit (Q : HealthyPreparationQuery S A V) :
    Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      (healthyResetSlack S Q.index : Time) ≤ Q.heal := by
  have h := healthy_heal_margin S A V Q.run Q.hn Q.cap Q.index Q.gst
    (M := healthyResetCoeff S Q.index + healthyResetSlack S Q.index)
    (by have := contract_heal_ge_reset S A Q.cap Q.index; omega)
  have hd : (1 : Time) ≤ Q.params.Δ := Q.run.1.ΔAC_pos
  have hr0 : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  push_cast at h
  linarith only [h, mul_nonneg hr0 (sub_nonneg.mpr hd)]

end Consensus.Goldilocks.Obligations

end
