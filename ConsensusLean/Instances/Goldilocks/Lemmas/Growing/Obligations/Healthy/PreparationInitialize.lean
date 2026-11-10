module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationReset
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyPreparationTiming
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The joint healthy preparation schedule under growing faults -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The coefficient inequality with `8Δ` more**: the heal margin exceeds the reset reserve
`R + 8k + 4X + 29` by `4δ_t − 13 ≥ 11` (at `δ_t ≥ 6`), so the reserve `+ 8` still fits. -/
private theorem contract_heal_ge_reset_late (cap : Capability) (X : ℕ+) :
    (contract_catchUp S A : Nat) + (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 34) + 3 ≤
      contract_heal S A cap X := by
  rw [contract_heal_val, healMargin_val, healthyResetCoeff_val]
  have := A.six_le_δt
  omega

set_option linter.unusedVariables false in
/-- An actual reset seed, a base slot and a repairing opening before the heal deadline, with `8Δ`
of the heal margin to spare after the reserve: the query is at most `ready + (R + 8k + 20)Δ` and the
heal point at least `ready + (R + 8k + 4X + 34)Δ + 2`. -/
theorem healthy_preparation_initialize_late_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTimingAt S A V Q, ∃ D : HealthyPreparationScheduleAt S A V Q W,
      D.query + (4 * (Q.index : Time) + 14) * Q.params.Δ + 2 ≤ Q.heal := by
  obtain ⟨ΔF, a, hreset, ha⟩ := healthy_preparation_reset_at S A V Q hb hp
  obtain ⟨v, r, l, O, hO, hra, hla⟩ := hreset.reset_seed_at
  obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := hreset.reset
  have ha0 : 0 ≤ a := hka ▸ hreset.run.time_nonneg k
  have hD0 : (0 : Time) ≤ Q.params.Δ := Q.params.toParams.hΔ.le
  have hB' := healthy_heal_margin S A V Q.run Q.hn Q.cap Q.index Q.gst
    (contract_heal_ge_reset_late S A Q.cap Q.index)
  push_cast at hB'
  obtain ⟨w, hw, hq⟩ := healthy_preparation_timing S A V Q.run Q.hn Q.cap Q.index Q.gst
    (by linarith only [hB', hD0])
  refine ⟨⟨w, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩,
    ⟨a, ΔF, hreset, v, r, l, O, hO, hra, hla, _, le_rfl,
      by linarith only [hq a l ha0 ha hla, hB', hD0]⟩, ?_⟩
  dsimp only
  linarith only [hq a l ha0 ha hla, hB']

/-- An actual reset seed, a base slot and a repairing opening before the heal deadline
(`healthy_preparation_initialize_late_at`). -/
theorem healthy_preparation_initialize_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTimingAt S A V Q, Nonempty (HealthyPreparationScheduleAt S A V Q W) :=
  let ⟨W, D, _⟩ := healthy_preparation_initialize_late_at S A V Q h0 hb hp
  ⟨W, ⟨D⟩⟩

end Consensus.Goldilocks.Obligations.Growing

end
