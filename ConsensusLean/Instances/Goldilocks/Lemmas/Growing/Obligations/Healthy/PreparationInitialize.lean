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
private theorem contract_heal_ge_reset_late_within (cap : Capability) (X : ℕ+) (L : Nat) :
    (contract_catchUp S A : Nat) + (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 34) + 3 +
      5 * L ≤ contract_heal S A cap X + 5 * L := by
  rw [contract_heal_val, healMargin_val, healthyResetCoeff_val]
  have := A.six_le_δt
  omega

set_option linter.unusedVariables false in
/-- An actual reset seed, a base slot and a repairing opening before the heal deadline, with `8Δ`
of the heal margin to spare after the reserve: the query is at most `ready + (R + 8k + 20)Δ` and the
heal point at least `ready + (R + 8k + 4X + 34)Δ + 2`. -/
theorem healthy_preparation_initialize_late_at
    (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index Q.ready Q.heal Q.run)
    {sign : Fin Q.params.n → Time → Bool}
    (hcal : Q.trace.SignCalendarAt (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys sign)
    {Gs : Nat} (hgap : SignGapAt Q.params.toParams sign Gs 0)
    (hδG : 3 + (Gs + 3) / 4 ≤ Q.params.toParams.fg.δt)
    (hGs : (contract_catchUp S A : Nat) +
        (healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 34) + 3 + 5 * Gs ≤
      contract_heal S A Q.cap Q.index)
    (hGsT : 4 * A.fgSlots + A.releaseGap + Gs ≤ 4 * S.δt)
    (hcover : HealthyQueryCover S A V Q) :
    ∃ W : HealthyBaseTimingAt S A V Q,
        ∃ D : HealthyPreparationScheduleAt
        S A V Q W,
      D.query + (4 * (Q.index : Time) + 14) * Q.params.Δ + 2 ≤ Q.heal := by
  obtain ⟨ΔF, a, hreset, ha⟩ :=
    healthy_preparation_reset_at S A V Q hb hp hcal hgap hδG hGs hGsT hcover
  obtain ⟨v, r, l, O, hO, hra, hla⟩ := hreset.reset_seed_at
  obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := hreset.reset
  have ha0 : 0 ≤ a := hka ▸ hreset.run.time_nonneg k
  have hD0 : (0 : Time) ≤ Q.params.Δ := Q.params.toParams.hΔ.le
  have hheal : (Sys (goldilocks S) V).heal (K S A) Q.cap Q.index Q.gst
      Q.run = Q.heal := rfl
  have hready : (Sys (goldilocks S) V).ready (K S A) Q.gst Q.run =
      Q.ready := rfl
  have hB' := healthy_heal_margin S A V Q.run Q.hn Q.cap Q.index Q.gst
    (M := healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 34 + 5 * Gs)
    (by omega)
  push_cast at hB'
  have hGD : (0 : Time) ≤ (Gs : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hD0
  obtain ⟨w, hw, hq⟩ := healthy_preparation_timing_within S A V Q.run Q.hn Q.cap Q.index Q.gst
    (5 * ((Gs : Time) * Q.params.Δ)) (by linarith only [hGD])
    (by linarith only [hB', hD0])
  simp only [hheal, hready] at hB' hq
  refine ⟨⟨w, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩,
    ⟨a, ΔF, _, hreset, v, r, l, O, hO, hra, hla, _, le_rfl,
      by linarith only [hq a l ha0 ha hla, hB', hD0]⟩, ?_⟩
  dsimp only
  linarith only [hq a l ha0 ha hla, hB']

/-- An actual reset seed, a base slot and a repairing opening before the heal deadline
(`healthy_preparation_initialize_late_at`). -/
theorem healthy_preparation_initialize_at
    (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog
      (shapeProgress (goldilocks S) V)
      (K S A) Q.cap Q.index Q.ready Q.heal Q.run)
    {sign : Fin Q.params.n → Time → Bool}
    (hcal : Q.trace.SignCalendarAt (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.keys sign)
    {Gs : Nat} (hgap : SignGapAt Q.params.toParams sign Gs 0)
    (hδG : 3 + (Gs + 3) / 4 ≤ Q.params.toParams.fg.δt)
    (hGs : (contract_catchUp S A : Nat) +
        (healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 34) + 3 + 5 * Gs ≤
      contract_heal S A Q.cap Q.index)
    (hGsT : 4 * A.fgSlots + A.releaseGap + Gs ≤ 4 * S.δt)
    (hcover : HealthyQueryCover S A V Q) :
    ∃ W : HealthyBaseTimingAt S A V Q,
        Nonempty (HealthyPreparationScheduleAt
        S A V Q W) :=
  let ⟨W, D, _⟩ := healthy_preparation_initialize_late_at S A V Q h0 hb hp hcal hgap hδG hGs
    hGsT hcover
  ⟨W, ⟨D⟩⟩

end Consensus.Goldilocks.Obligations.Growing

end
