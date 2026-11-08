module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationReset
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The joint healthy preparation schedule under growing faults -/

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

set_option linter.unusedVariables false in
/-- An actual reset seed, a base slot and a repairing opening before the heal deadline, with eight
slots of the heal margin to spare after the reserve: the query is at most `ready + (R + 8k + 20)Δ`
and the heal point at least `ready + (R + 8k + 4X + 34)Δ + 2`. -/
theorem healthy_preparation_initialize_late_at (Q : HealthyPreparationQueryAt S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.bound)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTimingAt S A V Q, ∃ D : HealthyPreparationScheduleAt S A V Q W,
      D.query + (4 * (Q.index : Time) + 14) * Q.params.Δ + 1 ≤ Q.heal := by
  obtain ⟨ΔF, a, hreset, ha⟩ := healthy_preparation_reset_at S A V Q hb hp
  obtain ⟨v, r, l, O, hO, hra, hla⟩ := hreset.reset_seed_at
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hD0 : (0 : Time) ≤ Q.params.Δ := zero_le_one.trans hd
  have hΔ : Q.params.Δ = Q.run.1.ΔAC := rfl
  have hready :
      Q.ready = max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
    change max Q.gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hheal : Q.heal = max Q.gst 0 + (contract_heal S A Q.cap Q.index : Time) * Q.run.1.ΔAC := by
    change max Q.gst 0 + ((contract_coefficients S A).heal Q.cap Q.index : Time) * Q.run.1.ΔAC = _
    rw [contract_coefficients_heal]
  have hC : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hkk : (Q.params.k : Time) = S.k := rfl
  rw [healthyResetSlack_val] at ha
  push_cast at ha
  set B : Time := (healthyResetCoeff S Q.index : Time) + 8 * (S.k : Time) +
    4 * ((Q.index : Nat) : Time) + 26 with hBdef
  have hB : Q.ready + B * Q.params.Δ + 2 ≤ Q.heal := by
    have hH : ((contract_catchUp S A : Nat) : Time) + B + 3 ≤
        (contract_heal S A Q.cap Q.index : Time) := by
      have h1 := (Nat.cast_le (α := Time)).mpr (contract_heal_ge_reset S A Q.cap Q.index)
      rw [healthyResetSlack_val] at h1
      push_cast at h1
      rw [hBdef]
      linarith only [h1]
    rw [hready, hheal, hΔ]
    linarith only [mul_le_mul_of_nonneg_right hH (zero_le_one.trans hd), hd]
  have hB' : Q.ready + (B + 8) * Q.params.Δ + 2 ≤ Q.heal := by
    have hH : ((contract_catchUp S A : Nat) : Time) + (B + 8) + 3 ≤
        (contract_heal S A Q.cap Q.index : Time) := by
      have h1 := (Nat.cast_le (α := Time)).mpr (contract_heal_ge_reset_late S A Q.cap Q.index)
      push_cast at h1
      rw [hBdef]
      linarith only [h1]
    rw [hready, hheal, hΔ]
    linarith only [mul_le_mul_of_nonneg_right hH (zero_le_one.trans hd), hd]
  have hR0 : (24 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith only [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hX0 : (0 : Time) ≤ ((Q.index : Nat) : Time) := Nat.cast_nonneg _
  have hr0 : 0 ≤ Q.ready := by
    rw [hready]
    exact add_nonneg (add_nonneg (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) hD0))
      zero_le_one
  have hgr : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.ready := by
    change max Q.gst 0 + _ ≤ _
    rw [hready, hΔ]
    linarith only [mul_le_mul_of_nonneg_right hC (zero_le_one.trans hd), hd]
  have hts (s j : Nat) : Q.params.ts (s + j : Nat) = Q.params.ts s + 4 * Q.params.Δ * j := by
    simp only [SA.SAParams.ts]; push_cast; ring
  set w : Nat := Q.params.slot Q.ready + 1 with hw
  have hw0 : Q.params.ts (Q.params.slot Q.ready : Nat) ≤ Q.ready :=
    (SA.ts_le_iff_le_slot Q.params hr0 _).mpr le_rfl
  have hw1 : Q.ready < Q.params.ts w := by
    have h := (SA.ts_le_iff_le_slot Q.params hr0 (w : Int)).not.mpr (by rw [hw]; push_cast; omega)
    exact lt_of_not_ge h
  have hw2 : Q.params.ts w ≤ Q.ready + 4 * Q.params.Δ := by
    rw [hw, hts]; push_cast; linarith only [hw0]
  obtain ⟨⟨_, k, _, _, _, _, hka⟩, _⟩ := hreset.reset
  have ha0 : 0 ≤ a := hka ▸ hreset.run.time_nonneg k
  have hsa : Q.params.ts (Q.params.slot a : Nat) ≤ a :=
    (SA.ts_le_iff_le_slot Q.params ha0 _).mpr le_rfl
  have hkD : (0 : Time) ≤ (S.k : Time) * Q.params.Δ := mul_nonneg (Nat.cast_nonneg _) hD0
  have hdrain : Healing.drainTime Q.params a ≤ a + (8 * (S.k : Time) + 20) * Q.params.Δ := by
    rw [Healing.drainTime_eq, show Q.params.slot a + 2 * Q.params.k + 5 =
      Q.params.slot a + (2 * S.k + 5) from rfl, hts]
    push_cast; linarith only [hsa]
  have hla' : l ≤ Q.params.slot a := hla
  have hseed : Q.params.ts (l + 1 : Nat) ≤ a + 4 * Q.params.Δ := by
    have hl : ((l + 1 : Nat) : Int) ≤ (Q.params.slot a : Int) + 1 := by push_cast; omega
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg zero_le_four hD0)
    simp only [SA.SAParams.ts] at hsa ⊢
    linarith only [this, hsa]
  have hRD := mul_le_mul_of_nonneg_right hR0 hD0
  have hq : max Q.ready (max (Healing.drainTime Q.params a) (max (Q.params.ts w)
      (max (SA.gbar Q.gst + 4 * Q.params.Δ) (max 0 (Q.params.ts (l + 1 : Nat)))))) ≤
      Q.ready + ((healthyResetCoeff S Q.index : Time) + 8 * (S.k : Time) + 20) * Q.params.Δ :=
    max_le (by linarith only [hRD, hkD, hD0]) (max_le (by linarith only [hdrain, ha])
      (max_le (by linarith only [hw2, hRD, hkD, hD0])
        (max_le (by linarith only [hgr, hRD, hkD, hD0])
          (max_le (by linarith only [hr0, hRD, hkD, hD0])
            (by linarith only [hseed, ha, hkD, hD0])))))
  have hXD : (0 : Time) ≤ ((Q.index : Nat) : Time) * Q.params.Δ := mul_nonneg hX0 hD0
  rw [hBdef] at hB hB'
  refine ⟨⟨w, hw1.le, by linarith only [hw2, hB, hRD, hkD, hXD, hD0],
    by rw [hts]; push_cast; linarith only [hw2, hB, hRD, hkD, hXD, hD0],
    by rw [hts, hkk]; linarith only [hw2, hB, hRD, hkD, hXD, hD0],
    by rw [hts]; push_cast; linarith only [hw2, hB, hRD, hkD, hXD, hD0]⟩,
    ⟨a, ΔF, hreset, v, r, l, O, hO, hra, hla, _, le_rfl, by linarith only [hq, hB]⟩, ?_⟩
  dsimp only
  linarith only [hq, hB']

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
