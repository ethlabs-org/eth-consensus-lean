module
public import ConsensusProblem.Regimes
public import Mathlib.Tactic

@[expose] public section

/-! # Numbers and regimes (L0 facts)

The standard thresholds are admissible; the healthy regime bounds the faults. -/

namespace Consensus

namespace Params

variable {Idx : Type}

/-- The standard thresholds are admissible. -/
theorem standard_admissible {catchUp lag budget : Nat} {heal latency : Capability → Idx → Nat}
    (h : 1 ≤ catchUp) (hb : 1 ≤ budget) :
    (standard catchUp lag budget heal latency).Admissible :=
  ⟨h, by norm_num [standard], by norm_num [standard], by norm_num [standard],
    by norm_num [standard], hb⟩

end Params

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] {p : EnvPoint V}

/-- Healthy bounds the faults: a set of more than `φ·n` honest validators
leaves fewer than `(1 − φ)·n` faulty. -/
theorem HealthyOn.faultsBelow {φ : ℚ} {g b : Time} (h : p.HealthyOn φ g b) :
    p.FaultsBelow (1 - φ) := by
  classical
  obtain ⟨H, hsub, ha, -⟩ := h
  have hc : H.card ≤ p.honest.card := Finset.card_le_card hsub
  have hsum : p.faulty.card + p.honest.card = Fintype.card V := by
    unfold faulty
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ p.honest
    omega
  have hc' : (H.card : ℚ) ≤ p.honest.card := by exact_mod_cast hc
  have hsum' : (p.faulty.card : ℚ) + p.honest.card = Fintype.card V := by exact_mod_cast hsum
  unfold FaultsBelow
  linarith

end EnvPoint

end Consensus

end
