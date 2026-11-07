module
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Blocks.Facts
public import ConsensusLeanTest.Fixtures.Common
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
@[expose] public section

/-! # Multiple permanent compromises

The profile grows twice within the healthy claim window, with constant intervals
between compromises. A constant profile is kept as a control.
-/

namespace Consensus.Tests.Growth

/-- Two faults at time five, none before; three validators are always awake. -/
def point : EnvPoint (Fin 5) where
  env := ⟨1, by decide, 1, by decide, fun v _ => decide (v.val < 3)⟩
  faultyAt := fun t => if 5 ≤ t then {0, 1} else ∅
  faultyAt_mono := by
    intro a b hab
    by_cases ha : 5 ≤ a
    · simp only [ite_eq_left ha, ite_eq_left (ha.trans hab)]
      exact Finset.Subset.refl _
    · simp only [ite_eq_right ha]
      exact Finset.empty_subset _
  horizon := 10
  submit := fun _ _ => []

theorem ready_before_compromise : point.Ready 0 0 4 := by
  constructor
  · simp [EnvPoint.HonestAt, point]
  · intro u _ _; rfl

theorem not_honest_at_compromise : ¬ point.HonestAt 0 5 := by
  simp [EnvPoint.HonestAt, point]

private theorem readyAt_eq (d : Time) :
    (point.retain d).readyAt 0 4 = if 5 ≤ d then {2} else {0, 1, 2} := by
  classical
  ext v
  fin_cases v <;> by_cases hd : 5 ≤ d <;>
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt, EnvPoint.retain,
      EnvPoint.AwakeOnClosed, point, hd] <;> exact ⟨3, le_rfl, by decide⟩

/-- The current partition admits three supporters against zero faults. -/
theorem current_budget : point.ReadyAbove (1 / 2) 0 4 := by
  have he : point.readyAt 0 4 = (point.retain 4).readyAt 0 4 := by
    classical
    ext v
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt, EnvPoint.retain,
      EnvPoint.AwakeOnClosed, point]
  rw [EnvPoint.ReadyAbove, he, readyAt_eq]
  norm_num [EnvPoint.faultCount, point]

/-- Charging the two compromised supporters at the consumption time rejects
the same formation-time support. -/
theorem lookAhead_rejects_compromised_support : ¬ point.SleepyOn (1 / 2) 0 1 4 4 := by
  intro h
  have hh := h 4 le_rfl le_rfl
  rw [EnvPoint.ReadyAbove, readyAt_eq] at hh
  norm_num [EnvPoint.retain, EnvPoint.lookAhead, EnvPoint.faultCount, point] at hh

/-- A prefix ending before compromise reads only the earlier faults. -/
theorem prefix_budget :
    ({ point with horizon := 4 } : EnvPoint (Fin 5)).SleepyOn (1 / 2) 0 1 4 4 := by
  intro t ht htb
  have he : t = 4 := le_antisymm htb ht
  subst t
  have hr : ({ point with horizon := 4 } : EnvPoint (Fin 5)).retain
      (({ point with horizon := 4 } : EnvPoint (Fin 5)).lookAhead 1 4) =
      { point.retain 4 with horizon := 4 } := by rfl
  rw [hr, EnvPoint.ReadyAbove]
  have he : ({ point.retain 4 with horizon := 4 } : EnvPoint (Fin 5)).readyAt 0 4 =
      (point.retain 4).readyAt 0 4 := by rfl
  rw [he, readyAt_eq]
  norm_num [EnvPoint.faultCount, EnvPoint.retain, point]

end Consensus.Tests.Growth

namespace Consensus.Shape.Tests.Growth

/-- Seven awake validators; key zero is compromised at two, key one at five. -/
def growthPoint : EnvPoint (Fin 7) where
  env := ⟨1, by decide, 1, by decide, fun _ _ => true⟩
  faultyAt := fun t => (if 2 ≤ t then {0} else ∅) ∪ (if 5 ≤ t then {1} else ∅)
  faultyAt_mono := by
    intro a b hab
    apply Finset.union_subset_union
    · split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · exact Finset.empty_subset _
      · exact Finset.Subset.refl _
    · split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · exact Finset.empty_subset _
      · exact Finset.Subset.refl _
  horizon := 8
  submit := fun _ _ => []

/-- Two strict increases occur at different times inside the healthy window `[0, 8]`. -/
theorem growthPoint_strict_growth :
    ∃ t₀ t₁ t₂ : Time, 0 ≤ t₀ ∧ t₀ < t₁ ∧ t₁ < t₂ ∧ t₂ ≤ growthPoint.horizon ∧
      growthPoint.faultyAt t₀ ⊂ growthPoint.faultyAt t₁ ∧
      growthPoint.faultyAt t₁ ⊂ growthPoint.faultyAt t₂ := by
  exact ⟨0, 2, 5, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Two compromises among seven validators remain below one third. -/
theorem growthPoint_healthy : growthPoint.HealthyOn (1 / 3) 0 8 := by
  exact ⟨by norm_num [EnvPoint.faultCount, growthPoint], fun _ _ _ _ _ => rfl⟩

/-- The same healthy verdict holds on the constant two-fault control. -/
theorem constantPoint_healthy : (growthPoint.retain 8).HealthyOn (1 / 3) 0 8 := by
  exact ⟨by norm_num [EnvPoint.faultCount, EnvPoint.retain, growthPoint],
    fun _ _ _ _ _ => rfl⟩

/-- The control has constant faults, unlike the two-increase profile. -/
theorem constantPoint_constant : (growthPoint.retain 8).ConstantFaults := fun _ => rfl

end Consensus.Shape.Tests.Growth
end
