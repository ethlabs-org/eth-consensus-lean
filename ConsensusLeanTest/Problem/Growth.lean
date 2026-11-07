module
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Blocks.Facts
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

public section

/-! # Growing-fault participation and proposer scopes

Small profiles exercise corruption inside a look-ahead and after an honest
read. These tests do not assume a protocol's correctness. -/

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

end
