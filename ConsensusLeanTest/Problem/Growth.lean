module
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Blocks.Facts
public import ConsensusLeanTest.Fixtures.Common
public import ConsensusLean.Spec.Problem.Properties
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

private theorem readyAt_eq (d : Time) (t : Time := 4) (ht : 0 ≤ t := by decide) :
    (point.retain d).readyAt 0 t = if 5 ≤ d then {2} else {0, 1, 2} := by
  classical
  ext v
  fin_cases v <;> by_cases hd : 5 ≤ d <;>
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt, EnvPoint.retain,
      EnvPoint.AwakeOnClosed, point, hd] <;>
      exact ⟨t, ht, le_add_of_nonneg_right (by decide), le_rfl⟩

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

/-- A finite look-ahead window is admitted even though charging terminal faults rejects it. -/
theorem sleepyOn_ahead_not_terminal :
    point.SleepyOn (1 / 2) 0 1 3 3 ∧
      ¬ (point.retain point.horizon).SleepyOn (1 / 2) 0 1 3 3 := by
  constructor
  · intro t ht htb
    have he : t = 3 := le_antisymm htb ht
    subst t
    rw [EnvPoint.ReadyAbove, readyAt_eq _ 3 (by decide)]
    norm_num [EnvPoint.lookAhead, EnvPoint.faultCount, EnvPoint.retain, point]
  · intro h
    have hh := h 3 le_rfl le_rfl
    change (point.retain 10).ReadyAbove (1 / 2) 0 3 at hh
    rw [EnvPoint.ReadyAbove, readyAt_eq _ 3 (by decide)] at hh
    norm_num [EnvPoint.faultCount, EnvPoint.retain, point] at hh

private theorem awakeAt_retained (d t : Time) :
    (point.retain d).awakeAt t = if 5 ≤ d then {2} else {0, 1, 2} := by
  ext v
  fin_cases v <;> by_cases hd : 5 ≤ d <;>
    simp [EnvPoint.awakeAt, EnvPoint.honestAt, EnvPoint.retain, point, hd]

private theorem lateWakers_retained (d : Time) :
    (point.retain d).lateWakers 3 4 = ∅ := by
  classical
  ext v
  simp only [EnvPoint.lateWakers, Finset.mem_sdiff, Finset.notMem_empty, iff_false,
    not_and]
  intro h hn
  obtain ⟨u, _, _, hv, ha⟩ := (Finset.mem_filter.mp h).2
  apply hn
  simp only [EnvPoint.awakeAt, Finset.mem_filter, EnvPoint.honestAt,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  exact ⟨hv, ha⟩

/-- The formation-time cohort passes, but charging the compromised cohort members rejects it. -/
theorem retained_cohort_rejected :
    (point.retain 4).CohortOn 3 4 ∧ ¬ (point.retain 5).CohortOn 3 4 := by
  constructor
  · rw [EnvPoint.CohortOn, lateWakers_retained, awakeAt_retained]
    norm_num [EnvPoint.retain, point]
  · rw [EnvPoint.CohortOn, lateWakers_retained, awakeAt_retained]
    norm_num [EnvPoint.retain, point]

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

/-- A third compromise crosses the strict one-third healthy threshold. -/
def threeFaultPoint : EnvPoint (Fin 7) where
  env := growthPoint.env
  faultyAt := fun t => if 5 ≤ t then {0, 1, 2} else {0, 1}
  faultyAt_mono := by
    intro a b hab
    dsimp only
    split_ifs with ha hb
    · exact Finset.Subset.refl _
    · exact False.elim (hb (ha.trans hab))
    · decide
    · exact Finset.Subset.refl _
  horizon := 8
  submit := fun _ _ => []

/-- Two-to-three faults among seven validators is rejected, beside the accepted control. -/
theorem threeFaultPoint_not_healthy : ¬ threeFaultPoint.HealthyOn (1 / 3) 0 8 := by
  intro h
  have hh := h.1
  norm_num [EnvPoint.faultCount, threeFaultPoint] at hh

/-- A rotating singleton has constant cardinality, but is not a permanent-compromise profile. -/
def rotatingFaults (t : Time) : Finset (Fin 3) := if t < 1 then {0} else {1}

/-- A cardinality bound cannot replace set monotonicity: rotation removes a compromised key. -/
theorem rotatingFaults_not_monotone : ¬ Monotone rotatingFaults := by
  intro h
  have hh := h (show (0 : Time) ≤ 1 by decide)
  have h0 : (0 : Fin 3) ∈ rotatingFaults 0 := by decide
  have := hh h0
  norm_num [rotatingFaults] at this

/-- The rotating profile still has exactly one faulty key at every time. -/
theorem rotatingFaults_card (t : Time) : (rotatingFaults t).card = 1 := by
  unfold rotatingFaults
  split_ifs <;> decide

/-- The two extracted keys together are a quorum of two, despite the singleton counts. -/
theorem rotatingFaults_union_quorum : (rotatingFaults 0 ∪ rotatingFaults 1).card = 2 := by
  decide

/-- Reads by key zero are empty while honest, then disagree across outputs after compromise. -/
def historicalReads : Trace (Fin 7) Nat Bool :=
  ⟨growthPoint, 8, fun i => (i : Int),
    fun g v i => if v = 0 ∧ 2 ≤ i then
      (if g then (if i = 2 then [1] else [3]) else [2]) else []⟩

/-- The honest-reader monotonicity contract ignores arbitrary reads after compromise. -/
theorem historicalReads_monotone (g : Bool) : historicalReads.Monotone g 0 := by
  intro v i j _ _ _ hi hj
  have empty_read (k : Nat) (hk : growthPoint.HonestAt v (k : Int)) :
      historicalReads.read g v k = [] := by
    by_cases hv : v = 0
    · subst v
      have ht : ¬ (2 : Int) ≤ k := by
        intro ht
        apply hk
        simp [growthPoint, ht]
      simp [historicalReads, show ¬ 2 ≤ k by omega]
    · simp [historicalReads, hv]
  rw [empty_read i hi, empty_read j hj]

/-- Nesting also only constrains the reads made while honest. -/
theorem historicalReads_nested : historicalReads.Nested true false := by
  intro v i _ hv
  by_cases h : v = 0 ∧ 2 ≤ i
  · rcases h with ⟨rfl, hi⟩
    exfalso
    apply hv
    simp [historicalReads, growthPoint, show (2 : Int) ≤ i by omega]
  · simp [historicalReads, h]

/-- Replacing honesty at each cut by honesty at zero would incorrectly require these reads. -/
theorem historicalReads_not_initially_honest_monotone :
    ¬ historicalReads.MonotoneAmong (fun v _ => growthPoint.HonestAt v 0) true 0 := by
  intro h
  have hh := h 0 2 3 (by constructor <;> decide) (by decide)
    (by constructor <;> decide)
    (by simp [EnvPoint.HonestAt, growthPoint]) (by simp [EnvPoint.HonestAt, growthPoint])
  change [1] <+: [3] at hh
  simp at hh

/-- The initially honest reader's post-compromise outputs need not nest either. -/
theorem historicalReads_not_initially_honest_nested :
    ¬ ∀ v i, i ≤ historicalReads.cuts → growthPoint.HonestAt v 0 →
      historicalReads.read true v i <+: historicalReads.read false v i := by
  intro h
  have hh := h 0 2 (by decide) (by simp [EnvPoint.HonestAt, growthPoint])
  change [1] <+: [2] at hh
  simp at hh

end Consensus.Shape.Tests.Growth
end
