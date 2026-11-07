module
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Blocks.Facts
public import ConsensusLeanTest.Fixtures.Common
public import ConsensusLean.Spec.Problem.Properties
public import ConsensusLean.Lemmas.Model.Constant
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import ConsensusLean.Lemmas.Tactic.Linarith
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

/-- Awake support rotates at compromise, so every current budget passes. -/
def rotatingSupport : EnvPoint (Fin 5) :=
  { point with env := ⟨1, by decide, 1, by decide,
      fun v t => decide (v.val < 3 ∨ 4 ≤ t)⟩ }

theorem rotatingSupport_current_budget (t : Time) (ht : 0 ≤ t) (hb : t ≤ 10) :
    rotatingSupport.ReadyAbove (1 / 2) 0 t := by
  classical
  have hr : rotatingSupport.readyAt 0 t =
      if 5 ≤ t then {2, 3, 4} else {0, 1, 2} := by
    ext v
    fin_cases v <;> interval_cases t <;>
      norm_num [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt,
        EnvPoint.AwakeOnClosed, rotatingSupport, point] <;>
      first
      | solve | intro u hu hv; linarith
      | solve | exact ⟨0, by decide, by decide, by decide⟩
      | solve | exact ⟨1, by decide, by decide, by decide⟩
      | solve | exact ⟨2, by decide, by decide, by decide⟩
      | solve | exact ⟨3, by decide, by decide, by decide⟩
  rw [EnvPoint.ReadyAbove, hr]
  split_ifs <;> norm_num [EnvPoint.faultCount, rotatingSupport, point, *]

/-- Replacing the window budget by every current budget would admit lost support. -/
theorem rotatingSupport_lookAhead_rejected :
    ¬ rotatingSupport.SleepyOn (1 / 2) 0 1 4 5 := by
  intro h
  have hh := h 4 le_rfl (by decide)
  have hr : (rotatingSupport.retain (rotatingSupport.lookAhead 1 4)).readyAt 0 4 = {2} := by
    classical
    ext v
    fin_cases v <;> norm_num [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt,
      EnvPoint.AwakeOnClosed, EnvPoint.retain, EnvPoint.lookAhead, rotatingSupport, point]
      <;> exact ⟨3, le_rfl, by decide, by decide⟩
  rw [EnvPoint.ReadyAbove, hr] at hh
  norm_num [EnvPoint.faultCount, EnvPoint.retain, EnvPoint.lookAhead,
    rotatingSupport, point] at hh

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

/-- One existing fault grows to two while exactly two honest validators remain awake. -/
def stressPoint : EnvPoint (Fin 5) :=
  { point with
    env := ⟨1, by decide, 1, by decide, fun v _ => decide (2 ≤ v.val ∧ v.val < 4)⟩
    faultyAt := fun t => if 5 ≤ t then {0, 1} else {0}
    faultyAt_mono := by
      intro a b hab
      dsimp only
      split_ifs with ha hb
      · exact Finset.Subset.refl _
      · exact False.elim (hb (ha.trans hab))
      · decide
      · exact Finset.Subset.refl _ }

/-- The one-to-two compromise crosses the strict sleepy budget with two supporters. -/
theorem stressPoint_sleepy_rejected :
    stressPoint.ReadyAbove (1 / 2) 0 4 ∧ ¬ stressPoint.SleepyOn (1 / 2) 0 1 4 5 := by
  have hr (d : Time) : (stressPoint.retain d).readyAt 0 4 = {2, 3} := by
    classical
    ext v
    fin_cases v <;> by_cases hd : 5 ≤ d <;>
      norm_num [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.HonestAt,
        EnvPoint.retain, EnvPoint.AwakeOnClosed, stressPoint, point, hd] <;>
      exact ⟨3, le_rfl, by decide⟩
  constructor
  · have he : stressPoint.readyAt 0 4 = (stressPoint.retain 4).readyAt 0 4 := by rfl
    rw [EnvPoint.ReadyAbove, he, hr]
    norm_num [EnvPoint.faultCount, stressPoint, point]
  · intro h
    have hh := h 4 le_rfl (by decide)
    rw [EnvPoint.ReadyAbove, hr] at hh
    norm_num [EnvPoint.faultCount, EnvPoint.retain, EnvPoint.lookAhead, stressPoint, point] at hh

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

/-- A proposer ready at two is excluded when compromised inside its hold window. -/
theorem proposer_hold_rejects_compromise :
    Blocks.HonestReadyIn growthPoint (pkiFin 7) (fun _ => {1}) 0 0 2 0 ∧
      ¬ Blocks.HonestReadyIn growthPoint (pkiFin 7) (fun _ => {1}) 0 0 2 3 := by
  constructor
  · refine ⟨by simp, fun k hk => ?_⟩
    have hk' : k = 1 := Finset.mem_singleton.mp hk
    subst k
    refine ⟨⟨?_, fun _ _ _ => rfl⟩, ?_⟩ <;>
      simp [EnvPoint.HonestAt, EnvPoint.lookAhead, growthPoint, pkiFin]
  · intro h
    have hh := (h.2 1 (Finset.mem_singleton_self _)).2
    norm_num [EnvPoint.HonestAt, EnvPoint.lookAhead, growthPoint, pkiFin] at hh
    exact hh (Fin.ext rfl)

/-- Constant faults make every proposer hold agree with the original readiness requirement. -/
theorem constant_proposer_hold (h : Time) :
    Blocks.HonestReadyIn (growthPoint.retain 8) (pkiFin 7) (fun _ => {2}) 0 0 2 h ↔
      ({2} : Finset (Fin 7)).Nonempty ∧
        ∀ k ∈ ({2} : Finset (Fin 7)), (growthPoint.retain 8).Ready 0 (pkiFin 7 k) 2 :=
  Blocks.honestReadyIn_constant_iff (fun _ => rfl) _ _ _ _ _ _

/-- Two compromises among seven validators remain below one third. -/
theorem growthPoint_healthy : growthPoint.HealthyOn (1 / 3) 0 8 := by
  exact ⟨by norm_num [EnvPoint.faultCount, growthPoint], fun _ _ _ _ _ => rfl⟩

/-- The same healthy verdict holds on the constant two-fault control. -/
theorem constantPoint_healthy : (growthPoint.retain 8).HealthyOn (1 / 3) 0 8 := by
  exact ⟨by norm_num [EnvPoint.faultCount, EnvPoint.retain, growthPoint],
    fun _ _ _ _ _ => rfl⟩

/-- The control has constant faults, unlike the two-increase profile. -/
theorem constantPoint_constant : (growthPoint.retain 8).ConstantFaults := fun _ => rfl

/-- Changing only the hold leaves every constant-fault recurrence verdict unchanged. -/
theorem constant_recurrence_hold (G : Blocks.TimeGrid) (ρ : Blocks.Recurrence)
    (hold : Nat) (c start stop : Time) :
    Blocks.PatternRecurrence (growthPoint.retain 8) (pkiFin 7) (fun _ => {2}) G
      { ρ with hold := hold } c start stop ↔
    Blocks.PatternRecurrence (growthPoint.retain 8) (pkiFin 7) (fun _ => {2}) G
      { ρ with hold := 0 } c start stop := by
  rw [Blocks.patternRecurrence_constant_iff constantPoint_constant,
    Blocks.patternRecurrence_constant_iff constantPoint_constant]
  rfl

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

section PrefixLiveness

variable {Prog : Type} {S : System (Fin 7)} {X : Progress S Prog} {K : Contract Prog}

/-- Sleepy liveness applies to a six-time-unit prefix spanning both compromises,
without assuming synchrony after that prefix. -/
theorem growing_sleepyLive_prefix (h : CorrectProtocol S X K)
    {g : S.schema.Id} (hg : S.schema.output .available = some g)
    (r : S.Run) (hv : S.Valid r) (hp : S.pt r = growthPoint) (i : K.Idx)
    (hs : (S.log r).SyncUntil (S.pt r) 6)
    (hb : (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) 0 6)
    (hx : S.prog X K .available i 0 6 r) :
    (∀ x t t', (S.pt r).SubmittedToSome x t →
      max t 0 + (S.pt r).env.ΔAC + S.lat K .available i r ≤ t' → t' ≤ 6 →
      ∀ v, (S.pt r).Ready (S.cDur K r) v t' → x ∈ (S.trace r).readAt g v t') ∨
      S.Excuse r :=
  h.sleepyLive_prefix (Or.inl rfl) hg r hv i (by decide)
    (by rw [hp]; decide) hs hb hx

/-- Healthy prefix liveness uses the two-increase profile's healthy budget,
not a terminal constant-fault projection. -/
theorem growing_healthyLive_prefix (h : CorrectProtocol S X K)
    {g : S.schema.Id} (hg : S.schema.output .final = some g)
    (r : S.Run) (hv : S.Valid r) (hp : S.pt r = growthPoint) (i : K.Idx)
    (hβ : K.params.β = 1 / 3)
    (hs : (S.log r).Delivers (S.pt r)
      (fun a => max a 0 + (S.pt r).env.ΔAC - 1)
      (fun a => max a 0 + (S.pt r).env.ΔFG - 1) 8)
    (hr : (S.pt r).env.ΔFG ≤ (K.params.fgDelay : Time) * (S.pt r).env.ΔAC)
    (hx : S.prog X K .final i (S.ready K 0 r) 8 r) :
    (∀ x t t', (S.pt r).SubmittedToSome x t →
      max t (S.heal K .final i 0 r) + (S.pt r).env.ΔAC + S.lat K .final i r ≤ t' →
      t' ≤ 8 → ∀ v, (S.pt r).Ready (S.cDur K r) v t' →
        x ∈ (S.trace r).readAt g v t') ∨ S.Excuse r :=
  h.healthyLive_prefix hg r hv i 0 (by decide) (by rw [hp]; exact le_rfl) hs
    (by rw [hp, hβ]; exact growthPoint_healthy) hr hx

end PrefixLiveness

end Consensus.Shape.Tests.Growth
end
