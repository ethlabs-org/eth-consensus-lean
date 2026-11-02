module
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Spec.Problem.Regimes
public import Mathlib.Tactic

public section

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

/-- Healthy bounds the faults below `β`. -/
theorem HealthyOn.faultsBelow {β : ℚ} {g b : Time} (h : p.HealthyOn β g b) :
    p.FaultsBelow β :=
  faultsBelow_iff.mpr h.1

/-- The outage cohort count bounds the opponents by half of all validators:
the faulty validators, the late wakers and the honest validators awake at `a`
are disjoint, so `2·|faulty ∪ late| < |faulty ∪ late| + |awake a| ≤ n`. -/
theorem CohortOn.two_mul_lt {a b : Time} (h : p.CohortOn a b) :
    2 * (p.faulty ∪ p.lateWakers a b).card < Fintype.card V := by
  classical
  have hdisj : Disjoint (p.faulty ∪ p.lateWakers a b) (p.awakeAt a) := by
    rw [Finset.disjoint_left]
    intro v hv ha
    have hah : v ∈ p.honest := (Finset.mem_filter.mp ha).1
    rcases Finset.mem_union.mp hv with hf | hl
    · exact (Finset.mem_sdiff.mp hf).2 hah
    · exact (Finset.mem_sdiff.mp hl).2 ha
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ ((p.faulty ∪ p.lateWakers a b) ∪ p.awakeAt a)
  unfold CohortOn at h
  omega

end EnvPoint

end Consensus

end
