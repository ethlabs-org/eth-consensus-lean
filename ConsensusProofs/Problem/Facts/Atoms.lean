module
public import ConsensusProofs.Problem.Derived
public import ConsensusSpec.Problem.Properties
public import Mathlib.Tactic

@[expose] public section

/-! # Environment atoms (L0 facts)

Facts about the participation and fault-bound vocabulary of `Basic` that
library proofs use: plain sleepy as a count over `ready ∪ faulty`, and a
larger fault bound is weaker. The explanatory facts (threshold monotonicity,
`η = 0`, the awake-count form) are checked in `ConsensusTests/Regimes`. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- Plain sleepy as a count over `ready ∪ faulty` (the two are disjoint). -/
theorem readyAbove_iff_union (θ : ℚ) (c t : Time) :
    p.ReadyAbove θ c t ↔ θ * ((p.readyAt c t ∪ p.faulty).card : ℚ) < (p.readyAt c t).card := by
  classical
  have hdis : Disjoint (p.readyAt c t) p.faulty := by
    refine Finset.disjoint_left.mpr fun v hv hf => ?_
    unfold readyAt at hv
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_filter.mp hv).1
  unfold ReadyAbove
  rw [Finset.card_union_of_disjoint hdis]
  push_cast
  rfl

/-- A larger fault bound is weaker. -/
theorem FaultsBelow.mono {β β' : ℚ} (h : p.FaultsBelow β') (hle : β' ≤ β) : p.FaultsBelow β :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (by positivity))

end EnvPoint

end Consensus

end
