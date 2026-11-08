module
public import ConsensusLean.Comparison.Protection
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! # Slice 2 rejection tests

Cheap checks that the Slice 2 statements reject what they must: a zero budget, an unrealizable
threshold (`θ = 1`, `θ < 0`), a cohort of exactly `A = 0` or of `n − fcap` at the boundary, a
boundary point whose sleeping witness breaks the sleepy budget (`θ = 99/100`, `A = 2`, `fcap = 1`,
`n = 4`), coverage by a system with no valid run or without the source output, a default at numbers
that do not put the class inside the contract's `Outage` (a shorter look-back, a shifted retention
point, a lower threshold, a shorter catch-up), and comparisons of points whose retention offsets
differ. The `A = 0` column is domain-feasible, so is Astra's example (`n = 4`, `A = 1`, cap `3`,
an unattained cap) and a threshold just below `1` (`θ = 99/100`, `n = 2`), a boundary point with
`θ = 1/2` is feasible, every boundary-feasible point is domain-feasible, and the default is the
contract's `lag` and `recovery` on the `A = 0` column of the stable source at the contract's
numbers. The monotonicity of the default is proved in `Proofs/Comparison/Protection`. -/

namespace Consensus.Comparison.Test

open Consensus.Comparison

variable {V : Type} [Fintype V] {Prog : Type} {K : Contract Prog}

/-- A zero budget is infeasible (an active outage lasts at least `ΔAC`). -/
theorem budget_zero_infeasible (q : ProtQ) (h : q.β = 0) : ¬ q.DomainFeasible V := by
  rintro ⟨h', -⟩
  omega

/-- `θ = 1` is infeasible for domain coverage: the class is empty (`θ·X ≥ |ready|`). -/
theorem theta_one_domain_infeasible (q : ProtQ) (h : q.θ = 1) : ¬ q.DomainFeasible V := by
  rintro ⟨-, -, h', -⟩
  exact absurd h' (by simp [h])

/-- `θ = 1` is infeasible for boundary coverage. -/
theorem theta_one_boundary_infeasible (q : ProtQ) (h : q.θ = 1) : ¬ q.BoundaryFeasible V := by
  rintro ⟨-, -, h', -⟩
  exact absurd h' (by simp [h])

/-- A negative threshold is infeasible. -/
theorem theta_neg_infeasible (q : ProtQ) (h : q.θ < 0) : ¬ q.DomainFeasible V := by
  rintro ⟨-, h', -⟩
  exact absurd h' (not_le.mpr h)

/-- `A = 0` is never boundary-feasible: `CohortOn` forces a cohort larger than the faults. -/
theorem boundary_A_zero_infeasible (q : ProtQ) (h : q.A = 0) : ¬ q.BoundaryFeasible V := by
  rintro ⟨-, -, -, h', -⟩
  omega

/-- A boundary cohort of `n − fcap` is infeasible: an honest validator outside the cohort must
remain to sleep through the outage. -/
theorem boundary_cohort_all_honest_infeasible (q : ProtQ) (h : q.A + q.fcap = Fintype.card V) :
    ¬ q.BoundaryFeasible V := by
  rintro ⟨-, -, -, -, h', -⟩
  omega

/-- The `A = 0` column is domain-feasible at every positive budget and realizable threshold,
whatever the fault cap, once `n ≥ 2` (a fault-free representative with a cohort of one). -/
theorem domain_A_zero_feasible (q : ProtQ) (hA : q.A = 0) (hβ : 1 ≤ q.β) (hθ₀ : 0 ≤ q.θ)
    (hθ₁ : q.θ < 1) (hn : 2 ≤ Fintype.card V) : q.DomainFeasible V :=
  ⟨hβ, hθ₀, hθ₁, 0, 1, Nat.zero_le _, by omega, by omega, by omega⟩

/-- **Astra's example**: `n = 4`, `A = 1`, cap `3` is domain-feasible at every realizable
threshold (the cap need not be attained; a fault-free representative suffices). -/
theorem astra_example_feasible (src : ProtSrc) (η ns ca ah cu : ℕ) (θ : ℚ) (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ < 1) : (⟨1, 1, 3, src, η, ns, ca, ah, θ, cu⟩ : ProtQ).DomainFeasible (Fin 4) :=
  ⟨le_rfl, hθ₀, hθ₁, 0, 1, by simp, le_rfl, by simp, by simp⟩

/-- A threshold just below `1` is domain-feasible on two validators: one sleeps, the other is
ready alone, and `θ·1 < 1`. The sleeping witness imposes no further limit on the domain. -/
theorem theta_near_one_domain_feasible (src : ProtSrc) (η ns ca ah cu fcap : ℕ) :
    (⟨1, 1, fcap, src, η, ns, ca, ah, 99 / 100, cu⟩ : ProtQ).DomainFeasible (Fin 2) :=
  ⟨le_rfl, by norm_num, by norm_num, 0, 1, by simp, le_rfl, by simp, by simp⟩

/-- A threshold just below `1` is not boundary-feasible at `A = 2`, `fcap = 1`, `n = 4`: the
sleeping witness's budget `θ·(A + fcap) < A` reads `297/100 < 2`. -/
theorem theta_near_one_boundary_infeasible (src : ProtSrc) (η ns ca ah cu : ℕ) :
    ¬ (⟨1, 2, 1, src, η, ns, ca, ah, 99 / 100, cu⟩ : ProtQ).BoundaryFeasible (Fin 4) := by
  rintro ⟨-, -, -, -, -, h⟩
  norm_num at h

/-- The same boundary point at `θ = 1/2` is feasible: `3/2 < 2`. -/
theorem theta_half_boundary_feasible (src : ProtSrc) (η ns ca ah cu : ℕ) :
    (⟨1, 2, 1, src, η, ns, ca, ah, 1 / 2, cu⟩ : ProtQ).BoundaryFeasible (Fin 4) :=
  ⟨le_rfl, by norm_num, by norm_num, by norm_num, by simp, by norm_num⟩

/-- Every boundary-feasible point is domain-feasible (the representative attains the cap). -/
theorem boundary_domainFeasible (q : ProtQ) (h : q.BoundaryFeasible V) : q.DomainFeasible V :=
  ⟨h.1, h.2.1, h.2.2.1, q.fcap, q.A, le_rfl, le_rfl, h.2.2.2.1, h.2.2.2.2.1⟩

/-- Two points that differ only in the cohort look-ahead are not comparable: the retention offset
`noSleep + cohortAhead` is fixed by the order. -/
theorem cohortAhead_shift_not_le (q : ProtQ) :
    ¬ q ≤ { q with cohortAhead := q.cohortAhead + 1 } := by
  rintro ⟨-, -, -, -, -, -, -, h, -, -⟩
  simp only at h
  omega

/-- The point with the contract's windows, threshold and catch-up. -/
def contractQ (K : Contract Prog) (β A f : ℕ) : ProtQ :=
  ⟨β, A, f, .stable, K.params.η, K.params.noSleep, K.params.cohortAhead, K.params.ahead,
    K.params.θ, K.params.catchUp⟩

/-- The default from `persists` on the `A = 0` column of the stable source within the budget, at
the contract's numbers, is the contract's `lag` and `recovery`. -/
theorem default_A_zero (β f : ℕ) (hβ : β ≤ K.params.budget) :
    protLagDefault K (contractQ K β 0 f) = (K.params.lag : WithTop ℕ) ∧
      protRecDefault K (contractQ K β 0 f) = (K.params.recovery : WithTop ℕ) := by
  simp [protLagDefault, protRecDefault, PersistsPoint, contractQ, hβ]

/-- The default claims nothing for the available source. -/
theorem default_available_top (q : ProtQ) (h : q.src = .available) :
    protLagDefault K q = ⊤ ∧ protRecDefault K q = ⊤ := by
  simp [protLagDefault, protRecDefault, PersistsPoint, h]

/-- The default claims nothing at a look-back shorter than the contract's (a weaker participation
premise than `Outage`'s). -/
theorem default_short_lookback_top (q : ProtQ) (h : q.η < K.params.η) :
    protLagDefault K q = ⊤ ∧ protRecDefault K q = ⊤ := by
  have : ¬ PersistsPoint K q := fun hp => absurd hp.2.2.1 (by omega)
  simp [protLagDefault, protRecDefault, this]

/-- The default claims nothing at a retention point other than the contract's (a later one weakens
`NoSleepOn`, an earlier one weakens `CohortOn`). -/
theorem default_shifted_retention_top (q : ProtQ)
    (h : q.noSleep + q.cohortAhead ≠ K.params.noSleep + K.params.cohortAhead) :
    protLagDefault K q = ⊤ ∧ protRecDefault K q = ⊤ := by
  have : ¬ PersistsPoint K q := fun hp => h hp.2.2.2.2.2.1
  simp [protLagDefault, protRecDefault, this]

/-- The default claims nothing at a threshold below the contract's (a weaker sleepy premise than
`Outage`'s). -/
theorem default_low_threshold_top (q : ProtQ) (h : q.θ < K.params.θ) :
    protLagDefault K q = ⊤ ∧ protRecDefault K q = ⊤ := by
  have : ¬ PersistsPoint K q := fun hp => absurd hp.2.2.2.2.2.2.1 (not_le.mpr h)
  simp [protLagDefault, protRecDefault, this]

/-- The default claims nothing at a catch-up shorter than the contract's (more ready validators:
a weaker sleepy premise, and sources and readers that `persists` does not cover). -/
theorem default_short_catchUp_top (q : ProtQ) (h : q.catchUp < K.params.catchUp) :
    protLagDefault K q = ⊤ ∧ protRecDefault K q = ⊤ := by
  have : ¬ PersistsPoint K q := fun hp => absurd hp.2.2.2.2.2.2.2 (by omega)
  simp [protLagDefault, protRecDefault, this]

variable [DecidableEq V] {S : System V}

/-- No valid run: finite bounds at a domain-feasible point are not covered. -/
theorem prot_no_valid_not_covered (hS : ∀ r, ¬ S.Valid r) {ℓ rec : Bound ProtQ} (q : ProtQ)
    (hq : q.DomainFeasible V) (c d : ℕ) (hc : ℓ q = c) (hd : rec q = d) :
    ¬ ProtDomainCoverage S ℓ rec := by
  intro h
  obtain ⟨-, r, -, -, -, hv, -⟩ := h.covers q hq c d hc hd
  exact hS r hv

/-- A source the protocol does not provide: finite bounds at a domain-feasible point are not
covered (the claim would be vacuous). -/
theorem prot_unprovided_not_covered {ℓ rec : Bound ProtQ} (q : ProtQ)
    (hout : S.schema.output q.src.cap = none) (hq : q.DomainFeasible V) (c d : ℕ) (hc : ℓ q = c)
    (hd : rec q = d) : ¬ ProtDomainCoverage S ℓ rec := by
  intro h
  obtain ⟨hs, -⟩ := h.covers q hq c d hc hd
  simp [hout] at hs

end Consensus.Comparison.Test

end
