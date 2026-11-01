module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- Four-anchor window for the one-delivery-bound model, cF=2 and δt≥4.
First-descendant row service, inherited progress and cache joins remain OPEN. -/
def finalWindow (S : Setup) : Pattern :=
  ⟨[0, S.δt - 1, S.δt + 1, S.δt + 3], by simp⟩

/-- Fixed timeout and outage assumptions. The pattern is determined by Setup,
not chosen by a caller; outer gaps never enter the timeout bound. -/
structure AcceptanceAssumptions (S : Setup) where
  timeout : 4 ≤ S.δt
  lookback : ℕ+

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure AcceptanceCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- OPEN numeric witness, chosen jointly with the adapter proofs below. -/
noncomputable def accepted_catchUp (S : Setup) (A : AcceptanceAssumptions S) : ℕ+ := by
  sorry

/-- OPEN finite healing witness; no whole-run progress premise may be added. -/
noncomputable def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- OPEN finite latency witness, at every outer gap, independent of timeout. -/
noncomputable def accepted_latency (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- The same three witnesses are used by every adapter. -/
noncomputable def accepted_coefficients (S : Setup) (A : AcceptanceAssumptions S) :
    AcceptanceCoefficients :=
  ⟨accepted_catchUp S A, accepted_heal S A, accepted_latency S A⟩

/-- Standard fixed resilience fractions; only guarantee coefficients vary.
Final progress is the chosen local pattern at every positive outer gap.
An abbreviation exposes the index type for the adapter signatures. -/
abbrev acceptanceContract {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard C.catchUp (8 * S.k - 8)
    (min A.lookback (4 * S.k - 6)) C.heal C.latency with η := A.lookback }
  progress := fun cap X => .recur ⟨if cap = .final then finalWindow S else Pattern.single, X⟩

theorem acceptanceContract_params_eq {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) :
    (acceptanceContract A C).params =
      { Params.standard C.catchUp (8 * S.k - 8)
        (min A.lookback (4 * S.k - 6)) C.heal C.latency with η := A.lookback } := by rfl

theorem accepted_coefficients_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).catchUp = accepted_catchUp S A := by rfl

/-- The fixed engine-unit coefficients imply the node arming lag and phase-sensitive (V).
This is only the time-window adapter, not network or participation transport. -/
theorem acceptance_outage_times (S : Setup) (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) (pub : Model.Public) (hn : 1 ≤ pub.n)
    (T b₀ b₁ : Time)
    (h : Consensus.OutageTimes (acceptanceContract A C).params pub.Δ T b₀ b₁) :
    Regimes.OutageWindowTimes (S.params pub hn) T b₀ b₁ := by
  obtain ⟨hT, hlag, horder, hbudget⟩ := h
  have hk : (2 : Int) ≤ S.k := by exact_mod_cast S.two_le_k
  have hd : (1 : Int) ≤ pub.Δ := pub.Δ_pos
  have hlcast : ((8 * S.k - 8 : Nat) : Int) = 8 * (S.k : Int) - 8 := by
    omega
  have hbcast : ((4 * S.k - 6 : Nat) : Int) = 4 * (S.k : Int) - 6 := by
    omega
  have hb : ((min A.lookback (4 * S.k - 6) : Nat) : Int) ≤ 4 * (S.k : Int) - 6 := by
    rw [← hbcast]
    exact_mod_cast (min_le_right (A.lookback : Nat) (4 * S.k - 6))
  change T + ((8 * S.k - 8 : Nat) : Int) * pub.Δ ≤ b₀ at hlag
  change b₁ ≤ b₀ + ((min A.lookback (4 * S.k - 6) : Nat) : Int) * pub.Δ at hbudget
  rw [hlcast] at hlag
  have hmul := mul_le_mul_of_nonneg_right hb (le_of_lt pub.Δ_pos)
  have hmod := Int.emod_lt_of_pos (b₀ - 6 * (pub.Δ + 1))
    (show 0 < 4 * (pub.Δ + 1) by linarith)
  change 0 ≤ T ∧ T + (4 * (S.k : Int) - 4) * (pub.Δ + 1) ≤ b₀ ∧
    b₀ ≤ b₁ ∧ b₁ - b₀ + (b₀ - 6 * (pub.Δ + 1)) % (4 * (pub.Δ + 1)) ≤
      (4 * (S.k : Int) - 2) * (pub.Δ + 1)
  refine ⟨hT, ?_, horder, ?_⟩ <;> nlinarith

noncomputable abbrev K (S : Setup) (A : AcceptanceAssumptions S) :=
  acceptanceContract A (accepted_coefficients S A)

end Consensus.Goldilocks.Refinement
end
