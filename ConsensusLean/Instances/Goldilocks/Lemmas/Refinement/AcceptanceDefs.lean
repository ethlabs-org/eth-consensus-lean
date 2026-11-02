module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage

public section
namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- Route-A four-anchor window `[0, 2, 4, 6]` (gap 2, span 6) for the one-delivery-bound model,
cF=2 and δt≥6 (docs/decisions.md, 2026-11-02). The span does not depend on `δt`. The anchor steps
and the extraction of the window remain OPEN. -/
def finalWindow (_S : Setup) : Pattern :=
  ⟨[0, 2, 4, 6], by simp⟩

theorem finalWindow_offsets (S : Setup) :
    (finalWindow S).offsets = [0, 2, 4, 6] := by rfl

theorem finalWindow_span (S : Setup) : (finalWindow S).span = 6 := by
  unfold Pattern.span
  rw [finalWindow_offsets]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

/-- Fixed timeout and outage assumptions. The pattern is determined by Setup,
not chosen by a caller; outer gaps never enter the timeout bound. -/
structure AcceptanceAssumptions (S : Setup) where
  timeout : 6 ≤ S.δt
  lookback : ℕ+

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure AcceptanceCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- Catch-up covers the Sleepy margin and the outage history window. -/
def accepted_catchUp (S : Setup) (_A : AcceptanceAssumptions S) : ℕ+ :=
  ⟨max 37 (8 * S.k + 4), lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)⟩

theorem accepted_catchUp_val (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_catchUp S A : Nat) = max 37 (8 * S.k + 4) := by rfl

/-- OPEN finite healing witness; no whole-run progress premise may be added. -/
noncomputable def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat := by
  sorry

/-- Latency pays for the selected window and the final publication reserve. -/
def accepted_latency (S : Setup) (_A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 8 * (X : Nat) + 12
  | .stable, X => 8 * (X : Nat) + 12
  | .final, X => 8 * ((X : Nat) + 6) + 2

theorem accepted_latency_available (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .available X = 8 * (X : Nat) + 12 := by rfl

theorem accepted_latency_stable (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .stable X = 8 * (X : Nat) + 12 := by rfl

theorem accepted_latency_final (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .final X = 8 * ((X : Nat) + 6) + 2 := by rfl

/-- For engine Δe ≥ 1, 37Δe covers 18(Δe+1)+1, including safety's literal +1. -/
theorem accepted_catchUp_ge_sleepy (S : Setup) (A : AcceptanceAssumptions S) :
    37 ≤ (accepted_catchUp S A : Nat) := by
  rw [accepted_catchUp_val]
  exact Nat.le_max_left _ _

/-- For Δe ≥ 1, the nonfinal latency covers (4idx+6)(Δe+1). -/
theorem accepted_latency_ge_sleepy (S : Setup) (A : AcceptanceAssumptions S)
    (cap : Capability) (idx : ℕ+) (hcap : cap = .available ∨ cap = .stable) :
    8 * (idx : Nat) + 12 ≤ accepted_latency S A cap idx := by
  rcases hcap with rfl | rfl
  · rw [accepted_latency_available]
  · rw [accepted_latency_stable]

/-- The same three witnesses are used by every adapter. -/
noncomputable def accepted_coefficients (S : Setup) (A : AcceptanceAssumptions S) :
    AcceptanceCoefficients :=
  ⟨accepted_catchUp S A, accepted_heal S A, accepted_latency S A⟩

/-- Standard fixed resilience fractions; only guarantee coefficients vary.
Final progress is the chosen local pattern at every positive outer gap.
An abbreviation exposes the index type for the adapter signatures.

Outage numbers (engine `Δe`, node `Δp = Δe + 1`, slot `4Δp`; slow arming only):
* arming lag `8k + 12`: `(8k+12)Δe ≥ (4k+6)Δp` for every `Δe ≥ 1` (equality only
  at `Δe = 1`, about `k + 1½` slots), so the label before the outage label is
  fully armed by `b₀`;
* no-sleep margin `max 38 (8k + 16)`: it covers the formation window
  (`(4k+6)Δp` before `b₀`), the restored votes (`8k + 16`) and the catch-up
  (`catchUp + 1 = max 38 (8k + 5)`), so the honest validators awake at the window
  start are ready on the recovery counts;
* recovery delay `18` (`18Δe ≥ 9Δp` for every `Δe ≥ 1`, equality only at
  `Δe = 1`): enough for the restored votes of the locked validators to bring
  the confirmed read back above the record (owner decision 2026-11-02;
  workbench 9f5d6a3, `outage_recovery_delay-readback-opus.md`).
These numbers are sufficient for the paper route, conditional on its open
obligations; they are not claimed minimal. -/
abbrev acceptanceContract {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard C.catchUp (8 * S.k + 12)
    (min A.lookback (4 * S.k - 6)) C.heal C.latency with
    η := A.lookback, noSleep := max 38 (8 * S.k + 16), recovery := 18 }
  progress := fun cap X => .recur ⟨if cap = .final then finalWindow S else Pattern.single, X⟩

theorem acceptanceContract_params_eq {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) :
    (acceptanceContract A C).params =
      { Params.standard C.catchUp (8 * S.k + 12)
        (min A.lookback (4 * S.k - 6)) C.heal C.latency with
        η := A.lookback, noSleep := max 38 (8 * S.k + 16), recovery := 18 } := by rfl

theorem accepted_coefficients_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).catchUp = accepted_catchUp S A := by rfl

theorem accepted_coefficients_latency (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).latency = accepted_latency S A := by rfl

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
  have hlcast : ((8 * S.k + 12 : Nat) : Int) = 8 * (S.k : Int) + 12 := by
    omega
  have hbcast : ((4 * S.k - 6 : Nat) : Int) = 4 * (S.k : Int) - 6 := by
    omega
  have hb : ((min A.lookback (4 * S.k - 6) : Nat) : Int) ≤ 4 * (S.k : Int) - 6 := by
    rw [← hbcast]
    exact_mod_cast (min_le_right (A.lookback : Nat) (4 * S.k - 6))
  change T + ((8 * S.k + 12 : Nat) : Int) * pub.Δ ≤ b₀ at hlag
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
