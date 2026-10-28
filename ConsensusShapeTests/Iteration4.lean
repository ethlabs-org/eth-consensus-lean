module
public import ConsensusShape
public import ConsensusProblem.Monotonicity
public import ConsensusShapeTests.Controls
@[expose] public section
namespace Consensus.Shape.Tests.Iteration4
open Consensus.System

def standardA := Assumptions.standard 1 2 1 1 2 (1/2) (1/2) true

def namedA : Assumptions := { standardA with
  sleepyReadyAbove := 3/5
  fastFaultsBelow := 1/5
  finalityReadyOfAll := 4/5
  accFrac := 1/5 }

theorem standard_wellFormed : standardA.WellFormed := by
  constructor <;> norm_num [standardA, Assumptions.standard]

theorem named_wellFormed : namedA.WellFormed := by
  constructor <;> norm_num [namedA, standardA, Assumptions.standard]

theorem standard_weaker : standardA.Weaker namedA := by
  constructor <;> norm_num [namedA, standardA, Assumptions.standard]

/-- Rational tradeoffs are read directly in A, with no hard-coded majority or
one-quarter premise in the claim interface. -/
theorem named_transport {V : Type} [Fintype V] [DecidableEq V]
    {S : System V} {B : Bounds} {X : ExecProfile S} (h : ProblemClaims S standardA B X) :
    ProblemClaims S namedA B X := h.mono standard_wellFormed standard_weaker

/-- Inclusive half participation keeps the even-population boundary. -/
example : (1/2 : ℚ) * 4 ≤ 2 := by norm_num

/-- The inclusive endpoint is rejected by the parameter domain. -/
example (A : Assumptions) (h : A.fastOutageReadyAtLeast = 1) : ¬ A.WellFormed := by
  intro hf
  have := hf.outage_upper
  rw [h] at this
  exact lt_irrefl _ this

/-- Recovery's environment admits two faulty validators out of five. -/
def recoveryPoint : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, 0, fun _ _ => true⟩, {0, 1, 2}, 10, fun _ _ => []⟩

theorem recovery_without_fault_cap :
    EnvAssumption standardA (bounds controls) (.recovery 1) recoveryPoint ∧
      ¬ recoveryPoint.BelowOneThird := by
  classical
  have hr : ∀ c t, recoveryPoint.readyAt c t = {0, 1, 2} := by
    intro c t; ext v
    simp [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, recoveryPoint]
  have hf : recoveryPoint.faulty.card = 2 := by decide
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro t _ _
      unfold EnvPoint.ReadyAbove
      rw [hr, hf]
      norm_num [standardA, Assumptions.standard]
    · intro _ v hv t ht hh; rfl
    · intro _ v hv t ht hh
      simp [Wakes, recoveryPoint]
    · norm_num [standardA, Assumptions.standard, bounds, controls, Affine.eval, recoveryPoint]
  · unfold EnvPoint.BelowOneThird EnvPoint.FaultsBelow
    rw [hf]
    norm_num

theorem recovery_covered_above_one_third (F : Family) :
    ∃ r : (Model.sysOf (compiled F) (Fin 5)).Run,
      ((Model.sysOf (compiled F) (Fin 5)).trace r).point = recoveryPoint ∧
      (Model.sysOf (compiled F) (Fin 5)).Valid r ∧
      (Model.sysOf (compiled F) (Fin 5)).Premise standardA (bounds controls)
        (profile standardA) (.recovery 1) r ∧
      ¬ (Model.sysOf (compiled F) (Fin 5)).Excuse r := by
  obtain ⟨r, hp, hv, hx, hn, _, _⟩ := exec_conservative F standardA standard_wellFormed
    controls (.recovery 1) recoveryPoint (by norm_num [EnvPoint.WellFormed, recoveryPoint])
      (by norm_num [CoverageDomain, recoveryPoint]) recovery_without_fault_cap.1
  refine ⟨r, hp, hv, ⟨?_, hx⟩, hn⟩
  rw [hp]
  exact recovery_without_fault_cap.1
end Consensus.Shape.Tests.Iteration4
end
