module
public import ConsensusProblem.Basic
public import Mathlib.Tactic
@[expose] public section
namespace Consensus
namespace EnvPoint
variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

theorem readyAbove_half_iff (c t : Time) : p.ReadyAbove (1 / 2) c t ↔ p.ReadyMajority c t := by
  unfold ReadyAbove ReadyMajority
  constructor <;> intro h
  · exact_mod_cast (show (p.faulty.card : ℚ) < (p.readyAt c t).card by linarith)
  · have h' : (p.faulty.card : ℚ) < (p.readyAt c t).card := by exact_mod_cast h
    linarith

theorem faultsBelow_third_iff : p.FaultsBelow (1 / 3) ↔ 3 * p.faulty.card < Fintype.card V := by
  unfold FaultsBelow
  constructor <;> intro h
  · exact_mod_cast (show (3 : ℚ) * p.faulty.card < Fintype.card V by linarith)
  · have h' : (3 : ℚ) * p.faulty.card < Fintype.card V := by exact_mod_cast h
    linarith

theorem faultsBelow_quarter_iff : p.FaultsBelow (1 / 4) ↔ 4 * p.faulty.card < Fintype.card V := by
  unfold FaultsBelow
  constructor <;> intro h
  · exact_mod_cast (show (4 : ℚ) * p.faulty.card < Fintype.card V by linarith)
  · have h' : (4 : ℚ) * p.faulty.card < Fintype.card V := by exact_mod_cast h
    linarith
end EnvPoint

structure RecoveryAssumptions where
  readyAbove : ℚ
  requireFull : Bool
  noWakeAfterGST : Bool
  deriving DecidableEq

/-- Environment parameters, published separately from service bounds. -/
structure Assumptions where
  catchUp : Nat
  sleepyReadyAbove : ℚ
  stableEtaAbove : ℚ
  eta : Nat
  fastFaultsBelow : ℚ
  armingLag : Nat
  fastArmingLag : Nat
  outageBudget : Nat
  fastOutageReadyAtLeast : ℚ
  recovery : RecoveryAssumptions
  finalityReadyOfAll : ℚ
  accFrac : ℚ
  deriving DecidableEq

namespace Assumptions
/-- Standard fractions; timing and the optional full-recovery policy are named
instance parameters, rather than hidden choices. -/
def standard (catchUp eta armingLag fastArmingLag outageBudget : Nat)
    (stableEtaAbove recoveryReadyAbove : ℚ) (recoveryFull : Bool) : Assumptions :=
  ⟨catchUp, 1/2, stableEtaAbove, eta, 1/4, armingLag, fastArmingLag,
    outageBudget, 1/2, ⟨recoveryReadyAbove, recoveryFull, true⟩, 2/3, 1/3⟩

/-- Parameter domains only. Even inclusive thresholds exclude 1, so nonempty
faults remain possible. Positive catch-up supports the relay refinement. -/
structure WellFormed (A : Assumptions) : Prop where
  catchUp_pos : 0 < A.catchUp
  sleepy_lower : 0 ≤ A.sleepyReadyAbove
  sleepy_upper : A.sleepyReadyAbove < 1
  stable_lower : 0 ≤ A.stableEtaAbove
  stable_upper : A.stableEtaAbove < 1
  fast_lower : 0 < A.fastFaultsBelow
  fast_upper : A.fastFaultsBelow < 1
  budget_pos : 0 < A.outageBudget
  outage_lower : 0 ≤ A.fastOutageReadyAtLeast
  outage_upper : A.fastOutageReadyAtLeast < 1
  recovery_lower : 0 ≤ A.recovery.readyAbove
  recovery_upper : A.recovery.readyAbove < 1
  finality_lower : 0 ≤ A.finalityReadyOfAll
  finality_upper : A.finalityReadyOfAll < 1
  acc_lower : 0 < A.accFrac
  acc_upper : A.accFrac < 1
end Assumptions
end Consensus
end
