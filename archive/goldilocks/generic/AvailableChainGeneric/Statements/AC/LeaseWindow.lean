module
public import AvailableChainGeneric.Statements.AC.Lease -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.Gen.AC

open AvailableChain

/-- A saved slow window excludes a conflicting live lease.
DC: none; INTENTIONAL addition: SA lease windows use release schedules; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
def SlowWindowConflictAbsurdStatement : Prop :=
  ∀ (leases : List (Block × Nat × Time))
    (result : Slot → Block → Prop)
    (releaseTime : Slot → Time)
    (s k : Nat) (B : Block),
    Monotone releaseTime →
    (∀ lease ∈ leases,
      ∃ w C,
        w < s ∧
        Lease.deadline lease ≤ releaseTime (w + k) ∧
        result w C ∧ Block.Preceq (Lease.target lease) C) →
    (∀ w, w < s → s + 1 ≤ w + k →
      ∃ C, result w C ∧ Block.Preceq B C) →
    (∀ w, w < s → s + 1 ≤ w + k →
      ∀ C D, result w C → result w D → Block.Compatible C D) →
    ∀ lease ∈ leases,
      releaseTime s < Lease.deadline lease →
      ¬ Block.Compatible (Lease.target lease) B →
      False

/-- The complete slow-window contract.
DC: none; INTENTIONAL addition: SA lease windows use release schedules; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
theorem SlowWindowConflictAbsurdStatement_def :
    SlowWindowConflictAbsurdStatement =
      (∀ (leases : List (Block × Nat × Time))
        (result : Slot → Block → Prop)
        (releaseTime : Slot → Time)
        (s k : Nat) (B : Block),
        Monotone releaseTime →
        (∀ lease ∈ leases,
          ∃ w C,
            w < s ∧
            Lease.deadline lease ≤ releaseTime (w + k) ∧
            result w C ∧ Block.Preceq (Lease.target lease) C) →
        (∀ w, w < s → s + 1 ≤ w + k →
          ∃ C, result w C ∧ Block.Preceq B C) →
        (∀ w, w < s → s + 1 ≤ w + k →
          ∀ C D, result w C → result w D → Block.Compatible C D) →
        ∀ lease ∈ leases,
          releaseTime s < Lease.deadline lease →
          ¬ Block.Compatible (Lease.target lease) B →
          False) := by rfl

/-- Expiry removes a row at or after its threshold deadline.
DC: none; INTENTIONAL addition: SA expires lease rows at thresholds; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
def ExpireByThresholdStatement : Prop :=
  ∀ {n : Nat} (st : GridCO.State n)
    (expiry : Slot → Time) (w c : Slot)
    (B : Block) (g : Nat) (d t : Time),
    Monotone expiry →
    w ≤ c →
    d ≤ expiry w →
    expiry c ≤ t →
    (B, g, d) ∉ (GridCO.expire st t).obligations

/-- The complete threshold-expiry contract.
DC: none; INTENTIONAL addition: SA expires lease rows at thresholds; DC uses SG records;
record codex/reports/dc-align-full.md:2000; blueprint/21-healing.md:535–540. -/
theorem ExpireByThresholdStatement_def :
    ExpireByThresholdStatement =
      (∀ {n : Nat} (st : GridCO.State n)
        (expiry : Slot → Time) (w c : Slot)
        (B : Block) (g : Nat) (d t : Time),
        Monotone expiry →
        w ≤ c →
        d ≤ expiry w →
        expiry c ≤ t →
        (B, g, d) ∉ (GridCO.expire st t).obligations) := by rfl

end AvailableChain.Gen.AC
