module
public import AvailableChainModel.Objects.Identifiers

@[expose] public section

/-! Source keys: P3 is
`fgsa-f0-f2-plan-r3.5-2a9a5877.md`, Appendix A.1.
Step-2 item I02; rulings D02 and D12. -/

namespace AvailableChain.Gen.Pure

open AvailableChain

-- P3:6409–6411.
structure AGRule (GR GT : Nat → Prop) : Prop where
  fg : ∀ i, (∀ j < i, GT j) → GR i
  ac : ∀ i, GR i → (∀ j < i, GT j) → GT i

-- P3:6417.
def FirstFailure (fail : Nat → Prop) : Prop :=
  ∀ i, (∀ j < i, ¬ fail j) → ¬ fail i

-- P3:6417; equation export required by BUILD §7.2 B3a.
theorem FirstFailure_def (fail : Nat → Prop) :
    FirstFailure fail = (∀ i, (∀ j < i, ¬ fail j) → ¬ fail i) := by
  rw [FirstFailure]

-- P3:6430–6432.
structure WindowRule (GRw GTw : Slot → Prop) : Prop where
  fg : ∀ s, (∀ s' < s, GTw s') → GRw s
  ac : ∀ s, GRw s → (∀ s' < s, GTw s') → GTw s

-- P3:6444.
def RetroAt (k j : Nat) (P : Nat → Prop) : Prop := j ≤ k ∧ P j

-- P3:6444; equation export required by BUILD §7.2 B3a.
theorem RetroAt_def (k j : Nat) (P : Nat → Prop) :
    RetroAt k j P = (j ≤ k ∧ P j) := by
  rw [RetroAt]

end AvailableChain.Gen.Pure
