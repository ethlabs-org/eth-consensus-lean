module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
@[expose] public section

/-! # Witnesses for the Goldilocks acceptance coefficients

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `assumptions_small`, `assumptions_large`: `AcceptanceAssumptions` is satisfiable at two
  concrete setups, `k = 2, δt = 6` and `k = 6, δt = 8`; `assumptions_iff` gives its exact range
  and `assumptions_empty_of_timeout` rejects `δt = 5`.
* (b) The coefficients at those setups: `accepted_catchUp` is `37` at `k = 2` and `8k + 4 = 52`
  at `k = 6`; the switch between the two branches is at `k = 5` (`catchUp_of_k_le_four`,
  `catchUp_of_five_le_k`, `catchUp_k_four`, `catchUp_k_five`). `accepted_latency` takes its
  documented value at each capability, and both Sleepy margins hold there.

`accepted_heal` (`catchUp + 2·healMargin + 3`, `accepted_heal_val`) is left out. -/

namespace Consensus.Goldilocks.Refinement.Test.Acceptance

open Shape SA

open Classical in
/-- A replay order at genesis root `0`: a chosen parent-order enumeration (`[]` if none). -/
noncomputable def replayOrder (n : Nat) : ReplayOrderData n 0 (List (FG.Att n)) where
  order := fun _ Φ => if h : ∃ l, ParentOrderAt 0 Φ l then h.choose else []
  parentOrder := fun _ Φ h => by simp only [h, ↓reduceDIte]; exact h.choose_spec

/-- The smallest setup the assumptions allow: `k = 2`, `δt = 6`. -/
noncomputable def setupSmall : Setup where
  genesisRoot := 0
  δt := 6
  k := 2
  two_le_k := le_rfl
  ro := replayOrder

/-- A larger setup, past the catch-up switch: `k = 6`, `δt = 8`. -/
noncomputable def setupLarge : Setup where
  genesisRoot := 0
  δt := 8
  k := 6
  two_le_k := by decide
  ro := replayOrder

/-- The assumptions at `setupSmall`, with lookback `1`. -/
def assumptionsSmall : AcceptanceAssumptions setupSmall := ⟨le_rfl, 1⟩

/-- The assumptions at `setupLarge`, with lookback `3`. -/
def assumptionsLarge : AcceptanceAssumptions setupLarge := ⟨by decide, 3⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 2, δt = 6`. -/
theorem assumptions_small : Nonempty (AcceptanceAssumptions setupSmall) := ⟨assumptionsSmall⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 6, δt = 8`. -/
theorem assumptions_large : Nonempty (AcceptanceAssumptions setupLarge) := ⟨assumptionsLarge⟩

/-- (a) The assumptions hold exactly at the setups with `6 ≤ δt`. -/
theorem assumptions_iff (S : Setup) : Nonempty (AcceptanceAssumptions S) ↔ 6 ≤ S.δt :=
  ⟨fun ⟨A⟩ => A.timeout, fun h => ⟨⟨h, 1⟩⟩⟩

/-- (a) Rejection: a timeout of five is not admitted. -/
theorem assumptions_empty_of_timeout (S : Setup) (h : S.δt = 5) :
    IsEmpty (AcceptanceAssumptions S) :=
  ⟨fun A => by have := A.timeout; omega⟩

/-- (b) Catch-up is `37` at `k = 2`. -/
theorem catchUp_small : (accepted_catchUp setupSmall assumptionsSmall : Nat) = 37 := by
  rw [accepted_catchUp_val]
  rfl

/-- (b) Catch-up is `8k + 4 = 52` at `k = 6`. -/
theorem catchUp_large :
    (accepted_catchUp setupLarge assumptionsLarge : Nat) = 8 * setupLarge.k + 4 ∧
      (accepted_catchUp setupLarge assumptionsLarge : Nat) = 52 := by
  rw [accepted_catchUp_val]
  exact ⟨rfl, rfl⟩

/-- (b) Catch-up is `37` for every `k ≤ 4`. -/
theorem catchUp_of_k_le_four (S : Setup) (A : AcceptanceAssumptions S) (hk : S.k ≤ 4) :
    (accepted_catchUp S A : Nat) = 37 := by
  rw [accepted_catchUp_val]
  omega

/-- (b) Catch-up is `8k + 4` for every `k ≥ 5`. -/
theorem catchUp_of_five_le_k (S : Setup) (A : AcceptanceAssumptions S) (hk : 5 ≤ S.k) :
    (accepted_catchUp S A : Nat) = 8 * S.k + 4 := by
  rw [accepted_catchUp_val]
  omega

/-- (b) The switch: at `k = 4` the `37` branch still wins (`8k + 4 = 36`). -/
theorem catchUp_k_four (S : Setup) (A : AcceptanceAssumptions S) (hk : S.k = 4) :
    (accepted_catchUp S A : Nat) = 37 ∧ (accepted_catchUp S A : Nat) ≠ 8 * S.k + 4 := by
  rw [accepted_catchUp_val]
  omega

/-- (b) The switch: at `k = 5` the `8k + 4 = 44` branch wins. -/
theorem catchUp_k_five (S : Setup) (A : AcceptanceAssumptions S) (hk : S.k = 5) :
    (accepted_catchUp S A : Nat) = 44 := by
  rw [accepted_catchUp_val]
  omega

/-- (b) Latency at `k = 2, δt = 6`: `8X + 12` for available and stable, `8X + 50` for final. -/
theorem latency_small (X : ℕ+) :
    accepted_latency setupSmall assumptionsSmall .available X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupSmall assumptionsSmall .stable X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupSmall assumptionsSmall .final X = 8 * (X : Nat) + 50 := by
  rw [accepted_latency_available, accepted_latency_stable, accepted_latency_final]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at `k = 6, δt = 8`: `8X + 12` for available and stable, `8X + 50` for final.
The final latency does not depend on `δt`. -/
theorem latency_large (X : ℕ+) :
    accepted_latency setupLarge assumptionsLarge .available X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupLarge assumptionsLarge .stable X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupLarge assumptionsLarge .final X = 8 * (X : Nat) + 50 := by
  rw [accepted_latency_available, accepted_latency_stable, accepted_latency_final]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at the first index: `20` nonfinal at both setups, `58` final. -/
theorem latency_one :
    accepted_latency setupSmall assumptionsSmall .available 1 = 20 ∧
      accepted_latency setupSmall assumptionsSmall .final 1 = 58 ∧
      accepted_latency setupLarge assumptionsLarge .stable 1 = 20 ∧
      accepted_latency setupLarge assumptionsLarge .final 1 = 58 := by
  rw [accepted_latency_available, accepted_latency_final, accepted_latency_stable,
    accepted_latency_final]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- (b) Both Sleepy margins hold at `k = 2, δt = 6`; catch-up meets the margin exactly. -/
theorem sleepy_margins_small (idx : ℕ+) :
    37 ≤ (accepted_catchUp setupSmall assumptionsSmall : Nat) ∧
      8 * (idx : Nat) + 12 ≤ accepted_latency setupSmall assumptionsSmall .available idx ∧
      8 * (idx : Nat) + 12 ≤ accepted_latency setupSmall assumptionsSmall .stable idx :=
  ⟨accepted_catchUp_ge_sleepy _ _, accepted_latency_ge_sleepy _ _ _ _ (.inl rfl),
    accepted_latency_ge_sleepy _ _ _ _ (.inr rfl)⟩

/-- (b) Both Sleepy margins hold at `k = 6, δt = 8`. -/
theorem sleepy_margins_large (idx : ℕ+) :
    37 ≤ (accepted_catchUp setupLarge assumptionsLarge : Nat) ∧
      8 * (idx : Nat) + 12 ≤ accepted_latency setupLarge assumptionsLarge .available idx ∧
      8 * (idx : Nat) + 12 ≤ accepted_latency setupLarge assumptionsLarge .stable idx :=
  ⟨accepted_catchUp_ge_sleepy _ _, accepted_latency_ge_sleepy _ _ _ _ (.inl rfl),
    accepted_latency_ge_sleepy _ _ _ _ (.inr rfl)⟩

end Consensus.Goldilocks.Refinement.Test.Acceptance
