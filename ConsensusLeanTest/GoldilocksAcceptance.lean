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

* (b) The row ratio `r` (`AcceptanceAssumptions.rowRatio`) and its gap `c = cF r`:
  `rowRatio_one` reproduces every constant of the single-bound contract (`c = 2`, `6 ≤ δt`, the
  window `[0, 2, 4, 6]`, final latency `8(X + 6) + 2`); `rowGap_boundary` crosses a rounding
  boundary (`cF 2 = 2`, `cF 3 = 3`); `rowRatio_three` and `rowRatio_thirtyTwo` give the window and
  latency at `c = 3` and `c = 10`; `timeout_rejects_ratio` rejects `r = 32` at `δt = 29`;
  `row_transport_slow` and `row_transport_fast` instantiate `cF_spec` at `ΔF > Δ` and `ΔF < Δ`.

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

/-- The assumptions at `setupSmall`, with row ratio `1` and lookback `1`. -/
def assumptionsSmall : AcceptanceAssumptions setupSmall := ⟨1, by decide, 1⟩

/-- The assumptions at `setupLarge`, with row ratio `1` and lookback `3`. -/
def assumptionsLarge : AcceptanceAssumptions setupLarge := ⟨1, by decide, 3⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 2, δt = 6`. -/
theorem assumptions_small : Nonempty (AcceptanceAssumptions setupSmall) := ⟨assumptionsSmall⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 6, δt = 8`. -/
theorem assumptions_large : Nonempty (AcceptanceAssumptions setupLarge) := ⟨assumptionsLarge⟩

/-- (a) The assumptions hold exactly at the setups with `6 ≤ δt`. -/
theorem assumptions_iff (S : Setup) : Nonempty (AcceptanceAssumptions S) ↔ 6 ≤ S.δt :=
  ⟨fun ⟨A⟩ => A.six_le_δt, fun h => ⟨⟨1, by rw [show cF 1 = 2 from rfl]; omega, 1⟩⟩⟩

/-- (a) Rejection: a timeout of five is not admitted. -/
theorem assumptions_empty_of_timeout (S : Setup) (h : S.δt = 5) :
    IsEmpty (AcceptanceAssumptions S) :=
  ⟨fun A => by have := A.six_le_δt; omega⟩

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

/-- Both setups' assumptions have row ratio `1`, hence gap `2`. -/
theorem gap_one {S : Setup} {A : AcceptanceAssumptions S} (h : A.rowRatio = 1 := by rfl) :
    cF A.rowRatio = 2 := by rw [h]; rfl

/-- (b) Latency at `k = 2, δt = 6`: `8X + 12` for available and stable, `8X + 50` for final. -/
theorem latency_small (X : ℕ+) :
    accepted_latency setupSmall assumptionsSmall .available X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupSmall assumptionsSmall .stable X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupSmall assumptionsSmall .final X = 8 * (X : Nat) + 50 := by
  rw [accepted_latency_available, accepted_latency_stable, accepted_latency_final, gap_one]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at `k = 6, δt = 8`: `8X + 12` for available and stable, `8X + 50` for final.
The final latency does not depend on `δt`. -/
theorem latency_large (X : ℕ+) :
    accepted_latency setupLarge assumptionsLarge .available X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupLarge assumptionsLarge .stable X = 8 * (X : Nat) + 12 ∧
      accepted_latency setupLarge assumptionsLarge .final X = 8 * (X : Nat) + 50 := by
  rw [accepted_latency_available, accepted_latency_stable, accepted_latency_final, gap_one]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at the first index: `20` nonfinal at both setups, `58` final. -/
theorem latency_one :
    accepted_latency setupSmall assumptionsSmall .available 1 = 20 ∧
      accepted_latency setupSmall assumptionsSmall .final 1 = 58 ∧
      accepted_latency setupLarge assumptionsLarge .stable 1 = 20 ∧
      accepted_latency setupLarge assumptionsLarge .final 1 = 58 := by
  rw [accepted_latency_available, accepted_latency_final, accepted_latency_stable,
    accepted_latency_final, gap_one, gap_one]
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

/-- A setup with a long timeout, `k = 2`, `δt = 30`, admitting row ratios up to `32`. -/
noncomputable def setupRow : Setup where
  genesisRoot := 0
  δt := 30
  k := 2
  two_le_k := le_rfl
  ro := replayOrder

/-- (b) Row ratio `1` reproduces the single-bound constants: gap `2`, `6 ≤ δt`, the window
`[0, 2, 4, 6]` of span `6` and final latency `8(X + 6) + 2`; the contract carries the ratio. -/
theorem rowRatio_one (X : ℕ+) :
    cF assumptionsSmall.rowRatio = 2 ∧ 6 ≤ setupSmall.δt ∧
      (finalWindow assumptionsSmall).offsets = [0, 2, 4, 6] ∧
      (finalWindow assumptionsSmall).span = 6 ∧
      accepted_latency setupSmall assumptionsSmall .final X = 8 * ((X : Nat) + 6) + 2 ∧
      (K setupSmall assumptionsSmall).params.rowRatio = 1 :=
  ⟨rfl, assumptionsSmall.six_le_δt, by rw [finalWindow_offsets]; rfl, by rw [finalWindow_span]; rfl,
    by rw [accepted_latency_final]; rfl, rfl⟩

/-- (b) The rounding boundary of the gap: `cF 1 = cF 2 = 2`, `cF 3 = 3`, and `cF 32 = 10`. -/
theorem rowGap_boundary : cF 1 = 2 ∧ cF 2 = 2 ∧ cF 3 = 3 ∧ cF 32 = 10 := ⟨rfl, rfl, rfl, rfl⟩

/-- The assumptions at `setupRow` with row ratio `3` (gap `3`, `9 ≤ 30`). -/
def assumptionsRowThree : AcceptanceAssumptions setupRow := ⟨3, by decide, 1⟩

/-- The assumptions at `setupRow` with row ratio `32` (gap `10`, `30 ≤ 30`). -/
def assumptionsRowThirtyTwo : AcceptanceAssumptions setupRow := ⟨32, by decide, 1⟩

/-- (b) Row ratio `3`: gap `3`, the window `[0, 3, 6, 9]` and final latency `8(X + 9) + 2`. -/
theorem rowRatio_three (X : ℕ+) :
    cF assumptionsRowThree.rowRatio = 3 ∧
      (finalWindow assumptionsRowThree).offsets = [0, 3, 6, 9] ∧
      accepted_latency setupRow assumptionsRowThree .final X = 8 * ((X : Nat) + 9) + 2 ∧
      accepted_latency setupRow assumptionsRowThree .available X = 8 * (X : Nat) + 12 :=
  ⟨rfl, by rw [finalWindow_offsets]; rfl, by rw [accepted_latency_final]; rfl,
    by rw [accepted_latency_available]⟩

/-- (b) Row ratio `32`: gap `10`, the window `[0, 10, 20, 30]` (span `30 = δt`) and final latency
`8(X + 30) + 2`; the nonfinal latency stays `8X + 12`; the contract carries the ratio `32` (so its
healthy regime assumes `ΔF ≤ 32·Δ`). -/
theorem rowRatio_thirtyTwo (X : ℕ+) :
    cF assumptionsRowThirtyTwo.rowRatio = 10 ∧
      (finalWindow assumptionsRowThirtyTwo).offsets = [0, 10, 20, 30] ∧
      (finalWindow assumptionsRowThirtyTwo).span = setupRow.δt ∧
      accepted_latency setupRow assumptionsRowThirtyTwo .final X = 8 * ((X : Nat) + 30) + 2 ∧
      accepted_latency setupRow assumptionsRowThirtyTwo .stable X = 8 * (X : Nat) + 12 ∧
      (K setupRow assumptionsRowThirtyTwo).params.rowRatio = 32 :=
  ⟨rfl, by rw [finalWindow_offsets]; rfl, by rw [finalWindow_span]; rfl,
    by rw [accepted_latency_final]; rfl, by rw [accepted_latency_stable], rfl⟩

/-- (a) Rejection: row ratio `32` is not admitted at `δt = 29` (`3·cF 32 = 30`). -/
theorem timeout_rejects_ratio (S : Setup) (h : S.δt = 29) :
    ¬ ∃ A : AcceptanceAssumptions S, A.rowRatio = 32 := by
  rintro ⟨A, hA⟩
  have := A.timeout
  rw [hA, show cF 32 = 10 from rfl] at this
  omega

/-- (b) Slower rows (`ΔF = 32 > Δ = 1`, `r = 32`): `6Δ_p + ΔF_p = 45 ≤ 80 = 4Δ_p·cF r`. -/
theorem row_transport_slow : 6 * ((1 : Time) + 1) + (32 + 1) ≤ 4 * (1 + 1) * (cF 32 : Time) :=
  cF_spec 32 1 32 (by decide) (by decide)

/-- (b) Faster rows (`ΔF = 1 < Δ = 5`, `r = 1`): `6Δ_p + ΔF_p = 38 ≤ 48 = 4Δ_p·cF r`. -/
theorem row_transport_fast : 6 * ((5 : Time) + 1) + (1 + 1) ≤ 4 * (5 + 1) * (cF 1 : Time) :=
  cF_spec 1 5 1 (by decide) (by decide)

end Consensus.Goldilocks.Refinement.Test.Acceptance
