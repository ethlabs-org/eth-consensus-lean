module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.AcceptanceDefs
@[expose] public section

/-! # Witnesses for the Goldilocks acceptance coefficients

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `assumptions_small`, `assumptions_large`: `AcceptanceAssumptions` is satisfiable at two
  concrete setups, `k = 2, δt = 6` and `k = 6, δt = 8`; `assumptions_iff` gives its exact range
  and `assumptions_empty_of_timeout` rejects `δt = 5`.
* (b) The coefficients at those setups (phase 2, `Δp = Δe`): `accepted_catchUp` is `19` at every
  `k` (`catchUp_small`, `catchUp_large`, `catchUp_of_k_le_four`, `catchUp_of_five_le_k`,
  `catchUp_k_four`, `catchUp_k_five`, each also against the former `max 37 (8k + 4)`); the outage
  no-sleep margin `4k + 6` covers catch-up + 1 only from `k = 4` on (`noSleep_covers_catchUp`,
  `noSleep_k_two_five`); lag `4k + 6`, recovery `9`, budget `4k − 5` (`outage_lag_recovery_budget`);
  heal `catchUp + M_f` on the rise-round route, `387` at `k = 2, δt = 6, X = 1`, below the
  five-window and the phase-1 coefficients (`heal_drop`). `accepted_latency` takes its documented
  value (`4X + 6`, `4(X + 3c) + 1`) at each capability, and both Sleepy margins hold there.

* (b) The row ratio `r` (`AcceptanceAssumptions.rowRatio`) and its gap `c = cF r`:
  `rowRatio_one` reproduces every constant of the single-bound contract (`c = 2`, `6 ≤ δt`, the
  window `[0, 2, 4, 6]`, final latency `4(X + 6) + 1`); `rowGap_boundary` crosses a rounding
  boundary (`cF 2 = 2`, `cF 3 = 3`); `rowRatio_three` and `rowRatio_thirtyTwo` give the window and
  latency at `c = 3` and `c = 10`; `timeout_rejects_ratio` rejects `r = 32` at `δt = 29`;
  `row_transport_slow` and `row_transport_fast` instantiate `cF_spec` at `ΔF > Δ` and `ΔF < Δ`.

`accepted_heal` (`catchUp + healMargin`, `accepted_heal_val`) is pinned by `heal_drop`. -/

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
  c := 2
  two_le_c := le_rfl
  ro := replayOrder

/-- A larger setup, past the catch-up switch: `k = 6`, `δt = 8`. -/
noncomputable def setupLarge : Setup where
  genesisRoot := 0
  δt := 8
  k := 6
  two_le_k := by decide
  c := 2
  two_le_c := le_rfl
  ro := replayOrder

/-- The assumptions at `setupSmall`, with row ratio `1`. -/
def assumptionsSmall : AcceptanceAssumptions setupSmall := ⟨1, by decide⟩

/-- The assumptions at `setupLarge`, with row ratio `1`. -/
def assumptionsLarge : AcceptanceAssumptions setupLarge := ⟨1, by decide⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 2, δt = 6`. -/
theorem assumptions_small : Nonempty (AcceptanceAssumptions setupSmall) := ⟨assumptionsSmall⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 6, δt = 8`. -/
theorem assumptions_large : Nonempty (AcceptanceAssumptions setupLarge) := ⟨assumptionsLarge⟩

/-- (a) The assumptions hold exactly at the setups with `6 ≤ δt`. -/
theorem assumptions_iff (S : Setup) : Nonempty (AcceptanceAssumptions S) ↔ 6 ≤ S.δt :=
  ⟨fun ⟨A⟩ => A.six_le_δt, fun h => ⟨⟨1, by rw [show cF 1 = 2 from rfl]; omega⟩⟩⟩

/-- (a) Rejection: a timeout of five is not admitted. -/
theorem assumptions_empty_of_timeout (S : Setup) (h : S.δt = 5) :
    IsEmpty (AcceptanceAssumptions S) :=
  ⟨fun A => by have := A.six_le_δt; omega⟩

/-- (b) Catch-up is `19` at `k = 2`. -/
theorem catchUp_small : (accepted_catchUp setupSmall assumptionsSmall : Nat) = 19 :=
  accepted_catchUp_val _ _

/-- (b) Catch-up is `19` at `k = 6` (phase 1 had `37`, the formula before it `8k + 4 = 52`). -/
theorem catchUp_large : (accepted_catchUp setupLarge assumptionsLarge : Nat) = 19 :=
  accepted_catchUp_val _ _

/-- (b) Catch-up is `19` for every `k ≤ 4`. -/
theorem catchUp_of_k_le_four (S : Setup) (A : AcceptanceAssumptions S) (_hk : S.k ≤ 4) :
    (accepted_catchUp S A : Nat) = 19 :=
  accepted_catchUp_val S A

/-- (b) Catch-up is `19` for every `k ≥ 5`, below the former `8k + 4`. -/
theorem catchUp_of_five_le_k (S : Setup) (A : AcceptanceAssumptions S) (hk : 5 ≤ S.k) :
    (accepted_catchUp S A : Nat) = 19 ∧ (accepted_catchUp S A : Nat) < 8 * S.k + 4 := by
  rw [accepted_catchUp_val]
  omega

/-- (b) At `k = 4`, `19`, below the former formula's `max 37 36 = 37`. -/
theorem catchUp_k_four (S : Setup) (A : AcceptanceAssumptions S) (hk : S.k = 4) :
    (accepted_catchUp S A : Nat) = 19 ∧ (accepted_catchUp S A : Nat) < max 37 (8 * S.k + 4) := by
  rw [accepted_catchUp_val, hk]
  decide

/-- (b) At `k = 5`, `19` (the former formula gave `44`). -/
theorem catchUp_k_five (S : Setup) (A : AcceptanceAssumptions S) (hk : S.k = 5) :
    (accepted_catchUp S A : Nat) = 19 ∧ max 37 (8 * S.k + 4) = 44 := by
  rw [accepted_catchUp_val, hk]
  decide

/-- (b) **Verdict flip** (phase 2): the outage no-sleep margin `4k + 6` no longer covers
catch-up + 1 = `20` at every `k`. It does from `k = 4` on (`22`), not at `k ≤ 3` (`14` at
`k = 2`, `18` at `k = 3`); the phase-1 margin `max 38 (8k + 16)` covered `37 + 1` at every `k`. -/
theorem noSleep_covers_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (4 ≤ S.k → (accepted_catchUp S A : Nat) + 1 ≤ (K S A).params.noSleep) ∧
      (S.k ≤ 3 → (K S A).params.noSleep < (accepted_catchUp S A : Nat) + 1) := by
  rw [accepted_catchUp_val]
  change (4 ≤ S.k → 19 + 1 ≤ 4 * S.k + 6) ∧ (S.k ≤ 3 → 4 * S.k + 6 < 19 + 1)
  omega

/-- (b) The no-sleep margin `4k + 6` at `k = 2` and `k = 5`. -/
theorem noSleep_k_two_five (S : Setup) (A : AcceptanceAssumptions S) :
    (S.k = 2 → (K S A).params.noSleep = 14) ∧ (S.k = 5 → (K S A).params.noSleep = 26) := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩ <;>
    · change 4 * S.k + 6 = _
      rw [hk]

/-- (b) The arming lag and recovery delay: lag `4k + 6` (`14` at `k = 2`), recovery `9`,
budget `4k − 5` (`3` at `k = 2`). -/
theorem outage_lag_recovery_budget :
    (K setupSmall assumptionsSmall).params.lag = 14 ∧
      (K setupSmall assumptionsSmall).params.recovery = 9 ∧
      (K setupSmall assumptionsSmall).params.budget = 3 := ⟨rfl, rfl, rfl⟩

/-- (b) The heal coefficient is `catchUp + M_f` at every capability, `387` at `k = 2`, `δt = 6`,
`X = 1` (`M_f = 368`, rise-round route); strictly below the five-window coefficient
`19 + (20L + 8k + 44δ_t + 44X + 40)` (`483` there; lower by `16(δ_t + X − 1)`, using
`δ_t ≥ 6`) and the phase-1 coefficient `37 + 2·M₁ + 3`, `M₁ = 64k + 56δ_t + 80X + 92`, at every
setup and index. -/
theorem heal_drop (S : Setup) (A : AcceptanceAssumptions S) (cap : Capability) (X : ℕ+) :
    accepted_heal S A cap X = 19 + healMargin S X ∧
      accepted_heal setupSmall assumptionsSmall cap 1 = 387 ∧
      accepted_heal S A cap X <
        19 + (20 * healthyDrainLen S X + 8 * S.k + 44 * S.δt + 44 * (X : Nat) + 40) ∧
      accepted_heal S A cap X <
        37 + 2 * (64 * S.k + 56 * S.δt + 80 * (X : Nat) + 92) + 3 := by
  refine ⟨by rw [accepted_heal_val, accepted_catchUp_val], by rw [accepted_heal_val]; rfl, ?_, ?_⟩
  all_goals
    have := A.six_le_δt
    rw [accepted_heal_val, accepted_catchUp_val]
    unfold healMargin healthyDrainLen
    omega

/-- Both setups' assumptions have row ratio `1`, hence gap `2`. -/
theorem gap_one {S : Setup} {A : AcceptanceAssumptions S} (h : A.rowRatio = 1 := by rfl) :
    cF A.rowRatio = 2 := by rw [h]; rfl

/-- (b) Latency at `k = 2, δt = 6`: `4X + 6` for available and stable, `4X + 25` for final. -/
theorem latency_small (X : ℕ+) :
    accepted_latency setupSmall assumptionsSmall .available X = 4 * (X : Nat) + 6 ∧
      accepted_latency setupSmall assumptionsSmall .stable X = 4 * (X : Nat) + 6 ∧
      accepted_latency setupSmall assumptionsSmall .final X = 4 * (X : Nat) + 25 := by
  rw [accepted_latency_available, accepted_latency_stable, accepted_latency_final, gap_one]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at `k = 6, δt = 8`: `4X + 6` for available and stable, `4X + 25` for final.
The final latency does not depend on `δt`. -/
theorem latency_large (X : ℕ+) :
    accepted_latency setupLarge assumptionsLarge .available X = 4 * (X : Nat) + 6 ∧
      accepted_latency setupLarge assumptionsLarge .stable X = 4 * (X : Nat) + 6 ∧
      accepted_latency setupLarge assumptionsLarge .final X = 4 * (X : Nat) + 25 := by
  rw [accepted_latency_available, accepted_latency_stable, accepted_latency_final, gap_one]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at the first index: `10` nonfinal at both setups, `29` final. -/
theorem latency_one :
    accepted_latency setupSmall assumptionsSmall .available 1 = 10 ∧
      accepted_latency setupSmall assumptionsSmall .final 1 = 29 ∧
      accepted_latency setupLarge assumptionsLarge .stable 1 = 10 ∧
      accepted_latency setupLarge assumptionsLarge .final 1 = 29 := by
  rw [accepted_latency_available, accepted_latency_final, accepted_latency_stable,
    accepted_latency_final, gap_one, gap_one]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- (b) Both Sleepy margins hold at `k = 2, δt = 6`; catch-up meets the margin exactly. -/
theorem sleepy_margins_small (idx : ℕ+) :
    19 ≤ (accepted_catchUp setupSmall assumptionsSmall : Nat) ∧
      4 * (idx : Nat) + 6 ≤ accepted_latency setupSmall assumptionsSmall .available idx ∧
      4 * (idx : Nat) + 6 ≤ accepted_latency setupSmall assumptionsSmall .stable idx :=
  ⟨accepted_catchUp_ge_sleepy _ _, accepted_latency_ge_sleepy _ _ _ _ (.inl rfl),
    accepted_latency_ge_sleepy _ _ _ _ (.inr rfl)⟩

/-- (b) Both Sleepy margins hold at `k = 6, δt = 8`. -/
theorem sleepy_margins_large (idx : ℕ+) :
    19 ≤ (accepted_catchUp setupLarge assumptionsLarge : Nat) ∧
      4 * (idx : Nat) + 6 ≤ accepted_latency setupLarge assumptionsLarge .available idx ∧
      4 * (idx : Nat) + 6 ≤ accepted_latency setupLarge assumptionsLarge .stable idx :=
  ⟨accepted_catchUp_ge_sleepy _ _, accepted_latency_ge_sleepy _ _ _ _ (.inl rfl),
    accepted_latency_ge_sleepy _ _ _ _ (.inr rfl)⟩

/-- A setup with a long timeout, `k = 2`, `δt = 30`, admitting row ratios up to `32`. -/
noncomputable def setupRow : Setup where
  genesisRoot := 0
  δt := 30
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl
  ro := replayOrder

/-- (b) Row ratio `1` reproduces the single-bound constants: gap `2`, `6 ≤ δt`, the window
`[0, 2, 4, 6]` of span `6` and final latency `4(X + 6) + 1`; the contract carries the ratio. -/
theorem rowRatio_one (X : ℕ+) :
    cF assumptionsSmall.rowRatio = 2 ∧ 6 ≤ setupSmall.δt ∧
      (finalWindow assumptionsSmall).offsets = [0, 2, 4, 6] ∧
      (finalWindow assumptionsSmall).span = 6 ∧
      accepted_latency setupSmall assumptionsSmall .final X = 4 * ((X : Nat) + 6) + 1 ∧
      (K setupSmall assumptionsSmall).params.rowRatio = 1 :=
  ⟨rfl, assumptionsSmall.six_le_δt, by rw [finalWindow_offsets]; rfl, by rw [finalWindow_span]; rfl,
    by rw [accepted_latency_final]; rfl, rfl⟩

/-- (b) The outage contract is plain sleepy with budget `4k − 5`: at `k = 2`, `η = 0` and
`budget = 3`. -/
theorem outage_eta_budget :
    (K setupSmall assumptionsSmall).params.η = 0 ∧
      (K setupSmall assumptionsSmall).params.budget = 3 := ⟨rfl, rfl⟩

/-- (b) The rounding boundary of the gap: `cF 1 = cF 2 = 2`, `cF 3 = 3`, and `cF 32 = 10`. -/
theorem rowGap_boundary : cF 1 = 2 ∧ cF 2 = 2 ∧ cF 3 = 3 ∧ cF 32 = 10 := ⟨rfl, rfl, rfl, rfl⟩

/-- The assumptions at `setupRow` with row ratio `3` (gap `3`, `9 ≤ 30`). -/
def assumptionsRowThree : AcceptanceAssumptions setupRow := ⟨3, by decide⟩

/-- The assumptions at `setupRow` with row ratio `32` (gap `10`, `30 ≤ 30`). -/
def assumptionsRowThirtyTwo : AcceptanceAssumptions setupRow := ⟨32, by decide⟩

/-- (b) Row ratio `3`: gap `3`, the window `[0, 3, 6, 9]` and final latency `4(X + 9) + 1`. -/
theorem rowRatio_three (X : ℕ+) :
    cF assumptionsRowThree.rowRatio = 3 ∧
      (finalWindow assumptionsRowThree).offsets = [0, 3, 6, 9] ∧
      accepted_latency setupRow assumptionsRowThree .final X = 4 * ((X : Nat) + 9) + 1 ∧
      accepted_latency setupRow assumptionsRowThree .available X = 4 * (X : Nat) + 6 :=
  ⟨rfl, by rw [finalWindow_offsets]; rfl, by rw [accepted_latency_final]; rfl,
    by rw [accepted_latency_available]⟩

/-- (b) Row ratio `32`: gap `10`, the window `[0, 10, 20, 30]` (span `30 = δt`) and final latency
`4(X + 30) + 1`; the nonfinal latency stays `4X + 6`; the contract carries the ratio `32` (so its
healthy regime assumes `ΔF ≤ 32·Δ`). -/
theorem rowRatio_thirtyTwo (X : ℕ+) :
    cF assumptionsRowThirtyTwo.rowRatio = 10 ∧
      (finalWindow assumptionsRowThirtyTwo).offsets = [0, 10, 20, 30] ∧
      (finalWindow assumptionsRowThirtyTwo).span = setupRow.δt ∧
      accepted_latency setupRow assumptionsRowThirtyTwo .final X = 4 * ((X : Nat) + 30) + 1 ∧
      accepted_latency setupRow assumptionsRowThirtyTwo .stable X = 4 * (X : Nat) + 6 ∧
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

/-- (b) Slower rows (`ΔF = 32 > Δ = 1`, `r = 32`): `6Δ + ΔF = 38 ≤ 40 = 4Δ·cF r` (the
protocol delays are the engine's, `Δ_p = Δ`, `ΔF_p = ΔF`). -/
theorem row_transport_slow : 6 * (1 : Time) + 32 ≤ 4 * 1 * (cF 32 : Time) :=
  cF_spec 32 1 32 (by decide) (by decide)

/-- (b) Faster rows (`ΔF = 1 < Δ = 5`, `r = 1`): `6Δ + ΔF = 31 ≤ 40 = 4Δ·cF r`. -/
theorem row_transport_fast : 6 * (5 : Time) + 1 ≤ 4 * 5 * (cF 1 : Time) :=
  cF_spec 1 5 1 (by decide) (by decide)

end Consensus.Goldilocks.Refinement.Test.Acceptance
