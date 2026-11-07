module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Proofs.Obligations.Main
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import Solution
@[expose] public section

/-! # Witnesses for the Goldilocks acceptance coefficients

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `assumptions_small`, `assumptions_large`: `ContractAssumptions` is satisfiable at two
  concrete setups, `k = 2, δt = 6` and `k = 6, δt = 8`; `assumptions_iff` gives its exact range
  and `assumptions_empty_of_timeout` rejects `δt = 5`.
* (b) The coefficients at those setups (phase 2, `Δp = Δe`): `contract_catchUp` is `19` at every
  `k` (`catchUp_small`, `catchUp_large`, `catchUp_of_k_le_four`, `catchUp_of_five_le_k`,
  `catchUp_k_four`, `catchUp_k_five`, each also against the former `max 37 (8k + 4)`); the outage
  no-sleep margin `4k + 6` covers catch-up + 1 only from `k = 4` on (`noSleep_covers_catchUp`,
  `noSleep_k_two_five`); lag `4k + 6`, recovery `9`, budget `4k − 5` (`outage_lag_recovery_budget`);
  heal `catchUp + M_f` on the rise-round route, `387` at `k = 2, δt = 6, X = 1`, below the
  five-window and the phase-1 coefficients (`heal_drop`). `contract_latency` takes its documented
  value (`4X + 6`, `4(X + 3c) + 1`) at each capability, and both Sleepy margins hold there.

* (b) The FG delay in slots `fgSlots` (its FG delay bound `fgDelay = 4·fgSlots − 6`):
  `fgSlots_two` gives every constant at the smallest gap (`6 ≤ δt`, the window `[0, 2, 4, 6]`,
  final latency `4(X + 6) + 1`, bound `2`); `fgSlots_three` and `fgSlots_ten` give the window,
  latency and bound at `fgSlots = 3` and `10`; `timeout_rejects_gap` rejects `fgSlots = 10` at
  `δt = 29`; `fg_transport_slow` and `fg_transport_fast` instantiate `fgDelay_bound_iff` at
  `ΔFG > ΔAC` and `ΔFG < ΔAC`.
* (b) The former FG delay bound `r` (before the `fgSlots` restatement, gap `cF r = ⌈(r + 6)/4⌉`):
  `cF_values`; `cF_four_mul_sub_six` (every gap is the former gap of its own bound, so each
  contract is the former contract at `r = fgDelay`); `shapeObligations_of_fgDelay_le` (the
  obligations are monotone in the FG delay bound: a smaller bound is a weaker healthy regime);
  `meets_obligations_at_every_bound` (the former endpoint, at every `r` with `3·cF r ≤ δt`) and
  `former_contract_fields` (its contract is the former one).

`contract_heal` (`catchUp + healMargin`, `contract_heal_val`) is pinned by `heal_drop`.

* (a) The headline `GoldilocksCorrect` is not vacuous: `goldilocksCorrect_realizable_small`.
* (a) The endpoint is not vacuous: `meets_obligations_nonvacuous` instantiates
  `MeetsObligations` (`meets_obligations`) at `setupSmall`, `assumptionsSmall`, and
  `meetsObligations_realizable_small` gives its contract's active witnesses on five validators
  (`Shape.regimes_realizable` from `ShapeObligations`'s admissibility, progress-fit and tolerance
  fields).
* The profile label is a restatement: `schema_profile` (the schema is Ebb-and-Flow, not BFT or
  available, decided on the schema alone), `meetsObligations_iff_unlabelled` (the endpoint is
  equivalent to the unlabelled obligations), and the rejections `not_obligationsAs_bft` and
  `not_obligationsAs_available` (no contract makes the family a BFT or an available protocol). -/

namespace Consensus.Goldilocks.Obligations.Test.Contract
open AsChainShape Simulation

open Blocks Shape SA

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

/-- The assumptions at `setupSmall`, with FG gap `2`. -/
def assumptionsSmall : ContractAssumptions setupSmall := ⟨2, le_rfl, by decide⟩

/-- The assumptions at `setupLarge`, with FG gap `2`. -/
def assumptionsLarge : ContractAssumptions setupLarge := ⟨2, le_rfl, by decide⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 2, δt = 6`. -/
theorem assumptions_small : Nonempty (ContractAssumptions setupSmall) := ⟨assumptionsSmall⟩

/-- (a) The acceptance assumptions are satisfiable at `k = 6, δt = 8`. -/
theorem assumptions_large : Nonempty (ContractAssumptions setupLarge) := ⟨assumptionsLarge⟩

/-- (a) The assumptions hold exactly at the setups with `6 ≤ δt`. -/
theorem assumptions_iff (S : Setup) : Nonempty (ContractAssumptions S) ↔ 6 ≤ S.δt :=
  ⟨fun ⟨A⟩ => A.six_le_δt, fun h => ⟨⟨2, le_rfl, by omega⟩⟩⟩

/-- (a) Rejection: a timeout of five is not admitted. -/
theorem assumptions_empty_of_timeout (S : Setup) (h : S.δt = 5) :
    IsEmpty (ContractAssumptions S) :=
  ⟨fun A => by have := A.six_le_δt; omega⟩

/-- (b) Catch-up is `19` at `k = 2`. -/
theorem catchUp_small : (contract_catchUp setupSmall assumptionsSmall : Nat) = 19 :=
  contract_catchUp_val _ _

/-- (b) Catch-up is `19` at `k = 6` (phase 1 had `37`, the formula before it `8k + 4 = 52`). -/
theorem catchUp_large : (contract_catchUp setupLarge assumptionsLarge : Nat) = 19 :=
  contract_catchUp_val _ _

/-- (b) Catch-up is `19` for every `k ≤ 4`. -/
theorem catchUp_of_k_le_four (S : Setup) (A : ContractAssumptions S) (_hk : S.k ≤ 4) :
    (contract_catchUp S A : Nat) = 19 :=
  contract_catchUp_val S A

/-- (b) Catch-up is `19` for every `k ≥ 5`, below the former `8k + 4`. -/
theorem catchUp_of_five_le_k (S : Setup) (A : ContractAssumptions S) (hk : 5 ≤ S.k) :
    (contract_catchUp S A : Nat) = 19 ∧ (contract_catchUp S A : Nat) < 8 * S.k + 4 := by
  rw [contract_catchUp_val]
  omega

/-- (b) At `k = 4`, `19`, below the former formula's `max 37 36 = 37`. -/
theorem catchUp_k_four (S : Setup) (A : ContractAssumptions S) (hk : S.k = 4) :
    (contract_catchUp S A : Nat) = 19 ∧ (contract_catchUp S A : Nat) < max 37 (8 * S.k + 4) := by
  rw [contract_catchUp_val, hk]
  decide

/-- (b) At `k = 5`, `19` (the former formula gave `44`). -/
theorem catchUp_k_five (S : Setup) (A : ContractAssumptions S) (hk : S.k = 5) :
    (contract_catchUp S A : Nat) = 19 ∧ max 37 (8 * S.k + 4) = 44 := by
  rw [contract_catchUp_val, hk]
  decide

/-- (b) **Verdict flip** (phase 2): the outage no-sleep margin `4k + 6` no longer covers
catch-up + 1 = `20` at every `k`. It does from `k = 4` on (`22`), not at `k ≤ 3` (`14` at
`k = 2`, `18` at `k = 3`); the phase-1 margin `max 38 (8k + 16)` covered `37 + 1` at every `k`. -/
theorem noSleep_covers_catchUp (S : Setup) (A : ContractAssumptions S) :
    (4 ≤ S.k → (contract_catchUp S A : Nat) + 1 ≤ (K S A).params.noSleep) ∧
      (S.k ≤ 3 → (K S A).params.noSleep < (contract_catchUp S A : Nat) + 1) := by
  rw [contract_catchUp_val]
  change (4 ≤ S.k → 19 + 1 ≤ 4 * S.k + 6) ∧ (S.k ≤ 3 → 4 * S.k + 6 < 19 + 1)
  omega

/-- (b) The no-sleep margin `4k + 6` at `k = 2` and `k = 5`. -/
theorem noSleep_k_two_five (S : Setup) (A : ContractAssumptions S) :
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
theorem heal_drop (S : Setup) (A : ContractAssumptions S) (cap : Capability) (X : ℕ+) :
    contract_heal S A cap X = 19 + healMargin S X ∧
      contract_heal setupSmall assumptionsSmall cap 1 = 387 ∧
      contract_heal S A cap X <
        19 + (20 * healthyDrainLen S X + 8 * S.k + 44 * S.δt + 44 * (X : Nat) + 40) ∧
      contract_heal S A cap X <
        37 + 2 * (64 * S.k + 56 * S.δt + 80 * (X : Nat) + 92) + 3 := by
  refine ⟨by rw [contract_heal_val, contract_catchUp_val], by rw [contract_heal_val]; rfl, ?_, ?_⟩
  all_goals
    have := A.six_le_δt
    rw [contract_heal_val, contract_catchUp_val]
    unfold healMargin healthyDrainLen
    omega

/-- Both setups' assumptions have FG gap `2`. -/
theorem gap_two {S : Setup} {A : ContractAssumptions S} (h : A.fgSlots = 2 := by rfl) :
    A.fgSlots = 2 := h

/-- (b) Latency at `k = 2, δt = 6`: `4X + 6` for available and stable, `4X + 25` for final. -/
theorem latency_small (X : ℕ+) :
    contract_latency setupSmall assumptionsSmall .available X = 4 * (X : Nat) + 6 ∧
      contract_latency setupSmall assumptionsSmall .stable X = 4 * (X : Nat) + 6 ∧
      contract_latency setupSmall assumptionsSmall .final X = 4 * (X : Nat) + 25 := by
  rw [contract_latency_available, contract_latency_stable, contract_latency_final, gap_two]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at `k = 6, δt = 8`: `4X + 6` for available and stable, `4X + 25` for final.
The final latency does not depend on `δt`. -/
theorem latency_large (X : ℕ+) :
    contract_latency setupLarge assumptionsLarge .available X = 4 * (X : Nat) + 6 ∧
      contract_latency setupLarge assumptionsLarge .stable X = 4 * (X : Nat) + 6 ∧
      contract_latency setupLarge assumptionsLarge .final X = 4 * (X : Nat) + 25 := by
  rw [contract_latency_available, contract_latency_stable, contract_latency_final, gap_two]
  refine ⟨rfl, rfl, ?_⟩
  omega

/-- (b) Latency at the first index: `10` nonfinal at both setups, `29` final. -/
theorem latency_one :
    contract_latency setupSmall assumptionsSmall .available 1 = 10 ∧
      contract_latency setupSmall assumptionsSmall .final 1 = 29 ∧
      contract_latency setupLarge assumptionsLarge .stable 1 = 10 ∧
      contract_latency setupLarge assumptionsLarge .final 1 = 29 := by
  rw [contract_latency_available, contract_latency_final, contract_latency_stable,
    contract_latency_final, gap_two, gap_two]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- (b) Both Sleepy margins hold at `k = 2, δt = 6`; catch-up meets the margin exactly. -/
theorem sleepy_margins_small (idx : ℕ+) :
    19 ≤ (contract_catchUp setupSmall assumptionsSmall : Nat) ∧
      4 * (idx : Nat) + 6 ≤ contract_latency setupSmall assumptionsSmall .available idx ∧
      4 * (idx : Nat) + 6 ≤ contract_latency setupSmall assumptionsSmall .stable idx :=
  ⟨contract_catchUp_ge_sleepy _ _, contract_latency_ge_sleepy _ _ _ _ (.inl rfl),
    contract_latency_ge_sleepy _ _ _ _ (.inr rfl)⟩

/-- (b) Both Sleepy margins hold at `k = 6, δt = 8`. -/
theorem sleepy_margins_large (idx : ℕ+) :
    19 ≤ (contract_catchUp setupLarge assumptionsLarge : Nat) ∧
      4 * (idx : Nat) + 6 ≤ contract_latency setupLarge assumptionsLarge .available idx ∧
      4 * (idx : Nat) + 6 ≤ contract_latency setupLarge assumptionsLarge .stable idx :=
  ⟨contract_catchUp_ge_sleepy _ _, contract_latency_ge_sleepy _ _ _ _ (.inl rfl),
    contract_latency_ge_sleepy _ _ _ _ (.inr rfl)⟩

/-- A setup with a long timeout, `k = 2`, `δt = 30`, admitting FG gaps up to `10`. -/
noncomputable def setupRow : Setup where
  genesisRoot := 0
  δt := 30
  k := 2
  two_le_k := le_rfl
  c := 2
  two_le_c := le_rfl
  ro := replayOrder

/-- (b) FG gap `2`: `6 ≤ δt`, the window `[0, 2, 4, 6]` of span `6`, final latency `4(X + 6) + 1`;
the contract's FG delay bound is `4·2 − 6 = 2` (its healthy regime assumes `ΔFG ≤ 2·ΔAC`). -/
theorem fgSlots_two (X : ℕ+) :
    assumptionsSmall.fgSlots = 2 ∧ 6 ≤ setupSmall.δt ∧
      (finalWindow assumptionsSmall).offsets = [0, 2, 4, 6] ∧
      (finalWindow assumptionsSmall).span = 6 ∧
      contract_latency setupSmall assumptionsSmall .final X = 4 * ((X : Nat) + 6) + 1 ∧
      (K setupSmall assumptionsSmall).params.fgDelay = 2 :=
  ⟨rfl, assumptionsSmall.six_le_δt, by rw [finalWindow_offsets]; rfl, by rw [finalWindow_span]; rfl,
    by rw [contract_latency_final]; rfl, rfl⟩

/-- (b) The outage contract is plain sleepy with budget `4k − 5`: at `k = 2`, `η = 0` and
`budget = 3`. -/
theorem outage_eta_budget :
    (K setupSmall assumptionsSmall).params.η = 0 ∧
      (K setupSmall assumptionsSmall).params.budget = 3 := ⟨rfl, rfl⟩

/-- The assumptions at `setupRow` with FG gap `3` (`9 ≤ 30`). -/
def assumptionsGapThree : ContractAssumptions setupRow := ⟨3, by decide, by decide⟩

/-- The assumptions at `setupRow` with FG gap `10` (`30 ≤ 30`). -/
def assumptionsGapTen : ContractAssumptions setupRow := ⟨10, by decide, by decide⟩

/-- (b) FG gap `3`: the window `[0, 3, 6, 9]`, final latency `4(X + 9) + 1`, FG delay bound `6`. -/
theorem fgSlots_three (X : ℕ+) :
    (finalWindow assumptionsGapThree).offsets = [0, 3, 6, 9] ∧
      contract_latency setupRow assumptionsGapThree .final X = 4 * ((X : Nat) + 9) + 1 ∧
      contract_latency setupRow assumptionsGapThree .available X = 4 * (X : Nat) + 6 ∧
      (K setupRow assumptionsGapThree).params.fgDelay = 6 :=
  ⟨by rw [finalWindow_offsets]; rfl, by rw [contract_latency_final]; rfl,
    by rw [contract_latency_available], rfl⟩

/-- (b) FG gap `10`: the window `[0, 10, 20, 30]` (span `30 = δt`), final latency `4(X + 30) + 1`;
the nonfinal latency stays `4X + 6`; the FG delay bound is `34` (so the healthy regime assumes
`ΔFG ≤ 34·ΔAC`, i.e. `6·ΔAC + ΔFG ≤ 40·ΔAC`). -/
theorem fgSlots_ten (X : ℕ+) :
    (finalWindow assumptionsGapTen).offsets = [0, 10, 20, 30] ∧
      (finalWindow assumptionsGapTen).span = setupRow.δt ∧
      contract_latency setupRow assumptionsGapTen .final X = 4 * ((X : Nat) + 30) + 1 ∧
      contract_latency setupRow assumptionsGapTen .stable X = 4 * (X : Nat) + 6 ∧
      (K setupRow assumptionsGapTen).params.fgDelay = 34 :=
  ⟨by rw [finalWindow_offsets]; rfl, by rw [finalWindow_span]; rfl,
    by rw [contract_latency_final]; rfl, by rw [contract_latency_stable], rfl⟩

/-- (a) Rejection: FG gap `10` is not admitted at `δt = 29` (`3·10 = 30`). -/
theorem timeout_rejects_gap (S : Setup) (h : S.δt = 29) :
    ¬ ∃ A : ContractAssumptions S, A.fgSlots = 10 := by
  rintro ⟨A, hA⟩
  have := A.timeout
  omega

/-- (b) Slower FG attestations (`ΔFG = 34 > ΔAC = 1`, FG gap `10`): the healthy bound
`ΔFG ≤ 34·ΔAC` is `6ΔAC + ΔFG = 40 ≤ 40 = 4ΔAC·10`. -/
theorem fg_transport_slow : 6 * (1 : Time) + 34 ≤ 4 * 1 * (assumptionsGapTen.fgSlots : Time) :=
  (fgDelay_bound_iff assumptionsGapTen 1 34).1 (by decide)

/-- (b) Faster FG attestations (`ΔFG = 1 < ΔAC = 5`, FG gap `2`): `31 ≤ 40 = 4ΔAC·2`. -/
theorem fg_transport_fast : 6 * (5 : Time) + 1 ≤ 4 * 5 * (assumptionsSmall.fgSlots : Time) :=
  (fgDelay_bound_iff assumptionsSmall 5 1).1 (by decide)

/-- (a) **The obligations endpoint is not vacuous**: there are a setup and an assumption set
(`k = 2`, `δt = 6`, FG gap `2`), and the family meets the obligations at their contract. -/
theorem meets_obligations_nonvacuous : ∃ (S : Setup) (A : ContractAssumptions S),
    ShapeObligationsOnAs .ebbAndFlow (goldilocks S)
      (goldilocksContract A (contract_coefficients S A)) (fun _ p => p.ConstantFaults) :=
  ⟨setupSmall, assumptionsSmall, meets_obligations_constant setupSmall assumptionsSmall⟩

/-- (a) The active witnesses of the endpoint's contract at `setupSmall`, `assumptionsSmall` on five
validators: sleepy, healthy, sleepy-stress, outage and bad-proposer runs exist
(`Shape.regimes_realizable`, from the fields of `meets_obligations`). -/
theorem meetsObligations_realizable_small :
    RealizableActive (goldilocks setupSmall)
      (goldilocksContract assumptionsSmall (contract_coefficients setupSmall assumptionsSmall))
      (Fin 5) :=
  have h := (meets_obligations_constant setupSmall assumptionsSmall).2
  regimes_realizable _ _ h.admissible h.progressFits h.progressTolerant (Fin 5) (by decide)

/-- (a) **The headline is not vacuous**: `goldilocksCorrect` at `setupSmall`, `assumptionsSmall` on
five validators gives the realizability branch of `CorrectProtocol`, a clean witness for every
regime of the compiled Goldilocks system. -/
theorem goldilocksCorrect_realizable_small :
    Realizable (Model.sysOf schema (compiled (goldilocks setupSmall)) (Fin 5))
      (shapeProgress (goldilocks setupSmall) (Fin 5))
      (goldilocksContract assumptionsSmall (contract_coefficients setupSmall assumptionsSmall)) :=
  (Consensus.Goldilocks.goldilocksCorrectConstant setupSmall assumptionsSmall (Fin 5)).realizable
    (by decide)

/-! ## The profile label

`MeetsObligations` labels the endpoint `ShapeObligationsAs .ebbAndFlow`. The label is decided by
the schema alone, so the labelled endpoint is the unlabelled one. -/

/-- The schema is Ebb-and-Flow (final, stable and available, with available and stable aliased to
`confirmed`), and neither BFT nor available: decided on the schema, not taken from the endpoint. -/
theorem schema_profile :
    Profile.ebbAndFlow.Matches schema ∧ ¬ Profile.bft.Matches schema ∧
      ¬ Profile.available.Matches schema :=
  ⟨fun cap => by cases cap <;> rfl, fun h => absurd (h .stable) (by decide),
    fun h => absurd (h .final) (by decide)⟩

/-- **The label is a restatement**: the endpoint is equivalent to the unlabelled obligations at
every setup and assumption set. -/
theorem meetsObligations_iff_unlabelled :
    MeetsObligationsConstant ↔ ∀ (S : Setup) (A : ContractAssumptions S),
      ShapeObligationsOn (goldilocks S) (goldilocksContract A (contract_coefficients S A))
        (fun _ p => p.ConstantFaults) :=
  ⟨fun h S A => (h S A).2, fun h S A => ⟨schema_profile.1, h S A⟩⟩

/-- Rejection: at no setup and contract is the family a BFT protocol. -/
theorem not_obligationsAs_bft (S : Setup) (K : Contract ProgressReq) :
    ¬ ShapeObligationsAs .bft (goldilocks S) K :=
  fun h => schema_profile.2.1 h.1

/-- Rejection: at no setup and contract is the family an available protocol. -/
theorem not_obligationsAs_available (S : Setup) (K : Contract ProgressReq) :
    ¬ ShapeObligationsAs .available (goldilocks S) K :=
  fun h => schema_profile.2.2 h.1

/-! ## The fixed FG gap against the former FG delay bound

Before the `fgSlots` restatement the assumptions took an FG delay bound `r ≥ 1` (the healthy
regime's `ΔFG ≤ r·ΔAC`), with the gap `cF r = ⌈(r + 6)/4⌉`, the timeout `3·cF r ≤ δt`, the window
`[0, cF r, 2·cF r, 3·cF r]` and the final latency `4(X + 3·cF r) + 1`. The restated endpoint is
equivalent, as one checked fact: `meetsObligations_iff_former`. Each contract is the former one at
`r = 4·fgSlots − 6` (`formerContract_eq`, from `cF_four_mul_sub_six`), and the former endpoint at
every `r` follows from the restated one (`meets_obligations_at_every_bound`), because the
obligations only weaken with a smaller bound (`shapeObligations_of_fgDelay_le`). -/

/-- The former FG gap at bound `r`: `cF r = ⌈(r + 6)/4⌉`. -/
def cF (r : ℕ+) : Nat := ((r : Nat) + 9) / 4

theorem cF_ceil (r : ℕ+) : (r : Nat) + 6 ≤ 4 * cF r ∧ 4 * cF r < (r : Nat) + 10 := by
  unfold cF
  omega

/-- The former gap at `r = 1, 2, 3, 32`: it crosses a rounding boundary between `2` and `3`. -/
theorem cF_values : cF 1 = 2 ∧ cF 2 = 2 ∧ cF 3 = 3 ∧ cF 32 = 10 := by decide

/-- Every gap `c ≥ 2` is the former gap of its own bound `4c − 6`: the contract at `fgSlots` is the
former contract at `r = fgDelay`. -/
theorem cF_four_mul_sub_six {S : Setup} (A : ContractAssumptions S) : cF A.fgDelay = A.fgSlots := by
  have := A.two_le_fgSlots
  unfold cF
  rw [A.fgDelay_val]
  omega

/-- `K` with its FG delay bound replaced by `d`. -/
def withFGDelay (K : Contract ProgressReq) (d : ℕ+) : Contract ProgressReq :=
  { K with params := { K.params with fgDelay := d } }

/-- **The obligations are monotone in the FG delay bound**: the bound enters them only through the
healthy regime's premise `ΔFG ≤ fgDelay·ΔAC` (`System.Healthy`, in `healthyLive` and
`healedSafe`), so a smaller bound keeps every claim. -/
theorem shapeObligations_of_fgDelay_le {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Countable Info] {F : ChainShapeFamily O Info} {K : Contract ProgressReq} {d : ℕ+}
    {Q : ∀ V : Type, EnvPoint V → Prop}
    (hd : d ≤ K.params.fgDelay) (h : ShapeObligationsOn F K Q) :
    ShapeObligationsOn F (withFGDelay K d) Q := by
  have hH : ∀ (V : Type) [Fintype V] [DecidableEq V] (g : Time) (r : (Sys F V).Run),
      (Sys F V).Healthy (withFGDelay K d) g r → (Sys F V).Healthy K g r := by
    intro V _ _ g r hr
    refine ⟨hr.1, hr.2.1, hr.2.2.trans ?_⟩
    have hd' : ((d : Nat) : Time) ≤ (K.params.fgDelay : Nat) := by exact_mod_cast hd
    exact mul_le_mul_of_nonneg_right hd' ((Sys F V).pt r).env.ΔAC_pos.le
  have ha := h.admissible
  refine ⟨fun V _ _ => ?_, ⟨ha.1, ha.2, ha.3, ha.4, ha.5, ha.6⟩, h.serves, h.progressFits,
    h.progressTolerant⟩
  have c := h.claims V
  exact
    { outputValid := c.outputValid
      nested := c.nested
      finalMonotone := c.finalMonotone
      finalAccountable := c.finalAccountable
      healthyLive := fun cap g hg i gst r hv hp =>
        c.healthyLive cap g hg i gst r hv ⟨hp.1, hH V gst r hp.2.1, hp.2.2⟩
      sleepySafe := c.sleepySafe
      sleepyLive := c.sleepyLive
      healedSafe := fun cap g hc hg i gst r hv hp =>
        c.healedSafe cap g hc hg i gst r hv ⟨hp.1, hH V gst r hp.2.1, hp.2.2⟩
      persists := c.persists }

/-- The former gap is at least `2`. -/
theorem two_le_cF (r : ℕ+) : 2 ≤ cF r := by
  have := (cF_ceil r).1
  have := r.pos
  omega

/-- The assumptions of the former bound `r`: gap `cF r`. -/
def formerAssumptions (S : Setup) (r : ℕ+) (ht : 3 * cF r ≤ S.δt) : ContractAssumptions S :=
  ⟨cF r, two_le_cF r, ht⟩

/-- The former contract at bound `r`: the contract at gap `cF r`, with FG delay bound `r`. -/
noncomputable def formerContract (S : Setup) (r : ℕ+) (ht : 3 * cF r ≤ S.δt) :
    Contract ProgressReq :=
  withFGDelay (goldilocksContract (formerAssumptions S r ht)
    (contract_coefficients S (formerAssumptions S r ht))) r

/-- The former contract has the former numbers: FG delay bound `r`, final progress the window
`[0, cF r, 2·cF r, 3·cF r]` in every window of the outer gap, final latency
`4(X + 3·cF r) + 1`. -/
theorem former_contract_fields (S : Setup) (r : ℕ+) (ht : 3 * cF r ≤ S.δt) (X : ℕ+) :
    (formerContract S r ht).params.fgDelay = r ∧
      (formerContract S r ht).progress .final X =
        .recur { pattern := ⟨[0, cF r, 2 * cF r, 3 * cF r], by simp⟩, gap := X, hold := 1 } ∧
      (formerContract S r ht).params.latency .final X = 4 * ((X : Nat) + 3 * cF r) + 1 :=
  ⟨rfl, rfl, rfl⟩

/-- Conversely, each contract is the former contract at its own FG delay bound
`r = 4·fgSlots − 6` (whose gap is `fgSlots`, `cF_four_mul_sub_six`): the same FG delay bound,
final progress and final latency. -/
theorem contract_eq_former {S : Setup} (A : ContractAssumptions S) (X : ℕ+) :
    (K S A).params.fgDelay = A.fgDelay ∧
      (K S A).progress .final X = .recur { pattern := finalWindow A, gap := X, hold := 1 } ∧
      (finalWindow A).offsets = [0, cF A.fgDelay, 2 * cF A.fgDelay, 3 * cF A.fgDelay] ∧
      (K S A).params.latency .final X = 4 * ((X : Nat) + 3 * cF A.fgDelay) + 1 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rw [finalWindow_offsets, cF_four_mul_sub_six A]
  · rw [cF_four_mul_sub_six A]
    rfl

/-- The timeout of the assumptions is the former timeout at their own bound `r = fgDelay`. -/
theorem former_timeout {S : Setup} (A : ContractAssumptions S) : 3 * cF A.fgDelay ≤ S.δt := by
  rw [cF_four_mul_sub_six A]
  exact A.timeout

/-- The former assumptions at `r = fgDelay` are the assumptions themselves. -/
theorem formerAssumptions_fgDelay {S : Setup} (A : ContractAssumptions S) :
    formerAssumptions S A.fgDelay (former_timeout A) = A := by
  have h := cF_four_mul_sub_six A
  cases A
  simp only [formerAssumptions, ContractAssumptions.mk.injEq]
  exact h

/-- **Each contract is the former contract at its own FG delay bound** `r = 4·fgSlots − 6`, as one
equality of contracts. -/
theorem formerContract_eq {S : Setup} (A : ContractAssumptions S) :
    formerContract S A.fgDelay (former_timeout A) = K S A := by
  unfold formerContract
  rw [formerAssumptions_fgDelay A]
  rfl

/-- **The restated endpoint is equivalent to the former one.** `MeetsObligations` (at every setup
and every FG gap `fgSlots`) holds iff Goldilocks meets the obligations at the former contract at
every setup and every FG delay bound `r` with `3·cF r ≤ δt`. Forward: the assumptions at the gap
`cF r` give a bound `4·cF r − 6 ≥ r` (`cF_ceil`), and the obligations are monotone in it
(`shapeObligations_of_fgDelay_le`). Backward: `formerContract_eq` at `r = fgDelay`. -/
theorem meetsObligations_iff_former :
    MeetsObligationsConstant ↔ ∀ (S : Setup) (r : ℕ+) (ht : 3 * cF r ≤ S.δt),
      ShapeObligationsOn (goldilocks S) (formerContract S r ht)
        (fun _ p => p.ConstantFaults) := by
  constructor
  · intro h S r ht
    refine shapeObligations_of_fgDelay_le ?_ (h S (formerAssumptions S r ht)).2
    change (r : Nat) ≤ 4 * cF r - 6
    have := (cF_ceil r).1
    omega
  · intro h S A
    have hA := h S A.fgDelay (former_timeout A)
    rw [formerContract_eq A] at hA
    exact ⟨schema_matches_ebbAndFlow, hA⟩

/-- **The former endpoint, at every FG delay bound `r`** with `3·cF r ≤ δt`: Goldilocks meets the
obligations at the former contract (`meetsObligations_iff_former` at `meets_obligations`). -/
theorem meets_obligations_at_every_bound (S : Setup) (r : ℕ+) (ht : 3 * cF r ≤ S.δt) :
    ShapeObligationsOn (goldilocks S) (formerContract S r ht)
      (fun _ p => p.ConstantFaults) :=
  meetsObligations_iff_former.1 meets_obligations_constant S r ht

end Consensus.Goldilocks.Obligations.Test.Contract
