module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import Solution
public import ConsensusLeanTest.Goldilocks.VoteBinding
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witnesses for the Goldilocks acceptance coefficients

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `assumptions_small`, `assumptions_large`: `ContractAssumptions` is satisfiable at two
  concrete setups, `k = 2, δt = 6` and `k = 6, δt = 8`; `assumptions_iff` gives its exact range
  and `assumptions_empty_of_timeout` rejects `δt = 5`.
* (b) The coefficients at those setups (phase 2, `Δp = Δe`): `contract_catchUp` is `19`
  (`catchUp_small`, `catchUp_large`; at every `k`, `contract_catchUp_val`); the outage look-back
  `12k + 7` is the proof window `budget + 2·lag` and covers catch-up + 1 at every `k`
  (`eta_covers_window`, `eta_k_two_five`); lag `4k + 6`, recovery `9`, budget `4k − 5`
  (`outage_lag_recovery_budget`); heal `catchUp + M_f` on the rise-round route, `387` at
  `k = 2, δt = 6, X = 1` (`heal_val`).
  `contract_latency` takes its documented value (`4X + 6`, `4(X + 3c) + 1`) at each capability,
  and both Sleepy margins hold there.

* (b) The FG delay in slots `fgSlots` (its FG delay bound `fgDelay = 4·fgSlots − 6`):
  `fgSlots_two` gives every constant at the smallest gap (`6 ≤ δt`, the window `[0, 2, 4, 6]`,
  final latency `4(X + 6) + 1`, bound `2`); `fgSlots_three` and `fgSlots_ten` give the window,
  latency and bound at `fgSlots = 3` and `10`; `timeout_rejects_gap` rejects `fgSlots = 10` at
  `δt = 29`; `fg_transport_slow` and `fg_transport_fast` instantiate `fgDelay_bound_iff` at
  `ΔFG > ΔAC` and `ΔFG < ΔAC`.

`contract_heal` (`catchUp + healMargin`, `contract_heal_val`) is pinned by `heal_val`, which also
checks `healMargin` as the rise-round route's heal bound at `λ = 2Δ`.

* (a) The headline `GoldilocksCorrect` is not vacuous: `goldilocksCorrect_realizable_small`.
* (a) The endpoint is not vacuous: `meetsObligations_realizable_small` instantiates
  `MeetsObligations` (`meets_obligations`) at `setupSmall`, `assumptionsSmall` and gives its
  contract's active witnesses on five validators (`Shape.regimes_realizable` from
  `ShapeObligations`'s admissibility, progress-fit and tolerance fields).
* (a) The endpoint's outage and sleepy rows cover every vote binding:
  `goldilocks_committeeOne` (a committee binding with a proper-subset
  committee, `Regression.committeeOne`), and its outage and sleepy regimes are not vacuous:
  `committeeOne_realizable` (its regimes on five validators), `committeeOne_selected_ne_univ`,
  `committeeOne_outage_witness` (a clean outage witness whose committee is never the population)
  and `committeeOne_sleepy_witness` (at every output capability and index, a clean witness of
  the endpoint's sleepy premises whose committee is never the population).
* The profile label: `schema_profile` (the schema is Ebb-and-Flow, not BFT or available, decided
  on the schema alone) and the rejections `not_obligationsAs_bft` and `not_obligationsAs_available`
  (no contract makes the family a BFT or an available protocol). -/

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
  vote := stock

/-- A larger setup: `k = 6`, `δt = 8`. -/
noncomputable def setupLarge : Setup where
  genesisRoot := 0
  δt := 8
  k := 6
  two_le_k := by decide
  c := 2
  two_le_c := le_rfl
  ro := replayOrder
  vote := stock

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

/-- (b) Catch-up is `19` at `k = 6`. -/
theorem catchUp_large : (contract_catchUp setupLarge assumptionsLarge : Nat) = 19 :=
  contract_catchUp_val _ _

/-- (b) The outage look-back `η = 12k + 7` is exactly the proof window `budget + 2·lag`
(`(4k − 5) + 2(4k + 6)`), and it covers the readers' catch-up `19`, so the outage catch-up
`max cDur (η·Δ − 1)` is `η·Δ − 1` at every `k` and every `Δ ≥ 1`. -/
theorem eta_covers_window (S : Setup) (A : ContractAssumptions S) :
    (K S A).params.η = (K S A).params.budget + 2 * (K S A).params.lag ∧
      (contract_catchUp S A : Nat) + 1 ≤ (K S A).params.η ∧
      ∀ Δ : Time, 1 ≤ Δ →
        max (((K S A).params.catchUp : Time) * Δ) (((K S A).params.η : Time) * Δ - 1) =
          ((K S A).params.η : Time) * Δ - 1 := by
  have hk := S.two_le_k
  have hη : ((K S A).params.η : Time) = 12 * (S.k : Int) + 7 := by
    change ((12 * S.k + 7 : Nat) : Int) = _; push_cast; ring
  have hc : ((K S A).params.catchUp : Time) = 19 := by
    change ((contract_catchUp S A : Nat) : Int) = 19
    rw [contract_catchUp_val]; rfl
  have hk2 : (2 : Int) ≤ S.k := by exact_mod_cast hk
  refine ⟨?_, ?_, fun Δ hΔ => max_eq_right ?_⟩
  · change 12 * S.k + 7 = (4 * S.k - 5) + 2 * (4 * S.k + 6)
    omega
  · rw [contract_catchUp_val]
    change 19 + 1 ≤ 12 * S.k + 7
    omega
  · rw [hη, hc]
    have : (0 : Time) ≤ ((S.k : Int) - 2) * Δ := mul_nonneg (by linarith) (by linarith)
    linarith

/-- (b) The outage look-back `12k + 7` at `k = 2` and `k = 5`. -/
theorem eta_k_two_five (S : Setup) (A : ContractAssumptions S) :
    (S.k = 2 → (K S A).params.η = 31) ∧ (S.k = 5 → (K S A).params.η = 67) := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩ <;>
    · change 12 * S.k + 7 = _
      rw [hk]

/-- (b) The arming lag and recovery delay: lag `4k + 6` (`14` at `k = 2`), recovery `9`,
budget `4k − 5` (`3` at `k = 2`). -/
theorem outage_lag_recovery_budget :
    (K setupSmall assumptionsSmall).params.lag = 14 ∧
      (K setupSmall assumptionsSmall).params.recovery = 9 ∧
      (K setupSmall assumptionsSmall).params.budget = 3 := ⟨rfl, rfl, rfl⟩

/-- (b) The heal coefficient is `catchUp + M_f` at every capability, `387` at `k = 2`, `δt = 6`,
`X = 1` (`M_f = 368`, rise-round route). `M_f = healMargin` is the rise-round route's heal bound at
`λ = 2Δ`: the route's coefficient `20L + 8k + 28δ_t + 28X + 46` (`L = healthyDrainLen`, without its
`5λ − 2` term), with the lag `5λ = 10Δ` added, is `healMargin·Δ − 2`. -/
theorem heal_val (S : Setup) (A : ContractAssumptions S) (cap : Capability) (X : ℕ+) :
    contract_heal S A cap X = 19 + healMargin S X ∧
      contract_heal setupSmall assumptionsSmall cap 1 = 387 ∧
      ∀ D : ℤ,
        ((20 * healthyDrainLen S X + 8 * S.k + 28 * S.δt + 28 * (X : Nat) + 46 : Nat) : ℤ) * D +
            5 * (2 * D) - 2 =
          (healMargin S X : ℤ) * D - 2 := by
  refine ⟨by rw [contract_heal_val, contract_catchUp_val], by rw [contract_heal_val]; rfl,
    fun D => ?_⟩
  rw [healMargin_val]
  push_cast
  ring

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
  vote := stock

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

/-- (b) The outage contract's look-back `12k + 7` and budget `4k − 5`: at `k = 2`, `η = 31` and
`budget = 3`. -/
theorem outage_eta_budget :
    (K setupSmall assumptionsSmall).params.η = 31 ∧
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

/-- (a) The active witnesses of the endpoint's contract at `setupSmall`, `assumptionsSmall` on five
validators: sleepy, healthy, sleepy-stress, outage and bad-proposer runs exist
(`Shape.regimes_realizable`, from the fields of `meets_obligations`). -/
theorem meetsObligations_realizable_small :
    RealizableActive (goldilocks { setupSmall with vote := AsChainShape.stock })
      (goldilocksContract assumptionsSmall (contract_coefficients setupSmall assumptionsSmall))
      (Fin 5) :=
  have h := (Growing.meets_obligations setupSmall assumptionsSmall).2
  regimes_realizable _ _ h.admissible h.progressFits h.progressTolerant (Fin 5)
    (((meetsObligations_optimalFaultTolerance setupSmall assumptionsSmall).room_iff _).mpr
      (by decide))

/-- (a) **The headline is not vacuous**: `goldilocksCorrect` at `setupSmall`, `assumptionsSmall` on
five validators gives the realizability branch of `CorrectProtocol`, a clean witness for every
regime of the compiled Goldilocks system. -/
theorem goldilocksCorrect_realizable_small :
    Realizable (Model.sysOf schema
      (compiled (goldilocks { setupSmall with vote := AsChainShape.stock })) (Fin 5))
      (shapeProgress (goldilocks { setupSmall with vote := AsChainShape.stock }) (Fin 5))
      (goldilocksContract assumptionsSmall (contract_coefficients setupSmall assumptionsSmall)) :=
  (Consensus.Goldilocks.goldilocksCorrect setupSmall assumptionsSmall (Fin 5)).1.realizable
    (((meetsObligations_optimalFaultTolerance setupSmall assumptionsSmall).room_iff _).mpr
      (by decide))

/-- (a) The explicit excuses do not absorb all structural runs: reuse a clean,
active sleepy realizability witness at delays two, and check the full property
table and all three `HoldsAlways` rows without a collision escape on that run. -/
theorem goldilocksCorrectWithExcuses_nonvacuous :
    ∃ r : (Model.sysOf schema
        (compiled (goldilocks { setupSmall with vote := AsChainShape.stock })) (Fin 5)).Run,
      r.2.StructuralValid ∧ ¬ r.2.BindingFailure ∧ ¬ r.2.HashCollision ∧
      Behaviour ((Model.sysOf schema
        (compiled (goldilocks { setupSmall with vote := AsChainShape.stock })) (Fin 5)).atRun r)
        ((shapeProgress (goldilocks { setupSmall with vote := AsChainShape.stock })
          (Fin 5)).atRun r)
        (goldilocksContract assumptionsSmall
          (contract_coefficients setupSmall assumptionsSmall)) ∧
      (Model.sysOf schema
        (compiled (goldilocks { setupSmall with vote := AsChainShape.stock }))
        (Fin 5)).NonFraming r ∧
      (∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → schema.output c₁ = some g₁ →
        schema.output c₂ = some g₂ →
        ((Model.sysOf schema
          (compiled (goldilocks { setupSmall with vote := AsChainShape.stock }))
          (Fin 5)).trace r).Nested
          g₁ g₂) ∧
      (∀ g, schema.output .final = some g →
        ((Model.sysOf schema
          (compiled (goldilocks { setupSmall with vote := AsChainShape.stock }))
          (Fin 5)).trace r).Monotone
          g 0) := by
  obtain ⟨r, hw, _⟩ := goldilocksCorrect_realizable_small.sleepy .available 1 2 2
    (by decide) (by decide)
  have hv := r.2.executionValid_iff_structuralValid.mp hw.1.1
  have hf : ¬ r.2.BindingFailure := by
    rintro (hf | hf | hf)
    · exact hf hv.2.1
    · exact hf hv.2.2.1
    · exact hf hv.2.2.2
  refine ⟨r, hv.1, hf, hw.1.2.1, ?_⟩
  rcases (Consensus.Goldilocks.goldilocksCorrectWithExcuses setupSmall assumptionsSmall
    (Fin 5)).behaviour r hv.1 with hb | he
  · exact ⟨hb, hb.nonFraming r rfl,
      fun c₁ c₂ g₁ g₂ hlt hg₁ hg₂ => hb.nested c₁ c₂ g₁ g₂ hlt hg₁ hg₂ r rfl,
      fun g hg => hb.finalMonotone g hg r rfl⟩
  · exact (hf he).elim

/-! ## The outage and sleepy rows at every vote binding

The endpoint's `persists` claim holds for `goldilocks S` at every bound setup. At a committee
binding it reads a genuine proper subset (`goldilocks_committeeOne`), and its outage regime
has a clean witness whose committee is a proper subset at every time (`committeeOne_realizable`,
`committeeOne_selected_ne_univ`, `committeeOne_outage_witness`). The endpoint includes both sleepy
claims at every bound setup; at the committee binding its sleepy regime has, at every output
capability and index, a clean witness whose committee is a proper subset at every time
(`committeeOne_sleepy_witness`). -/

/-- (a) The committee instance is not the population case: at `committeeOne` the
family signs votes in the committee role selected `.sized 1`, and the SA committee size (the vote
threshold denominator) is `1`, a proper subset of every population of at least two validators. -/
theorem goldilocks_committeeOne (S : Setup) (pub : Model.Public) (hn : 2 ≤ pub.n) :
    (goldilocks { S with vote := Regression.committeeOne } pub).skel.participationKind =
        some VoteKind.vote ∧
      (goldilocks { S with vote := Regression.committeeOne } pub).skel.kindSel
        VoteKind.vote = .sized 1 ∧
      (({ S with vote := Regression.committeeOne } : Setup).params
        pub (by omega)).committeeSize = 1 ∧
      (({ S with vote := Regression.committeeOne } : Setup).params pub (by omega)).committeeSize <
        pub.n := by
  have h := Regression.committeeOne_committeeSize S pub (by omega)
  exact ⟨rfl, rfl, h, by omega⟩

/-- (a) The committee binding's regimes are realizable on at least five validators, the outage
regime with its committee clause included (`Shape.regimes_realizable`). The contract's
admissibility and tolerance are the stock ones; its progress fit is `rfl` at every binding (the
proposer selection is `.sized 1`). -/
theorem committeeOne_realizable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (hn : 5 ≤ Fintype.card V) :
    RealizableActive (goldilocks { S with vote := Regression.committeeOne }) (K S A) V :=
  regimes_realizable _ _ (meetsObligations_admissible S A) (fun _ _ _ _ => rfl)
    (meetsObligations_progressTolerant S A) V
    (((meetsObligations_optimalFaultTolerance S A).room_iff _).mpr hn)

/-- (a) On every valid run of the committee binding on at least two validators, the committee the
outage regime reads (`External.selected`, the slot's vote committee) is not the whole population at
any time: the committee clause is not the population clause. -/
theorem committeeOne_selected_ne_univ (S : Setup) (V : Type) [Fintype V] [DecidableEq V]
    (hn : 2 ≤ Fintype.card V)
    (r : (Sys (goldilocks { S with vote := Regression.committeeOne }) V).Run)
    (hv : (Sys (goldilocks { S with vote := Regression.committeeOne }) V).Valid r) (t : Time) :
    (shapeProgress (goldilocks { S with vote := Regression.committeeOne }) V).toExternal.selected
      ((Sys (goldilocks { S with vote := Regression.committeeOne }) V).pt r).env
      ((shapeProgress (goldilocks { S with vote := Regression.committeeOne }) V).toExternal.ext
        r) t ≠
      Finset.univ := by
  intro h
  have hc (s : Slot) : (r.2.sel (.duty s VoteKind.vote)).card = min 1 (Fintype.card V) :=
    hv.selValid (.duty s VoteKind.vote)
  have hcard := congrArg Finset.card h
  change ((r.2.sel (.duty _ VoteKind.vote)).map r.2.key.toEmbedding).card = _ at hcard
  rw [Finset.card_map, hc, Finset.card_univ] at hcard
  omega

/-- (a) **The committee outage regime is not vacuous**: on five validators, at `Δ = ΔF = 2`, a
clean witness of the committee binding lies in the outage regime of the obligations contract,
and its committee is a proper subset at every time. -/
theorem committeeOne_outage_witness (S : Setup) (A : ContractAssumptions S) :
    ∃ r T b₀ b₁,
      (Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).WitnessAt 2 2 r ∧
      (Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).Outage
        (shapeProgress (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).toExternal
        (K S A) T b₀ b₁ r ∧
      ∀ t, (shapeProgress
        (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).toExternal.selected
        ((Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).pt r).env
        ((shapeProgress
          (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).toExternal.ext r)
        t ≠ Finset.univ := by
  obtain ⟨r, T, b₀, b₁, hw, ho, -, -⟩ :=
    (committeeOne_realizable S A (Fin 5) (by decide)).outage 2 2 0 (by decide) (by decide)
  exact ⟨r, T, b₀, b₁, hw, ho,
    committeeOne_selected_ne_univ S (Fin 5) (by decide) r hw.1.1⟩

/-- (a) **The committee sleepy regime is not vacuous**: on five validators, at `Δ = ΔF = 2`, for
every output capability `cap` and index `i`, a clean witness of the committee binding satisfies
the endpoint's liveness premise at `cap, i` (`System.Sleepy` at the obligations contract and the
contract's proposer progress over the whole run, the first two conjuncts of `SleepyLive`), hence
also its safety premise (`System.Sleepy`), and its committee is a proper subset at every time. -/
theorem committeeOne_sleepy_witness (S : Setup) (A : ContractAssumptions S) (cap : Capability)
    (i : (K S A).Idx) :
    ∃ r,
      (Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).WitnessAt 2 2 r ∧
      ((Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).Sleepy
          (shapeProgress (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).toExternal
          (K S A) r ∧
        (Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).prog
          (shapeProgress (goldilocks { S with vote := Regression.committeeOne }) (Fin 5))
          (K S A) cap i 0
          ((Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).pt r).horizon r) ∧
      ∀ t, (shapeProgress
        (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).toExternal.selected
        ((Sys (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).pt r).env
        ((shapeProgress
          (goldilocks { S with vote := Regression.committeeOne }) (Fin 5)).toExternal.ext r)
        t ≠ Finset.univ := by
  obtain ⟨r, hw, ⟨hs, hp, -⟩, -⟩ :=
    (committeeOne_realizable S A (Fin 5) (by decide)).sleepy cap i 2 2 (by decide) (by decide)
  exact ⟨r, hw, ⟨hs, hp⟩, committeeOne_selected_ne_univ S (Fin 5) (by decide) r hw.1.1⟩

/-! ## The profile label

`MeetsObligations` labels the endpoint `ShapeObligationsAs .ebbAndFlow`. The label is decided by
the schema alone. -/

/-- The schema is Ebb-and-Flow (final, stable and available, with available and stable aliased to
`confirmed`), and neither BFT nor available: decided on the schema, not taken from the endpoint. -/
theorem schema_profile :
    Profile.ebbAndFlow.Matches schema ∧ ¬ Profile.bft.Matches schema ∧
      ¬ Profile.available.Matches schema :=
  ⟨fun cap => by cases cap <;> rfl, fun h => absurd (h .stable) (by decide),
    fun h => absurd (h .final) (by decide)⟩

/-- Rejection: at no setup and contract is the family a BFT protocol. -/
theorem not_obligationsAs_bft (S : Setup) (K : Contract ProgressReq) :
    ¬ ShapeObligationsOnAs .bft (goldilocks { S with vote := AsChainShape.stock }) K
      (fun _ p => p.ConstantFaults) :=
  fun h => schema_profile.2.1 h.1

/-- Rejection: at no setup and contract is the family an available protocol. -/
theorem not_obligationsAs_available (S : Setup) (K : Contract ProgressReq) :
    ¬ ShapeObligationsOnAs .available (goldilocks { S with vote := AsChainShape.stock }) K
      (fun _ p => p.ConstantFaults) :=
  fun h => schema_profile.2.2 h.1

end Consensus.Goldilocks.Obligations.Test.Contract

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned message is longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Goldilocks.Obligations.Test.Contract.heal_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Goldilocks.Obligations.Test.Contract.heal_val
