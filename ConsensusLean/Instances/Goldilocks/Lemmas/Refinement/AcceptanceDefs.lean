module
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Instances.Goldilocks.Statements.Regimes.Outage
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetCoefficients

public section

/-! # Goldilocks Refinement: the acceptance contract and its coefficients

The fixed assumptions (`AcceptanceAssumptions`: row ratio and timeout), the final pattern
(`finalWindow`, gap `cF r`), the coefficients (`accepted_catchUp`, `accepted_heal`,
`accepted_latency`) and the contract `acceptanceContract`/`K`. The row transport is instantiated
at the actual protocol row delay `rowDelay` (HSSharedRun, HSSharedOfQuery); the monotone lift
`PSyncFGRowTransport.mono` exists, but Accepted's chain uses it only at `le_rfl`. -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- Fixed row ratio and timeout assumptions. The row ratio `r` bounds the engine row delay
by `ΔF ≤ r·Δ` in the healthy regime (`Params.rowRatio`); the timeout pays the route-A window at
the row gap `cF r` (`Refinement/Defs`), `3·cF r ≤ δ_t`. The final pattern is determined by these,
not chosen by a caller; outer gaps never enter the timeout bound. The outage regime is plain
sleepy (`η = 0`, Francesco 2026-11-02), so no outage look-back is assumed. -/
structure AcceptanceAssumptions (S : Setup) where
  rowRatio : ℕ+
  timeout : 3 * cF rowRatio ≤ S.δt

/-- The row gap is at least `2` at every ratio (`cF_ceil`: `4·cF r ≥ r + 6 ≥ 7`). -/
theorem AcceptanceAssumptions.two_le_cF {S : Setup} (A : AcceptanceAssumptions S) :
    2 ≤ cF A.rowRatio := by
  have := (cF_ceil A.rowRatio).1
  have := A.rowRatio.pos
  omega

/-- The timeout covers the gap-2 bound `6 ≤ δ_t` at every ratio. -/
theorem AcceptanceAssumptions.six_le_δt {S : Setup} (A : AcceptanceAssumptions S) :
    6 ≤ S.δt := by
  have := A.timeout
  have := A.two_le_cF
  omega

/-- Route-A four-anchor window `[0, c, 2c, 3c]` at the row gap `c = cF r` of the assumptions'
row ratio (span `3c ≤ δ_t`, `A.timeout`). At `r = 1`, `c = 2`: `[0, 2, 4, 6]`. -/
def finalWindow {S : Setup} (A : AcceptanceAssumptions S) : Pattern :=
  ⟨[0, cF A.rowRatio, 2 * cF A.rowRatio, 3 * cF A.rowRatio], by simp⟩

theorem finalWindow_offsets {S : Setup} (A : AcceptanceAssumptions S) :
    (finalWindow A).offsets = [0, cF A.rowRatio, 2 * cF A.rowRatio, 3 * cF A.rowRatio] := by rfl

theorem finalWindow_span {S : Setup} (A : AcceptanceAssumptions S) :
    (finalWindow A).span = 3 * cF A.rowRatio := by
  unfold Pattern.span
  rw [finalWindow_offsets]
  simp only [List.foldr_cons, List.foldr_nil]
  omega

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

/-- The finite healing witness `catchUp + 2M + 3`, `M = healMargin S X`, at every capability: a
closed expression in `k`, `δ_t`, `X` and the catch-up, fixed before any run. `M` is read off the
proved reset envelope (`healthy_reset_envelope_of_drain`) and covers the final route's heal-bound
margin (`healMargin_ge_final`). No whole-run progress premise may be added. -/
def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) : Capability → ℕ+ → Nat :=
  fun _ X => (accepted_catchUp S A : Nat) + 2 * healMargin S X + 3

theorem accepted_heal_val (S : Setup) (A : AcceptanceAssumptions S) (cap : Capability) (X : ℕ+) :
    accepted_heal S A cap X = (accepted_catchUp S A : Nat) + 2 * healMargin S X + 3 := by rfl

/-- **The coefficient inequality (★)** of the nonfinal reset envelope, at every capability: the
`hheal` of `healthy_repair_schedule_of_finite_envelope` at the named `R = healthyResetCoeff` and
`r = healthyResetSlack`. -/
theorem accepted_heal_ge_reset (S : Setup) (A : AcceptanceAssumptions S) (cap : Capability)
    (X : ℕ+) :
    (accepted_catchUp S A : Nat) + 2 * (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 26) +
      healthyResetSlack S X + 3 ≤ accepted_heal S A cap X := by
  rw [accepted_heal_val, healMargin_val, healthyResetSlack_val]
  omega

/-- The final route's coefficient form `accepted_heal(final, X) ≥ C + 2 M_f`,
`M_f = 24 L_drain + 8k + 52δ_t + 52X + 44` at `λ = 2Δ` and `L_drain = healthyDrainLen`
(`heal_bound.md` §0.1). A budget for the final route, not a proof of its reset. -/
theorem accepted_heal_ge_final (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    (accepted_catchUp S A : Nat) +
        2 * (24 * healthyDrainLen S X + 8 * S.k + 52 * S.δt + 52 * (X : Nat) + 44) ≤
      accepted_heal S A .final X := by
  rw [accepted_heal_val]
  have := healMargin_ge_final S X
  omega

/-- Latency pays for the selected window and the final publication reserve. The final latency
`8(X + 3c) + 2`, `c = cF r`, covers the window of span `3c` (`finalWindow`); at `r = 1` it is
`8(X + 6) + 2`. The nonfinal latency `8X + 12` is independent of `r`. -/
def accepted_latency (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 8 * (X : Nat) + 12
  | .stable, X => 8 * (X : Nat) + 12
  | .final, X => 8 * ((X : Nat) + 3 * cF A.rowRatio) + 2

theorem accepted_latency_available (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .available X = 8 * (X : Nat) + 12 := by rfl

theorem accepted_latency_stable (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .stable X = 8 * (X : Nat) + 12 := by rfl

theorem accepted_latency_final (S : Setup) (A : AcceptanceAssumptions S) (X : ℕ+) :
    accepted_latency S A .final X = 8 * ((X : Nat) + 3 * cF A.rowRatio) + 2 := by rfl

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

/-- Standard fixed resilience fractions, the coefficient record `C`, and the numbers below.
Final progress is the chosen local pattern at every positive outer gap.
An abbreviation exposes the index type for the adapter signatures.

* row ratio `A.rowRatio`: the healthy regime assumes `ΔF ≤ r·Δ` (an envelope, never a deadline;
  final gap `cF r`).

Outage numbers (engine `Δe`, node `Δp = Δe + 1`, slot `4Δp`; slow arming only):
* arming lag `8k + 12`: `(8k+12)Δe ≥ (4k+6)Δp` for every `Δe ≥ 1` (equality only
  at `Δe = 1`, about `k + 1½` slots), so the label before the outage label is
  fully armed by `b₀`;
* no-sleep margin `max 38 (8k + 16)`: it covers the formation window
  (`(4k+6)Δp` before `b₀`), the restored votes (`8k + 16`) and the catch-up
  (`accepted_catchUp = max 37 (8k + 4)`, so `catchUp + 1 = max 38 (8k + 5)`), so the honest
  validators awake at the window start are ready on the recovery counts;
* recovery delay `18` (`18Δe ≥ 9Δp` for every `Δe ≥ 1`, equality only at
  `Δe = 1`): enough for the restored votes of the locked validators to bring
  the confirmed read back above the record (owner decision 2026-11-02;
  workbench 9f5d6a3, `outage_recovery_delay-readback-opus.md`);
* budget `4k − 6` and look-back `η = 0` (`Params.standard`): the outage regime is plain sleepy
  (Francesco 2026-11-02), and the budget is the bound the node time window needs
  (`acceptance_outage_times`).
These numbers are not claimed minimal. -/
abbrev acceptanceContract {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard C.catchUp (8 * S.k + 12)
    (4 * S.k - 6) C.heal C.latency with
    noSleep := max 38 (8 * S.k + 16), recovery := 18,
    rowRatio := A.rowRatio }
  progress := fun cap X => .recur ⟨if cap = .final then finalWindow A else Pattern.single, X⟩

theorem acceptanceContract_params_eq {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) :
    (acceptanceContract A C).params =
      { Params.standard C.catchUp (8 * S.k + 12)
        (4 * S.k - 6) C.heal C.latency with
        noSleep := max 38 (8 * S.k + 16), recovery := 18,
        rowRatio := A.rowRatio } := by rfl

theorem accepted_coefficients_catchUp (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).catchUp = accepted_catchUp S A := by rfl

theorem accepted_coefficients_heal (S : Setup) (A : AcceptanceAssumptions S) :
    (accepted_coefficients S A).heal = accepted_heal S A := by rfl

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
  have hb : ((4 * S.k - 6 : Nat) : Int) ≤ 4 * (S.k : Int) - 6 := hbcast.le
  change T + ((8 * S.k + 12 : Nat) : Int) * pub.Δ ≤ b₀ at hlag
  change b₁ ≤ b₀ + ((4 * S.k - 6 : Nat) : Int) * pub.Δ at hbudget
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

/-- The readiness duration of an acceptance contract with catch-up `≥ 37` covers `18 Δp`, for
any coefficient record `C`, so that it also serves the witnesses over `acceptanceContract A C`.
At `K S A` the premise is `accepted_catchUp_ge_sleepy`. -/
theorem cDur_ge_of_catchUp {S : Setup} (A : AcceptanceAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (C : AcceptanceCoefficients) (hC : 37 ≤ (C.catchUp : Nat))
    (r : (Sys (family S) V).Run) :
    18 * (r.1.Δ + 1) ≤ (Sys (family S) V).cDur (acceptanceContract A C) r := by
  have hd : (1 : Time) ≤ r.1.Δ := r.1.Δ_pos
  have hc : (37 : Time) ≤ (C.catchUp : Nat) := by exact_mod_cast hC
  change 18 * (r.1.Δ + 1) ≤ ((C.catchUp : Nat) : Time) * r.1.Δ
  nlinarith

/-- **The snapshot fit at readiness** for any coefficient record with catch-up `≥ 37`:
`c_z + Δp + 1 ≤ max ready 0 + 4Δp`, the `lo` condition of `snapshotCall_of_awake` at the frame
base `max ready 0 + 4Δp`. Generic in `C` as `cDur_ge_of_catchUp`; its instance at `K S A` is
`C := accepted_coefficients S A`, `hC := accepted_catchUp_ge_sleepy S A`. -/
theorem cutZ_fit_of_catchUp {S : Setup} (A : AcceptanceAssumptions S) (V : Type) [Fintype V]
    [DecidableEq V] (C : AcceptanceCoefficients) (hC : 37 ≤ (C.catchUp : Nat))
    (r : (Sys (family S) V).Run) (hn : 1 ≤ Fintype.card V) (g : Time) :
    Healing.cutZ (S.params (Model.pubOf r.1) hn).toParams g +
        (S.params (Model.pubOf r.1) hn).Δ + 1 ≤
      max ((Sys (family S) V).ready (acceptanceContract A C) g r) 0 +
        4 * (S.params (Model.pubOf r.1) hn).Δ := by
  have h := cDur_ge_of_catchUp A V C hC r
  have hΔ : (S.params (Model.pubOf r.1) hn).Δ = r.1.Δ + 1 := rfl
  exact Healing.cutZ_add_lt_ready_add _ g _ (by have := r.1.Δ_pos; rw [hΔ]; linarith)

end Consensus.Goldilocks.Refinement
end
