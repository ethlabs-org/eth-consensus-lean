module
public import ConsensusLean.Spec.Shape.Accepted
public import ConsensusLean.Instances.Goldilocks.Refinement.Defs

@[expose] public section

/-! # Goldilocks milestone Accepted (statement)

The concrete acceptance endpoint of the Goldilocks family (`family S`, the node of
`Refinement/Defs` as a chain shape): for every setup `S` and every assumption set `A`, the family
is `Accepted` (`Spec/Shape/Accepted`: shape claims, admissible numbers, a served ledger, progress
that fits the skeleton and tolerates validators not ready and bad proposer slots) at the contract
`acceptanceContract A (accepted_coefficients S A)`, whose every number is a closed formula in the
protocol parameters `k`, `δ_t`, the row ratio `r` and the outer gap `X`.

* **Assumptions** (`AcceptanceAssumptions`): a row ratio `r ≥ 1` and the timeout
  `3·cF r ≤ δ_t` (`cF r = ⌈(r + 6)/4⌉`, `Refinement/Defs`). `Setup` fixes the genesis root,
  `δ_t`, the lock window `k ≥ 2` and the restart replay order.
* **Contract** (`acceptanceContract`): the standard thresholds; row ratio `r` (the healthy regime
  assumes `ΔF ≤ r·Δ`); arming lag `8k + 12`, outage budget `4k − 6`, look-back `η = 0` (plain
  sleepy outage), no-sleep margin `max 38 (8k + 16)` and recovery delay `18` (engine
  `Δ`-coefficients); final progress the pattern `finalWindow A` (`[0, c, 2c, 3c]`, `c = cF r`)
  and one honest ready proposer for the other outputs, in every window of the outer gap.
* **Coefficients** (`accepted_coefficients`, engine `Δ`-coefficients): catch-up
  `max 37 (8k + 4)`; heal `max 37 (8k + 4) + 128k + 112δ_t + 160X + 187` at every capability
  (`catchUp + 2·healMargin + 3`, `healMargin = 64k + 56δ_t + 80X + 92`); latency `8X + 12` for
  the available and stable outputs and `8(X + 3·cF r) + 2` for the final one. Only the final
  latency reads the assumptions (through `r`); the heal coefficient ignores the capability.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- The drain length `L_drain = 2k + X` of the nonfinal reset envelope. -/
def healthyDrainLen (S : Setup) (X : ℕ+) : Nat := 2 * S.k + X

/-- The reset coefficient `R = 24·L_drain + 48(δ_t + X) + 28` of the nonfinal reset envelope. -/
def healthyResetCoeff (S : Setup) (X : ℕ+) : Nat := 24 * healthyDrainLen S X + 48 * (S.δt + X) + 28

/-- The literal slack `r = 0` of the nonfinal reset envelope. -/
def healthyResetSlack (_S : Setup) (_X : ℕ+) : Nat := 0

/-- The margin `M = R + 16k + 8δ_t + 8X + 64` of the heal coefficient; expanded,
`M = 64k + 56δ_t + 80X + 92`. -/
def healMargin (S : Setup) (X : ℕ+) : Nat :=
  healthyResetCoeff S X + 16 * S.k + 8 * S.δt + 8 * X + 64

/-- Fixed row ratio and timeout assumptions. The row ratio `r` bounds the engine row delay
by `ΔF ≤ r·Δ` in the healthy regime (`Params.rowRatio`); the timeout pays the route-A window at
the row gap `cF r` (`Refinement/Defs`), `3·cF r ≤ δ_t`. The final pattern is determined by these,
not chosen by a caller; outer gaps never enter the timeout bound. The outage regime is plain
sleepy (`η = 0`, Francesco 2026-11-02), so no outage look-back is assumed. -/
structure AcceptanceAssumptions (S : Setup) where
  rowRatio : ℕ+
  timeout : 3 * cF rowRatio ≤ S.δt

/-- Route-A four-anchor window `[0, c, 2c, 3c]` at the row gap `c = cF r` of the assumptions'
row ratio (span `3c ≤ δ_t`, `A.timeout`). At `r = 1`, `c = 2`: `[0, 2, 4, 6]`. -/
def finalWindow {S : Setup} (A : AcceptanceAssumptions S) : Pattern :=
  ⟨[0, cF A.rowRatio, 2 * cF A.rowRatio, 3 * cF A.rowRatio], by simp⟩

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure AcceptanceCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- Catch-up `max 37 (8k + 4)`: it covers the Sleepy margin and the outage history window. -/
def accepted_catchUp (S : Setup) (_A : AcceptanceAssumptions S) : ℕ+ :=
  ⟨max 37 (8 * S.k + 4), lt_of_lt_of_le (by decide) (Nat.le_max_left _ _)⟩

/-- The finite healing witness `catchUp + 2M + 3`, `M = healMargin S X`, at every capability: a
closed expression in `k`, `δ_t`, `X` and the catch-up, fixed before any run; expanded,
`max 37 (8k + 4) + 128k + 112δ_t + 160X + 187`. `M` is read off the reset envelope of the
healing route and covers the final route's heal-bound margin. -/
def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) : Capability → ℕ+ → Nat :=
  fun _ X => (accepted_catchUp S A : Nat) + 2 * healMargin S X + 3

/-- Latency pays for the selected window and the final publication reserve. The final latency
`8(X + 3c) + 2`, `c = cF r`, covers the window of span `3c` (`finalWindow`); at `r = 1` it is
`8(X + 6) + 2`. The nonfinal latency `8X + 12` is independent of `r`. -/
def accepted_latency (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 8 * (X : Nat) + 12
  | .stable, X => 8 * (X : Nat) + 12
  | .final, X => 8 * ((X : Nat) + 3 * cF A.rowRatio) + 2

/-- The guarantee coefficients of the endpoint: catch-up `accepted_catchUp`, heal
`accepted_heal` and latency `accepted_latency`. -/
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
  (Francesco 2026-11-02), and the budget is the bound that the node-level outage timing needs
  (the node time window).
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

/-- **Goldilocks Accepted**, the concrete endpoint: for every setup and every assumption set (a
row ratio `r` and the timeout `3·cF r ≤ δ_t`), the Goldilocks family is accepted at the contract
`acceptanceContract A (accepted_coefficients S A)`, every number of which is fixed above. -/
def AcceptedEndpoint : Prop :=
  ∀ (S : Setup) (A : AcceptanceAssumptions S),
    Accepted (family S) (acceptanceContract A (accepted_coefficients S A))

end Consensus.Goldilocks.Refinement

end
