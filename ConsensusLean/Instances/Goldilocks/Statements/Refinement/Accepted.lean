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
  assumes `ΔF ≤ r·Δ`); arming lag `4k + 6`, outage budget `4k − 5`, look-back `η = 0` (plain
  sleepy outage), no-sleep margin `4k + 6` and recovery delay `9` (`Δ`-coefficients; node and
  engine delay agree, `Δp = Δe`); final progress the pattern `finalWindow A` (`[0, c, 2c, 3c]`,
  `c = cF r`) and one honest ready proposer for the other outputs, in every window of the outer
  gap.
* **Coefficients** (`accepted_coefficients`, `Δ`-coefficients): catch-up `19`; heal
  `56k + 52δ_t + 76X + 63` at every capability (`catchUp + healMargin`,
  `healMargin = 56k + 52δ_t + 76X + 44`); latency `4X + 6` for the available and stable outputs
  and `4(X + 3·cF r) + 1` for the final one. Only the final latency reads the assumptions
  (through `r`) directly; heal depends on `r` only through the `δ_t` that `3·cF r ≤ δ_t`
  requires, and the heal coefficient ignores the capability.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks.Refinement
open Blocks Shape

/-- The drain length `L_drain = 2k + X` of the nonfinal reset envelope. -/
def healthyDrainLen (S : Setup) (X : ℕ+) : Nat := 2 * S.k + X

/-- The margin `M_f = 24 L_drain + 8k + 52δ_t + 52X + 44` of the heal coefficient (the final
route's heal bound at `λ = 2Δ`); expanded, `M_f = 56k + 52δ_t + 76X + 44`. It also covers the
nonfinal reset envelope, `R + 8k + 4X + 29 ≤ M_f` for `δ_t ≥ 6`. -/
def healMargin (S : Setup) (X : ℕ+) : Nat :=
  24 * healthyDrainLen S X + 8 * S.k + 52 * S.δt + 52 * X + 44

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

/-- Catch-up `19` delays: it covers the Sleepy margin, `18Δ + 1 ≤ 19Δ` for every delay `Δ ≥ 1`
(node and engine delay agree, `Δp = Δe`). -/
def accepted_catchUp (S : Setup) (_A : AcceptanceAssumptions S) : ℕ+ :=
  ⟨19, by decide⟩

/-- The finite healing witness `catchUp + M_f`, `M_f = healMargin S X`, at every capability: a
closed expression in `k`, `δ_t`, `X` and the catch-up, fixed before any run; expanded,
`56k + 52δ_t + 76X + 63`. In delays `Δ` (node and engine alike, `Δp = Δe`), `M_f` is the final
route's heal-bound margin and covers the nonfinal reset envelope. -/
def accepted_heal (S : Setup) (A : AcceptanceAssumptions S) : Capability → ℕ+ → Nat :=
  fun _ X => (accepted_catchUp S A : Nat) + healMargin S X

/-- Latency pays for the selected window and the final publication reserve. The final latency
`4(X + 3c) + 1`, `c = cF r`, covers the window of span `3c` (`finalWindow`) and one delay; at
`r = 1` it is `4(X + 6) + 1`. The nonfinal latency `4X + 6` is independent of `r`. -/
def accepted_latency (S : Setup) (A : AcceptanceAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 4 * (X : Nat) + 6
  | .stable, X => 4 * (X : Nat) + 6
  | .final, X => 4 * ((X : Nat) + 3 * cF A.rowRatio) + 1

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

Outage numbers (in delays `Δ`, node and engine alike since L0 delivers strictly before the bound,
`Δp = Δe`; slot `4Δ`; slow arming only):
* arming lag `4k + 6`: the label before the outage label (`k + 1½` slots before `b₀`) is fully
  armed by `b₀`;
* no-sleep margin `4k + 6`: the window `[b₀ − (4k+6)Δ, b₁ + (4k+6)Δ]` starts by `t_{j₀ − k}` (the
  formation window of the arming lock) and ends after the restored votes of labels up to
  `j₀ + k`;
* recovery delay `9`: enough for the restored votes of the locked validators to bring
  the confirmed read back above the record (owner decision 2026-11-02;
  workbench 9f5d6a3, `outage_recovery_delay-readback-opus.md`);
* budget `4k − 5` and look-back `η = 0` (`Params.standard`): the outage regime is plain sleepy
  (Francesco 2026-11-02); `4k − 5` is the bound of the Accepted proof (the lock window keeps an
  unpolluted label for outages up to `(4k − 5)Δ`, `exists_unpolluted_label`; Francesco
  2026-11-03, was `4k − 6`).
These numbers are not claimed minimal. -/
abbrev acceptanceContract {S : Setup} (A : AcceptanceAssumptions S)
    (C : AcceptanceCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard C.catchUp (4 * S.k + 6)
    (4 * S.k - 5) C.heal C.latency with
    noSleep := 4 * S.k + 6, recovery := 9,
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
