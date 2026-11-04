module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Instances.Goldilocks.AsChainShape

@[expose] public section

/-! # Goldilocks meets the shape obligations (statement)

The concrete acceptance endpoint of the Goldilocks family (`goldilocks S`, the node of
`AsChainShape` as a chain shape): for every setup `S` and every assumption set `A`, the family
meets `ShapeObligations` (`Spec/Shape/Obligations`: shape claims, admissible numbers, a served
ledger, progress that fits the skeleton and tolerates validators not ready and bad proposer slots)
at the contract `goldilocksContract A (contract_coefficients S A)`, whose every number is a closed
formula in the protocol parameters `k`, `δ_t`, the row ratio `r` and the outer gap `X`.

* **Assumptions** (`ContractAssumptions`): a row ratio `r ≥ 1` and the timeout
  `3·cF r ≤ δ_t` (`cF r = ⌈(r + 6)/4⌉`, `AsChainShape`). `Setup` fixes the genesis root,
  `δ_t`, the lock window `k ≥ 2`, the fast increment `c ≥ 2` (read by no coefficient) and the
  restart replay order.
* **Contract** (`goldilocksContract`): the standard thresholds, the row ratio, the outage
  numbers, and the progress patterns (`finalWindow A` for the final output, one honest ready
  proposer for the others, in every window of the outer gap).
* **Coefficients** (`contract_coefficients`): catch-up `contract_catchUp`, heal `contract_heal`
  and latency `contract_latency`. Only the final latency reads the assumptions (through `r`)
  directly; heal depends on `r` only through the `δ_t` that `3·cF r ≤ δ_t` requires.

The time numbers (catch-up, heal, latency, arming lag, outage budget, no-sleep margin, recovery
delay) are coefficients of `Δ`, the node and the engine delay alike (`Δp = Δe`: L0 delivers
strictly before the bound).

Statements only: no proofs here. -/

namespace Consensus.Goldilocks
open AsChainShape
open Blocks Shape

/-- The drain length `L_drain = 2k + X` of the nonfinal reset envelope. -/
def healthyDrainLen (S : Setup) (X : ℕ+) : Nat := 2 * S.k + X

/-- The margin `M_f = 20 L_drain + 8k + 28δ_t + 28X + 56` of the heal coefficient (the final
route's heal bound on the key-dependent rise-round route at `λ = 2Δ`); expanded,
`M_f = 48k + 28δ_t + 48X + 56`. It also covers the nonfinal reset envelope for `δ_t ≥ 6`
(`healMargin_ge_reset`, `Lemmas/Obligations/ResetCoefficients`). -/
def healMargin (S : Setup) (X : ℕ+) : Nat :=
  20 * healthyDrainLen S X + 8 * S.k + 28 * S.δt + 28 * X + 56

/-- Fixed row ratio and timeout assumptions. The row ratio `r` bounds the engine row delay
by `ΔF ≤ r·Δ` in the healthy regime (`Params.fgDelay`); the timeout pays the route-A window at
the row gap `cF r` (`AsChainShape`), `3·cF r ≤ δ_t`. The final pattern is determined by these,
not chosen by a caller; outer gaps never enter the timeout bound. The outage regime is plain
sleepy (`η = 0`), so no outage look-back is assumed. -/
structure ContractAssumptions (S : Setup) where
  fgDelay : ℕ+
  timeout : 3 * cF fgDelay ≤ S.δt

/-- Route-A four-anchor window `[0, c, 2c, 3c]` at the row gap `c = cF r` of the assumptions'
row ratio (span `3c ≤ δ_t`, `A.timeout`). At `r = 1`, `c = 2`: `[0, 2, 4, 6]`. -/
def finalWindow {S : Setup} (A : ContractAssumptions S) : Pattern :=
  ⟨[0, cF A.fgDelay, 2 * cF A.fgDelay, 3 * cF A.fgDelay], by simp⟩

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure ContractCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- Catch-up `19` delays: it covers the Sleepy margin, `18Δ + 1 ≤ 19Δ` for every delay
`Δ ≥ 1`. -/
def contract_catchUp (S : Setup) (_A : ContractAssumptions S) : ℕ+ :=
  ⟨19, by decide⟩

/-- The finite healing witness `catchUp + M_f`, `M_f = healMargin S X`, at every capability: a
closed expression in `k`, `δ_t`, `X` and the catch-up, fixed before any run; expanded,
`48k + 28δ_t + 48X + 75`. -/
def contract_heal (S : Setup) (A : ContractAssumptions S) : Capability → ℕ+ → Nat :=
  fun _ X => (contract_catchUp S A : Nat) + healMargin S X

/-- Latency pays for the selected window and the final publication reserve. The final latency
`4(X + 3c) + 1`, `c = cF r`, covers the window of span `3c` (`finalWindow`) and one delay; at
`r = 1` it is `4(X + 6) + 1`. The nonfinal latency `4X + 6` is independent of `r`. -/
def contract_latency (S : Setup) (A : ContractAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 4 * (X : Nat) + 6
  | .stable, X => 4 * (X : Nat) + 6
  | .final, X => 4 * ((X : Nat) + 3 * cF A.fgDelay) + 1

/-- The guarantee coefficients of the endpoint: catch-up `contract_catchUp`, heal
`contract_heal` and latency `contract_latency`. -/
noncomputable def contract_coefficients (S : Setup) (A : ContractAssumptions S) :
    ContractCoefficients where
  catchUp := contract_catchUp S A
  heal := contract_heal S A
  latency := contract_latency S A

/-- Standard fixed resilience fractions, the coefficient record `C`, and the numbers below.
Final progress is the chosen local pattern at every positive outer gap.
An abbreviation exposes the index type for the adapter signatures.

* row ratio `A.fgDelay`: the healthy regime assumes `ΔF ≤ r·Δ` (an envelope, never a deadline;
  final gap `cF r`).

Outage numbers (slot `4Δ`; slow arming only):
* arming lag `4k + 6`: the label before the outage label (`k + 1½` slots before `b₀`) is fully
  armed by `b₀`;
* no-sleep margin `4k + 6`: the window `[b₀ − (4k+6)Δ, b₁ + (4k+6)Δ]` starts by `t_{j₀ − k}` (the
  formation window of the arming lock) and ends after the restored votes of labels up to
  `j₀ + k`;
* recovery delay `9`: enough for the restored votes of the locked validators to bring
  the confirmed read back above the record;
* budget `4k − 5` and look-back `η = 0` (`Params.standard`): the outage regime is plain sleepy;
  `4k − 5` is the bound of the obligations proof (the lock window keeps an unpolluted label for
  outages up to `(4k − 5)Δ`, `exists_unpolluted_label`).
The decisions behind these numbers are in `docs/decisions.md`.
These numbers are not claimed minimal. -/
abbrev goldilocksContract {S : Setup} (A : ContractAssumptions S)
    (C : ContractCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard (catchUp := C.catchUp) (lag := 4 * S.k + 6)
      (budget := 4 * S.k - 5) (heal := C.heal) (latency := C.latency) with
    noSleep := 4 * S.k + 6
    recovery := 9
    fgDelay := A.fgDelay }
  progress := fun cap X =>
    .recur { pattern := if cap = .final then finalWindow A else Pattern.single, gap := X }

/-- **Goldilocks meets the obligations**, the concrete endpoint: for every setup and every
assumption set (a row ratio `r` and the timeout `3·cF r ≤ δ_t`), the Goldilocks family meets the
obligations at the contract `goldilocksContract A (contract_coefficients S A)`, every number of
which is fixed above. -/
def MeetsObligations : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S),
    ShapeObligations (goldilocks S) (goldilocksContract A (contract_coefficients S A))

end Consensus.Goldilocks

end
