module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Instances.Goldilocks.AsChainShape

@[expose] public section

/-! # Goldilocks meets the shape obligations (statement)

The concrete obligations endpoint of the Goldilocks family (`goldilocks S`, the node of
`AsChainShape` as a chain shape): for every setup `S` and every assumption set `A`, the family
meets `ShapeObligations` (`Spec/Shape/Obligations`: shape claims, admissible numbers, a served
ledger, progress that fits the skeleton and tolerates validators not ready and bad proposer slots)
at the contract `goldilocksContract A (contract_coefficients S A)`, whose every number is a closed
formula in the protocol parameters `k`, `δ_t`, the FG delay in slots `fgSlots` and the outer
gap `X`.

* **Assumptions** (`ContractAssumptions`): the FG delay in slots `fgSlots ≥ 2` and the timeout
  `3·fgSlots ≤ δ_t`. Healthy runs have `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC` (the contract's FG delay
  bound is `fgDelay = 4·fgSlots − 6`): the FG attestations of a round reach every node within
  `fgSlots` slots, the paper's `c_F = ⌈(6Δ + Δ_F)/(4Δ)⌉ ≤ fgSlots`. `Setup` fixes the genesis root,
  `δ_t`, the lock window `k ≥ 2`, the fast increment `c ≥ 2` (read by no coefficient) and the
  restart replay order.
* **Contract** (`goldilocksContract`): the standard thresholds, the FG delay bound, the outage
  numbers, and the progress patterns (`finalWindow A` for the final output, one honest ready
  proposer for the others, in every window of the outer gap).
* **Coefficients** (`contract_coefficients`): catch-up `contract_catchUp`, heal `contract_heal`
  and latency `contract_latency`. Only the final latency reads the assumptions (`fgSlots`)
  directly; heal depends on `fgSlots` only through the `δ_t` that `3·fgSlots ≤ δ_t` requires.

The time numbers (catch-up, heal, latency, arming lag, outage budget, no-sleep margin, recovery
delay) are coefficients of `ΔAC`, the node and the engine delay alike (`Δp = Δe`: L0 delivers
strictly before the bound).

**The headline** (`GoldilocksCorrect`): with `ObligationsSufficient`, the endpoint makes the
Goldilocks family, run by the general execution model, an L0 `CorrectProtocol` at that contract.

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

/-- Fixed FG delay and timeout assumptions. `fgSlots` is the FG delay in slots (`4ΔAC` each):
the healthy regime assumes `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC` (`fgDelay`, `Params.fgDelay`), the
paper's `c_F ≤ fgSlots`; the timeout pays the route-A window, `3·fgSlots ≤ δ_t`. The final
pattern is determined by these, not chosen by a caller; outer gaps never enter the timeout
bound. The outage regime is plain sleepy (`η = 0`), so no outage look-back is assumed. -/
structure ContractAssumptions (S : Setup) where
  fgSlots : Nat
  two_le_fgSlots : 2 ≤ fgSlots
  timeout : 3 * fgSlots ≤ S.δt

/-- The contract's FG delay bound `4·fgSlots − 6` (positive, `fgSlots ≥ 2`): the healthy regime's
`ΔFG ≤ (4·fgSlots − 6)·ΔAC` is `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC`. -/
def ContractAssumptions.fgDelay {S : Setup} (A : ContractAssumptions S) : ℕ+ :=
  ⟨4 * A.fgSlots - 6, by have := A.two_le_fgSlots; omega⟩

/-- Route-A four-anchor window `[0, c, 2c, 3c]` at `c = fgSlots` (span `3c ≤ δ_t`, `A.timeout`).
At `fgSlots = 2`: `[0, 2, 4, 6]`. -/
def finalWindow {S : Setup} (A : ContractAssumptions S) : Pattern :=
  ⟨[0, A.fgSlots, 2 * A.fgSlots, 3 * A.fgSlots], by simp⟩

/-- Only guarantees are chosen: positive finite catch-up and finite heal/latency
coefficients at every capability and outer gap. -/
structure ContractCoefficients where
  catchUp : ℕ+
  heal : Capability → ℕ+ → Nat
  latency : Capability → ℕ+ → Nat

/-- Catch-up `19` delays: it covers the Sleepy margin, `18ΔAC + 1 ≤ 19ΔAC` for every delay
`ΔAC ≥ 1`. -/
def contract_catchUp (S : Setup) (_A : ContractAssumptions S) : ℕ+ :=
  ⟨19, by decide⟩

/-- The finite healing witness `catchUp + M_f`, `M_f = healMargin S X`, at every capability: a
closed expression in `k`, `δ_t`, `X` and the catch-up, fixed before any run; expanded,
`48k + 28δ_t + 48X + 75`. -/
def contract_heal (S : Setup) (A : ContractAssumptions S) : Capability → ℕ+ → Nat :=
  fun _ X => (contract_catchUp S A : Nat) + healMargin S X

/-- Latency pays for the selected window and the final publication reserve. The final latency
`4(X + 3·fgSlots) + 1` covers the window of span `3·fgSlots` (`finalWindow`) and one delay; at
`fgSlots = 2` it is `4(X + 6) + 1`. The nonfinal latency `4X + 6` is independent of `fgSlots`. -/
def contract_latency (S : Setup) (A : ContractAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 4 * (X : Nat) + 6
  | .stable, X => 4 * (X : Nat) + 6
  | .final, X => 4 * ((X : Nat) + 3 * A.fgSlots) + 1

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

* FG delay bound `A.fgDelay = 4·fgSlots − 6`: the healthy regime assumes
  `ΔFG ≤ (4·fgSlots − 6)·ΔAC`, i.e. `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC` (an envelope, never a
  deadline; final gap `fgSlots`).

Outage numbers (slot `4ΔAC`; slow arming only):
* arming lag `4k + 6`: the label before the outage label (`k + 1½` slots before `b₀`) is fully
  armed by `b₀`;
* no-sleep margin `4k + 6`: the window `[b₀ − (4k+6)ΔAC, b₁ + (4k+6)ΔAC]` starts by
  `t_{j₀ − k}` (the formation window of the arming lock) and ends after the restored votes of
  labels up to `j₀ + k`;
* recovery delay `9`: enough for the restored votes of the locked validators to bring
  the confirmed read back above the record;
* budget `4k − 5` and look-back `η = 0` (`Params.standard`): the outage regime is plain sleepy;
  `4k − 5` is the bound of the obligations proof (the lock window keeps an unpolluted label for
  outages up to `(4k − 5)ΔAC`, `exists_unpolluted_label`).
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
assumption set (the FG delay in slots `fgSlots ≥ 2` and the timeout `3·fgSlots ≤ δ_t`), the
Goldilocks family meets the obligations at the contract
`goldilocksContract A (contract_coefficients S A)`, every number of which is fixed above. -/
def MeetsObligations : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S),
    ShapeObligations (goldilocks S) (goldilocksContract A (contract_coefficients S A))

/-- **Goldilocks is correct**, the headline statement: for every setup `S`, every assumption set
`A` (the FG delay in slots `fgSlots ≥ 2` and the timeout `3·fgSlots ≤ δ_t`) and every finite
validator type `V`, the Goldilocks family, compiled and run by the general execution model
(`sysOf schema (compiled (goldilocks S)) V`, with progress read by `shapeProgress`), is an L0
`CorrectProtocol` at the contract `goldilocksContract A (contract_coefficients S A)`. It composes
`MeetsObligations` with the review statement `ObligationsSufficient`; it has their parameters and
no further hypothesis. -/
def GoldilocksCorrect : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    CorrectProtocol (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V) (goldilocksContract A (contract_coefficients S A))

end Consensus.Goldilocks

end
