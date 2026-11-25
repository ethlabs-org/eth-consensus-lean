module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Instances.Goldilocks.AsChainShape

@[expose] public section

/-! # Goldilocks meets the shape obligations (statement)

The concrete obligations endpoint of the Goldilocks family at the setup's vote binding
(`goldilocks S`, the node of `AsChainShape` as a chain shape): for every setup `S` and every
assumption set `A`, the family meets the shape obligations (shape claims, admissible numbers, a
served ledger, progress that fits the skeleton and tolerates validators not ready and bad proposer
slots) on every run, faults growing over it, as an Ebb-and-Flow protocol
(`ShapeObligationsAs .ebbAndFlow`: the schema provides all three capabilities, available and
stable aliased to `confirmed`, final served by `finalized`), at the contract
`goldilocksContract A (contract_coefficients S A)`, whose every number is a closed formula in the
protocol parameters `k`, `δ_t`, the FG delay in slots `fgSlots`, the signing gap `G`, the
release gap `R`, and the outer gap `X`.

* **Assumptions** (`ContractAssumptions`): the FG delay in slots `fgSlots ≥ 2` and the timeout
  `3·finalSlots ≤ δ_t`, where `finalSlots = ⌈(6 + fgDelay + R + G)/4⌉`. Each validator has a
  public signing appointment within the signing-gap bound and a release time within the
  release-gap bound. Healthy runs have
  `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC` (the contract's FG delay
  bound is `fgDelay = 4·fgSlots − 6`): the FG attestations of a round reach every node within
  `fgSlots` slots, the paper's `c_F = ⌈(6Δ + Δ_F)/(4Δ)⌉ ≤ fgSlots`. `Setup` fixes the genesis root,
  `δ_t`, the lock window `k ≥ 2`, the fast increment `c ≥ 2` (read by no coefficient), the
  optimistic switch (on by default; read by no coefficient) and the restart replay order, vote
  binding, signing calendar and release schedule.
  The endpoint and headlines hold at every vote binding for calendars and schedules satisfying
  the gap bounds.
* **Contract** (`goldilocksContract`): the standard thresholds, the FG delay bound, the outage
  numbers, and the progress patterns (`finalWindow A` for the final output, one honest ready
  proposer for the others, in every window of the outer gap).
* **Coefficients** (`contract_coefficients`): catch-up `contract_catchUp`, heal `contract_heal`
  and latency `contract_latency`. Only the final latency depends on `finalSlots`; the heal
  coefficient includes `5G` for signing waits and no release term (a held attestation delays
  delivery, which the timeout `3·finalSlots ≤ δ_t` pays, not a report).

The time numbers (catch-up, heal, latency, arming lag, outage budget, outage look-back, recovery
delay) are coefficients of `ΔAC`, the node and the engine delay alike (`Δp = Δe`: L0 delivers
strictly before the bound).

**The certified statements**: the endpoint `MeetsObligations`, the headline `GoldilocksCorrect`
(with `ObligationsSufficient`) and the per-run headline `GoldilocksCorrectWithExcuses`.
The endpoint's shape claims include outage resilience and sleepy safety and liveness.

Statements only: no proofs here. -/

namespace Consensus.Goldilocks
open AsChainShape
open Blocks Shape
open Consensus.Model (Public)

/-- The drain length `L_drain = 2k + X` of the nonfinal reset envelope. -/
def healthyDrainLen (S : Setup) (X : ℕ+) : Nat := 2 * S.k + X

/-- Fixed FG delay, signing-gap and timeout assumptions. `fgSlots` is the FG delay in slots
(`4ΔAC` each): the healthy regime assumes `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC` (`fgDelay`), the
paper's `c_F ≤ fgSlots`; the timeout pays the route-A window including the signing wait. The final
pattern is determined by these, not chosen by a caller; outer gaps never enter the timeout
bound. The contract fixes the outage look-back at `η = 12k + 7`, independently of these
timing assumptions. -/
structure ContractAssumptions (S : Setup) where
  fgSlots : Nat
  two_le_fgSlots : 2 ≤ fgSlots
  /-- Maximum signing wait in protocol-delay units after the next public time. -/
  signGap : Nat := 0
  /-- Every validator has a public signing appointment within the gap bound. -/
  sign_liveness : ∀ (pub : Public) (y : Fin pub.n) (t : Time), 0 ≤ t →
    ∃ t', t ≤ t' ∧ t' < t + ((signGap : Time) + 1) * pub.ΔAC ∧
      pub.ΔAC ∣ t' ∧ S.sign pub y t' = true
  /-- Maximum wait, in protocol-delay units, from a signing to the release of the attestation. -/
  releaseGap : Nat := 0
  /-- Every validator may release within the gap bound from every time; at `releaseGap = 0`
  the schedule releases at every time `t ≥ 0`. -/
  release_liveness : ∀ (pub : Public) (y : Fin pub.n) (t : Time), 0 ≤ t →
    ∃ t', t ≤ t' ∧ t' ≤ t + (releaseGap : Time) * pub.ΔAC ∧ S.release pub y t' = true
  timeout : 3 * ((6 + (4 * fgSlots - 6) + releaseGap + signGap + 3) / 4) ≤ S.δt

/-- The contract's FG delay bound `4·fgSlots − 6` (positive, `fgSlots ≥ 2`): the healthy regime's
`ΔFG ≤ (4·fgSlots − 6)·ΔAC` is `6·ΔAC + ΔFG ≤ 4·fgSlots·ΔAC`. -/
def ContractAssumptions.fgDelay {S : Setup} (A : ContractAssumptions S) : ℕ+ :=
  ⟨4 * A.fgSlots - 6, by have := A.two_le_fgSlots; omega⟩

/-- Final anchor spacing `⌈(6 + fgDelay + R + G)/4⌉` in slots. -/
def ContractAssumptions.finalSlots {S : Setup} (A : ContractAssumptions S) : Nat :=
  (6 + (A.fgDelay : Nat) + A.releaseGap + A.signGap + 3) / 4

/-- Route-A four-anchor window `[0, c′, 2c′, 3c′]` at `c′ = finalSlots`. -/
def finalWindow {S : Setup} (A : ContractAssumptions S) : Pattern :=
  ⟨[0, A.finalSlots, 2 * A.finalSlots, 3 * A.finalSlots], by simp⟩

/-- The heal margin `20 L_drain + 8k + 28δ_t + 28X + 56 + 5G` allows for five signing waits. -/
def healMargin (S : Setup) (A : ContractAssumptions S) (X : ℕ+) : Nat :=
  20 * healthyDrainLen S X + 8 * S.k + 28 * S.δt + 28 * X + 56 + 5 * A.signGap

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

/-- The finite healing witness `catchUp + healMargin S A X` at every capability; expanded,
`48k + 28δ_t + 48X + 75 + 5G`. -/
def contract_heal (S : Setup) (A : ContractAssumptions S) : Capability → ℕ+ → Nat :=
  fun _ X => (contract_catchUp S A : Nat) + healMargin S A X

/-- Latency pays for the selected window and the final publication reserve. The final latency
`4(X + 3·finalSlots) + 1` covers the window of span `3·finalSlots` and one delay. The nonfinal
latency is `4X + 6`. -/
def contract_latency (S : Setup) (A : ContractAssumptions S) :
    Capability → ℕ+ → Nat
  | .available, X => 4 * (X : Nat) + 6
  | .stable, X => 4 * (X : Nat) + 6
  | .final, X => 4 * ((X : Nat) + 3 * A.finalSlots) + 1

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
  deadline; final gap `finalSlots` also accounts for signing and release waits).

Outage numbers (slot `4ΔAC`; slow arming only):
* arming lag `4k + 6`: the label before the outage label (`k + 1½` slots before `b₀`) is fully
  armed by `b₀`;
* look-back `η = 12k + 7`: the proof window
  `[b₀ − (4k+6)ΔAC, b₁ + (4k+6)ΔAC]` has length at most
  `(budget + 2(4k+6))ΔAC = (12k+7)ΔAC`;
* outage participation catch-up `max cDur (η·ΔAC − 1)`: readiness covers the whole
  look-back, since `Ready c` requires `c + 1` awake time units. Readers keep `cDur`;
* recovery delay `9`: enough for the restored votes of the locked validators to bring
  the confirmed read back above the record;
* budget `4k − 5`: the bound of the obligations proof (the lock window keeps an unpolluted label for
  outages up to `(4k − 5)ΔAC`, `exists_unpolluted_label`).
The reasons behind these numbers are in `docs/decisions.md` §"Contract numbers".
The growing-fault windows (`docs/decisions.md` §"Adversary growth"):
* sleepy look-ahead `ahead = 5`: support at the participation point `t_s + Δ` of a
  slot's votes is last counted by the slot's confirmation update at `t_s + 6Δ`;
* proposer hold `1`: a proposer honest through `t_s + Δ`, when the slot's votes are
  cast, cannot split them with a second proposal of its slot;
* committee look-ahead `5`: the same fault charge as the population clause. At every run time,
  the bound holds for every nonempty committee selected in the preceding `η·ΔAC`, restricted
  to nonnegative selection times. This includes the proof's committees at one common observation
  time. Each look-ahead is set from its own consumer.
These numbers are not claimed minimal. -/
abbrev goldilocksContract {S : Setup} (A : ContractAssumptions S)
    (C : ContractCoefficients) : Contract ProgressReq where
  Idx := ℕ+
  idx_nonempty := ⟨1⟩
  params := { Params.standard (catchUp := C.catchUp) (lag := 4 * S.k + 6)
      (budget := 4 * S.k - 5) (heal := C.heal) (latency := C.latency) with
    η := 12 * S.k + 7
    recovery := 9
    fgDelay := A.fgDelay
    ahead := 5
    committeeAhead := 5 }
  progress := fun cap X =>
    .recur
      { pattern := if cap = .final then finalWindow A else Pattern.single
        gap := X
        hold := 1 }

/-- **Goldilocks meets the obligations**, the concrete endpoint: for every setup and every
assumption set (the FG delay, signing-gap and release-gap bounds and timeout), the
Goldilocks family at the setup's vote binding meets the obligations as an Ebb-and-Flow protocol,
for every finite validator type, including the empty type (its schema provides exactly
the final, stable and available capabilities; available and stable are both the `confirmed`
output) at the contract `goldilocksContract A (contract_coefficients S A)`, every number of which
is fixed above. -/
def MeetsObligations : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S),
    ShapeObligationsAs .ebbAndFlow (goldilocks S)
      (goldilocksContract A (contract_coefficients S A))

/-- **Goldilocks is correct and optimally fault tolerant**, the headline statement:
for every setup `S`, every assumption set
`A` (the FG delay, signing-gap and release-gap bounds and timeout) and every finite
validator type `V`, including the empty type, the family at `S`'s vote binding, compiled and run
by the general execution model (`sysOf schema (compiled (goldilocks S)) V`, with progress read by
`shapeProgress`), is an L0
`CorrectProtocol` at the contract `goldilocksContract A (contract_coefficients S A)`,
whose fractions satisfy `Params.OptimalFaultTolerance`. Correctness composes
`MeetsObligations` with the review statement `ObligationsSufficient`; optimality
pins the contract's fractions. Neither conjunct adds a hypothesis. The engine has no slashing
protection, so the non-framing row of `CorrectProtocol` is Goldilocks' own: it comes from the
endpoint's obligation that slashing protection never fires (`Shape.GuardIdleAlways`). -/
def GoldilocksCorrect : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    CorrectProtocol (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V)
      (goldilocksContract A (contract_coefficients S A)) ∧
      (goldilocksContract A (contract_coefficients S A)).params.OptimalFaultTolerance

/-- **Goldilocks is correct or a binding fails.** For every setup, timing
assumption set and finite validator type, including the empty type, on every structurally valid
run of the family at the setup's vote binding the
entire correctness property table holds on the single run `r` (validity means
"is `r`"), or a signature forgery, credential failure or inadmissible selection
holds. Collisions excuse only `Holds` rows, never `HoldsAlways` rows. The laws
`convicts_mono` and `view_mono` remain global over all runs. `SelValid` ranges
over every selection role, including slots beyond the horizon; selection is
external data fixed before execution, so a failure need not be an observed event.
No execution binding is an antecedent. Network regimes and proposer progress
remain the premises of their respective rows. Adequacy and realizability retain
their original valid, binding-sound, collision-free witnesses. -/
def GoldilocksCorrectWithExcuses : Prop :=
  ∀ (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V],
    CorrectProtocolWithExcuses (Model.sysOf schema (compiled (goldilocks S)) V)
      (shapeProgress (goldilocks S) V)
      (goldilocksContract A (contract_coefficients S A))
      (fun r => r.2.StructuralValid) (fun r => r.2.BindingFailure)

end Consensus.Goldilocks

end
