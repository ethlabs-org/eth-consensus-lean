module
public import ConsensusLean.Proofs.Comparison.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.Main
public import ConsensusLean.Proofs.ComparisonCoverage.Main

@[expose] public section

/-! # Comparison registry: the proved Slice 0 instances (Lean index)

One entry per proved profile instance: the statement it proves (whose type fixes the bound
function, the tier and the premises), proved by its proof, with its axioms pinned. Columns of each
docstring: **bound** (the bound function), **tier** (R: over every L0 system or the compiled
protocol; A: over AC traces of the Goldilocks SA), **premises** (what the instance
assumes beyond the profile's class). A new instance adds an entry here.

| statement | bound | tier | premises |
|---|---|---|---|
| `HealDefault0` | `hsDefault`, `hlDefault`, `latDefault` | R | `Behaviour` |
| `TxLatencyDefault0` | `txLatDefault` | R | `Behaviour` |
| `GoldilocksHealDefault0` | the same, at the endpoint's contract | R | none (the endpoint) |
| `GoldilocksTxLatencyDefault0` | `txLatDefault`, endpoint contract | R | none (the endpoint) |
| `HealProfileAC0Free` | `acFree0` (`8k + 4` at `2·fcap < n`) | A, static | width-k modes |
| `SigningRateAC0` | one vote per slot | A, static | every mode |
| `HealDefault` | `healHsDefault`, `healHlDefault`, `healLatDefault` (Slice 1) | R | `Behaviour` |

Coverage packages (shared across chain shape families; they read a protocol only through which
bounds are finite):

| statement | covers bounds finite only in | premises |
|---|---|---|
| `ShapeHealCoverage0` | `HealSupport0` | chain claims, fit, `ProposalsNotFGAtt`, `1 ≤ fgDelay` |
| `ShapeTxLatencyCoverage0` | `LatencySupport0` | progress fit |
| `ShapeProposalLatencyCoverage0` | `LatencySupport0` | progress fit |

Every package also assumes the output it covers is provided.
-/

namespace Consensus.Comparison.Registry

/-- The order implies class inclusion (Slice 0 heal parameters). -/
theorem slice0ClassMono : Consensus.Comparison.Slice0ClassMono :=
  Consensus.Comparison.slice0Class_mono

/-- The order implies class inclusion (Slice 0 synchronous class). -/
theorem sync0ClassMono : Consensus.Comparison.Sync0ClassMono :=
  Consensus.Comparison.sync0Class_mono

/-- Bound `hsDefault`/`hlDefault`/`latDefault`; tier R; premise `Behaviour`. -/
theorem healDefault0 : Consensus.Comparison.HealDefault0 := Consensus.Comparison.healDefault0

/-- Bound `txLatDefault`; tier R; premise `Behaviour`. -/
theorem txLatencyDefault0 : Consensus.Comparison.TxLatencyDefault0 :=
  Consensus.Comparison.txLatencyDefault0

/-- Goldilocks heal defaults at the endpoint's contract; tier R; no premise. -/
theorem goldilocksHealDefault0 : Consensus.Goldilocks.Comparison.GoldilocksHealDefault0 :=
  Consensus.Goldilocks.Comparison.goldilocks_heal_default0

/-- Goldilocks transaction latency default at the endpoint's contract; tier R; no premise. -/
theorem goldilocksTxLatencyDefault0 : Consensus.Goldilocks.Comparison.GoldilocksTxLatencyDefault0 :=
  Consensus.Goldilocks.Comparison.goldilocks_txLatency_default0

/-- Bound `acFree0`; tier A, static; every width-`k` write mode and unlock oracle. -/
theorem healProfileAC0Free : Consensus.Goldilocks.Comparison.HealProfileAC0Free :=
  Consensus.Goldilocks.Comparison.healProfileAC0_free

/-- One vote per slot; tier A, static; every write mode and unlock oracle. -/
theorem signingRateAC0 : Consensus.Goldilocks.Comparison.SigningRateAC0 :=
  Consensus.Goldilocks.Comparison.signingRateAC0

/-- Heal coverage for chain shapes. -/
theorem shapeHealCoverage0 : Consensus.Comparison.ShapeHealCoverage0 :=
  Consensus.Comparison.shapeHealCoverage0

/-- Transaction latency coverage for chain shapes. -/
theorem shapeTxLatencyCoverage0 : Consensus.Comparison.ShapeTxLatencyCoverage0 :=
  Consensus.Comparison.shapeTxLatencyCoverage0

/-- Proposal latency coverage for chain shapes. -/
theorem shapeProposalLatencyCoverage0 : Consensus.Comparison.ShapeProposalLatencyCoverage0 :=
  Consensus.Comparison.shapeProposalLatencyCoverage0

/-- The order implies class inclusion (Slice 1 heal parameters). -/
theorem healClassMono : Consensus.Comparison.HealClassMono := Consensus.Comparison.healClassMono

/-- Bound `healHsDefault`/`healHlDefault`/`healLatDefault` (Slice 1); tier R; premise
`Behaviour`. -/
theorem healDefault : Consensus.Comparison.HealDefault := Consensus.Comparison.healDefault

end Consensus.Comparison.Registry

-- `#guard_msgs in #print axioms` puts the command off column 0; the pinned messages are longer
-- than 100 columns.
set_option linter.style.whitespace false
set_option linter.style.longLine false

/-- info: 'Consensus.Comparison.Registry.slice0ClassMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.slice0ClassMono

/-- info: 'Consensus.Comparison.Registry.sync0ClassMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.sync0ClassMono

/-- info: 'Consensus.Comparison.Registry.healDefault0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healDefault0

/-- info: 'Consensus.Comparison.Registry.txLatencyDefault0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.txLatencyDefault0

/-- info: 'Consensus.Comparison.Registry.goldilocksHealDefault0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.goldilocksHealDefault0

/-- info: 'Consensus.Comparison.Registry.goldilocksTxLatencyDefault0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.goldilocksTxLatencyDefault0

/-- info: 'Consensus.Comparison.Registry.healProfileAC0Free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healProfileAC0Free

/-- info: 'Consensus.Comparison.Registry.signingRateAC0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.signingRateAC0

/-- info: 'Consensus.Comparison.Registry.shapeHealCoverage0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.shapeHealCoverage0

/-- info: 'Consensus.Comparison.Registry.shapeTxLatencyCoverage0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.shapeTxLatencyCoverage0

/-- info: 'Consensus.Comparison.Registry.shapeProposalLatencyCoverage0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.shapeProposalLatencyCoverage0

/-- info: 'Consensus.Comparison.Registry.healClassMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healClassMono

/-- info: 'Consensus.Comparison.Registry.healDefault' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healDefault

end
