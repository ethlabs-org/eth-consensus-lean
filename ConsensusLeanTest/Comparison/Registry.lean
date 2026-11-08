module
public import ConsensusLean.Proofs.Comparison.Main
public import ConsensusLean.Instances.Goldilocks.Proofs.Comparison.Main

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
| `ProposalLatencyAC0Sync` | `acLat0` (`6` at `2·f < n`), from slot 2 | A, static | width-k modes |
| `ProposalLatencyAC0Bridge` | `G_p + 6` from `t₂` | A, static | width-k modes, `Prop(G_p)` |
| `HealProfileER0Free` | `acFree0` | A, cand. | evidence release, width-`k` modes |
| `HealProfileCert0Free` | `acFree0` | A, cand. | late certificate (pool trace), width-`k` modes |
| `HealProfileERParent0` | `acFree0` | A, cand. | evidence release, parent mode |
| `HealProfileCertParent0` | `acFree0` | A, cand. | late certificate (pool trace), parent mode |
| `HealProfileMinimalAC0` | `acFree0` | A, cand. | minimal-ac, `slowOnly k false` |
| `HealProfileMinimalACOptLocked0` | `acFree0` | A, cand. | minimal-ac + opt-locked (`k true`) |
| `HealProfileAC1Free` | `acFree1` (`8k + 4` at `2·fcap < n`) | A, Slice 1 | width-k, every h, m |
| `HealProfileER1Free` | `acFree1` | A, cand., S1 | evidence release, width-`k` modes |
| `HealProfileCert1Free` | `acFree1` | A, cand., S1 | late certificate (pool trace) |
| `HealProfileERParent1` | `acFree1` | A, cand., S1 | evidence release, parent mode |
| `HealProfileCertParent1` | `acFree1` | A, cand., S1 | late certificate, parent mode |
| `HealProfileMinimalAC1` | `acFree1` | A, cand., S1 | minimal-ac, `slowOnly k false` |
| `HealProfileMinimalACOptLocked1` | `acFree1` | A, cand., S1 | minimal-ac + opt-locked |
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

/-- Bound `acLat0` from slot `2`; tier A, static; every width-`k` write mode and unlock oracle. -/
theorem proposalLatencyAC0Sync : Consensus.Goldilocks.Comparison.ProposalLatencyAC0Sync :=
  Consensus.Goldilocks.Comparison.proposalLatencyAC0_sync

/-- Some honest proposal by `t + G_p + 6Δ` from `t₂`; tier A, static; premise `Prop(G_p)`. -/
theorem proposalLatencyAC0Bridge : Consensus.Goldilocks.Comparison.ProposalLatencyAC0Bridge :=
  Consensus.Goldilocks.Comparison.proposalLatencyAC0_bridge
/-- Bound `acFree0`; tier A, candidate runs: evidence release, width-`k` modes. -/
theorem healProfileER0Free : Consensus.Goldilocks.Comparison.HealProfileER0Free :=
  Consensus.Goldilocks.Comparison.healProfileER0_free

/-- Bound `acFree0`; tier A, candidate runs: late certificate (pool trace), width-`k` modes. -/
theorem healProfileCert0Free : Consensus.Goldilocks.Comparison.HealProfileCert0Free :=
  Consensus.Goldilocks.Comparison.healProfileCert0_free

/-- Bound `acFree0`; tier A, candidate runs: evidence release, parent mode. -/
theorem healProfileERParent0 : Consensus.Goldilocks.Comparison.HealProfileERParent0 :=
  Consensus.Goldilocks.Comparison.healProfileERParent0

/-- Bound `acFree0`; tier A, candidate runs: late certificate (pool trace), parent mode. -/
theorem healProfileCertParent0 : Consensus.Goldilocks.Comparison.HealProfileCertParent0 :=
  Consensus.Goldilocks.Comparison.healProfileCertParent0

/-- Bound `acFree0`; tier A, candidate runs: minimal-ac, `slowOnly k false`. -/
theorem healProfileMinimalAC0 : Consensus.Goldilocks.Comparison.HealProfileMinimalAC0 :=
  Consensus.Goldilocks.Comparison.healProfileMinimalAC0

/-- Bound `acFree0`; tier A, candidate runs: minimal-ac `w = k` + locked ¾ optimistic, evidence
release's release (simulator class `minimal-ac+opt-locked`), `slowOnly k true`; integrated-pc's own
single release is not covered. -/
theorem healMinimalACOptLocked0 :
    Consensus.Goldilocks.Comparison.HealProfileMinimalACOptLocked0 :=
  Consensus.Goldilocks.Comparison.healProfileMinimalACOptLocked0

/-- Bound `acFree1` (`8k + 4` at `2·fcap < n`); tier A, Slice 1; width-k modes, every h, m. -/
theorem ac1Free : Consensus.Goldilocks.Comparison.HealProfileAC1Free :=
  Consensus.Goldilocks.Comparison.healProfileAC1_free

/-- Bound `acFree1`; tier A, cand., S1; evidence release, width-`k` modes. -/
theorem er1Free : Consensus.Goldilocks.Comparison.HealProfileER1Free :=
  Consensus.Goldilocks.Comparison.healProfileER1_free

/-- Bound `acFree1`; tier A, cand., S1; late certificate (pool trace). -/
theorem cert1Free : Consensus.Goldilocks.Comparison.HealProfileCert1Free :=
  Consensus.Goldilocks.Comparison.healProfileCert1_free

/-- Bound `acFree1`; tier A, cand., S1; evidence release, parent mode. -/
theorem erParent1 : Consensus.Goldilocks.Comparison.HealProfileERParent1 :=
  Consensus.Goldilocks.Comparison.healProfileERParent1

/-- Bound `acFree1`; tier A, cand., S1; late certificate, parent mode. -/
theorem certParent1 : Consensus.Goldilocks.Comparison.HealProfileCertParent1 :=
  Consensus.Goldilocks.Comparison.healProfileCertParent1

/-- Bound `acFree1`; tier A, cand., S1; minimal-ac, `slowOnly k false`. -/
theorem minimalAC1 : Consensus.Goldilocks.Comparison.HealProfileMinimalAC1 :=
  Consensus.Goldilocks.Comparison.healProfileMinimalAC1

/-- Bound `acFree1`; tier A, cand., S1; minimal-ac + opt-locked. -/
theorem minimalACOptLocked1 : Consensus.Goldilocks.Comparison.HealProfileMinimalACOptLocked1 :=
  Consensus.Goldilocks.Comparison.healProfileMinimalACOptLocked1

/-- The Slice 1 Tier A incident premises are monotone in the order of `HealQ`. -/
theorem incidentAC1Mono : Consensus.Goldilocks.Comparison.IncidentAC1Mono :=
  Consensus.Goldilocks.Comparison.incidentAC1_mono

/-- The order of `HealQ` passes to the Slice 0 points. -/
theorem healQSlice0Mono : Consensus.Comparison.HealQSlice0Mono :=
  Consensus.Comparison.healQ_slice0_mono

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

/-- info: 'Consensus.Comparison.Registry.proposalLatencyAC0Sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.proposalLatencyAC0Sync

/-- info: 'Consensus.Comparison.Registry.proposalLatencyAC0Bridge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.proposalLatencyAC0Bridge
/-- info: 'Consensus.Comparison.Registry.healProfileER0Free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healProfileER0Free

/-- info: 'Consensus.Comparison.Registry.healProfileCert0Free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healProfileCert0Free

/-- info: 'Consensus.Comparison.Registry.healProfileERParent0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healProfileERParent0

/-- info: 'Consensus.Comparison.Registry.healProfileCertParent0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healProfileCertParent0

/-- info: 'Consensus.Comparison.Registry.healProfileMinimalAC0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healProfileMinimalAC0

/-- info: 'Consensus.Comparison.Registry.healMinimalACOptLocked0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healMinimalACOptLocked0

/-- info: 'Consensus.Comparison.Registry.ac1Free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.ac1Free

/-- info: 'Consensus.Comparison.Registry.er1Free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.er1Free

/-- info: 'Consensus.Comparison.Registry.cert1Free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.cert1Free

/-- info: 'Consensus.Comparison.Registry.erParent1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.erParent1

/-- info: 'Consensus.Comparison.Registry.certParent1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.certParent1

/-- info: 'Consensus.Comparison.Registry.minimalAC1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.minimalAC1

/-- info: 'Consensus.Comparison.Registry.minimalACOptLocked1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.minimalACOptLocked1

/-- info: 'Consensus.Comparison.Registry.incidentAC1Mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.incidentAC1Mono

/-- info: 'Consensus.Comparison.Registry.healQSlice0Mono' depends on axioms: [propext] -/
#guard_msgs in #print axioms Consensus.Comparison.Registry.healQSlice0Mono

end
