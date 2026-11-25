module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ReleaseGap

public section

/-! # The signing and release gaps from the contract assumptions

`ContractAssumptions.sign_liveness` gives every validator a signing time divisible by `ΔAC` in
`[t, t + (G + 1)·ΔAC)` from every `t ≥ 0`. At the node parameters `S.params pub hn` the delay is
`ΔAC` and the public times are its multiples, so this is the calendar's signing gap
(`signGapAt_of_assumptions`); likewise `ContractAssumptions.release_liveness` is the release
schedule's release gap (`releaseGapAt_of_assumptions`).

The final gap `finalSlots` is `releaseFinalSlots fgSlots releaseGap signGap`
(`ContractAssumptions.finalSlots_eq`), so the arithmetic of `ReleaseGap` applies to the
assumption set: the timeout pays `4·fgSlots + R + G ≤ 4·δ_t`
(`ContractAssumptions.fgSlots_releaseGap_signGap_le`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Consensus.Model (Public)

/-- The final gap of the assumption set is the release-gap final gap at its parameters. -/
theorem _root_.Consensus.Goldilocks.ContractAssumptions.finalSlots_eq {S : Setup}
    (A : ContractAssumptions S) :
    A.finalSlots = releaseFinalSlots A.fgSlots A.releaseGap A.signGap := by
  rw [ContractAssumptions.finalSlots, A.fgDelay_val, releaseFinalSlots_eq]

/-- The timeout of the assumption set, `3·c′ ≤ δ_t`. -/
theorem _root_.Consensus.Goldilocks.ContractAssumptions.timeout_releaseFinalSlots {S : Setup}
    (A : ContractAssumptions S) :
    3 * releaseFinalSlots A.fgSlots A.releaseGap A.signGap ≤ S.δt := by
  rw [releaseFinalSlots_eq]
  exact A.timeout

/-- The timeout pays the FG delay, the release wait and the signing wait:
`4·fgSlots + R + G ≤ 4·δ_t`. -/
theorem _root_.Consensus.Goldilocks.ContractAssumptions.fgSlots_releaseGap_signGap_le
    {S : Setup} (A : ContractAssumptions S) :
    4 * A.fgSlots + A.releaseGap + A.signGap ≤ 4 * S.δt :=
  Consensus.Goldilocks.Obligations.fgSlots_releaseGap_signGap_le A.timeout_releaseFinalSlots

/-- The setup's signing calendar has signing gap `A.signGap` from time `0` on. -/
theorem signGapAt_of_assumptions {S : Setup} (A : ContractAssumptions S) (pub : Public)
    (hn : 1 ≤ pub.n) :
    SignGapAt (S.params pub hn).toParams (S.sign pub) A.signGap 0 :=
  fun y t ht => A.sign_liveness pub y t ht

/-- The setup's release schedule has release gap `A.releaseGap` from time `0` on. -/
theorem releaseGapAt_of_assumptions {S : Setup} (A : ContractAssumptions S) (pub : Public)
    (hn : 1 ≤ pub.n) :
    ReleaseGapAt (S.params pub hn).toParams (S.release pub) A.releaseGap 0 :=
  fun y t ht => A.release_liveness pub y t ht

/-- The timeout pays the signing wait of the reset's update round: `3 + ⌈G/4⌉ ≤ δ_t`. -/
theorem signGap_δt {S : Setup} (A : ContractAssumptions S) : 3 + (A.signGap + 3) / 4 ≤ S.δt :=
  releaseGap_signGap_δt A.timeout_releaseFinalSlots

/-- The heal margin covers the nonfinal reset reserve and five signing waits. -/
theorem contract_heal_ge_reset_signGap {S : Setup} (A : ContractAssumptions S)
    (cap : Capability) (X : ℕ+) :
    (contract_catchUp S A : Nat) + (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 34) + 3 +
      5 * A.signGap ≤ contract_heal S A cap X := by
  rw [contract_heal_val, healMargin_val, healthyResetCoeff_val]
  have := A.six_le_δt
  omega

end Consensus.Goldilocks.Obligations
