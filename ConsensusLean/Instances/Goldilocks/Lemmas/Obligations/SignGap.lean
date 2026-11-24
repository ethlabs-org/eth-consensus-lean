module
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs

public section

/-! # The signing gap from the contract assumptions

`ContractAssumptions.sign_liveness` gives every validator a signing time divisible by `ΔAC` in
`[t, t + (G + 1)·ΔAC)` from every `t ≥ 0`. At the node parameters `S.params pub hn` the delay is
`ΔAC` and the public times are its multiples, so this is the calendar's signing gap
(`signGapAt_of_assumptions`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Consensus.Model (Public)

/-- The setup's signing calendar has signing gap `A.signGap` from time `0` on. -/
theorem signGapAt_of_assumptions {S : Setup} (A : ContractAssumptions S) (pub : Public)
    (hn : 1 ≤ pub.n) :
    SignGapAt (S.params pub hn).toParams (S.sign pub) A.signGap 0 :=
  fun y t ht => A.sign_liveness pub y t ht

/-- The timeout pays the signing wait of the reset's update round: `3 + ⌈G/4⌉ ≤ δ_t`. -/
theorem signGap_δt {S : Setup} (A : ContractAssumptions S) : 3 + (A.signGap + 3) / 4 ≤ S.δt := by
  have := A.timeout
  have := A.two_le_fgSlots
  omega

/-- The timeout pays the FG delay and the signing wait: `4·fgSlots + G ≤ 4·δ_t`. -/
theorem fgSlots_signGap_le {S : Setup} (A : ContractAssumptions S) :
    4 * A.fgSlots + A.signGap ≤ 4 * S.δt := by
  have := A.timeout
  have := A.two_le_fgSlots
  omega

/-- The heal margin covers the nonfinal reset reserve and five signing waits. -/
theorem contract_heal_ge_reset_signGap {S : Setup} (A : ContractAssumptions S)
    (cap : Capability) (X : ℕ+) :
    (contract_catchUp S A : Nat) + (healthyResetCoeff S X + 8 * S.k + 4 * (X : Nat) + 34) + 3 +
      5 * A.signGap ≤ contract_heal S A cap X := by
  rw [contract_heal_val, healMargin_val, healthyResetCoeff_val]
  have := A.six_le_δt
  omega

end Consensus.Goldilocks.Obligations
