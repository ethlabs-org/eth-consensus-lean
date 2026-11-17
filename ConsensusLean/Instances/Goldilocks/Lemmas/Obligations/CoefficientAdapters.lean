module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Lemmas.Blocks.Facts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Conditional coefficient adapters

Arithmetic and recurrence of the coefficient envelope.
These bounds do not choose the shared witnesses or supply semantic service producers.
All readiness comparisons use the same interval; changing catch-up does not recover
progress opportunities before the new start.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Blocks

/-- Maturity includes catch-up inside healing, with the readiness unit charged once. -/
theorem ready_le_heal {g d c h : Time} (hd : 1 ≤ d) (hh : c + 1 ≤ h) :
    max g 0 + c * d + 1 ≤ max g 0 + h * d := by
  linarith [mul_le_mul_of_nonneg_right hh (zero_le_one.trans hd)]

end Consensus.Goldilocks.Obligations
