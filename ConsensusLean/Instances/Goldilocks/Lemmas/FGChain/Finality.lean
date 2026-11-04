module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Transition

public section

/-! # Goldilocks FG: finality before the gate (G0.8)

At a height whose previous height is justified and whose predecessor is the highest pending pair, a
finality quorum for it makes `bestFinal` pick it, so the finality step of the same block finalizes
it, and a target quorum then justifies. -/

namespace Consensus.Goldilocks.FG

/-- **G0.8.** -/
theorem finality_before_gate (gp : FGParams) : FinalityBeforeGate gp := by
  intro σ _ hm hpw hle hq
  cases hb : gp.bestFinal σ with
  | none => exact absurd hq (Nat.not_le.2 (gp.bestFinal_eq_none hb _ hm))
  | some r =>
    obtain ⟨hr, -, hmax⟩ := gp.bestFinal_eq_some hb
    have := eq_of_pairwise_fst_lt hpw hr hm (le_antisymm (hle r hr) (hmax _ hm hq))
    subst this
    simp only [FGParams.finalizePrune, hb, FGParams.justifies]
    simp

end Consensus.Goldilocks.FG

end
