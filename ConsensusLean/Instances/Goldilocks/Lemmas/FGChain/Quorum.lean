module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.FGSafety

public section

/-! # Goldilocks FG: quorum intersection (G1.1)

Two sets of at least `q = ⌈2n/3⌉` validators meet in at least `2q − n ≥ n/3` of them. -/

namespace Consensus.Goldilocks.FG

/-- **G1.1.** -/
theorem quorum_intersection (gp : FGParams) : QuorumIntersection gp := by
  intro S₁ S₂ h₁ h₂
  have hu := Finset.card_union_add_card_inter S₁ S₂
  have hn := (S₁ ∪ S₂).card_le_univ
  simp only [Fintype.card_fin] at hn
  have hq : gp.q = (2 * gp.n + 2) / 3 := rfl
  omega

end Consensus.Goldilocks.FG

end
