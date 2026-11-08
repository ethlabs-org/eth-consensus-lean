module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.ParentOracleM

public section

/-! # The parent's unlock oracle at a write mode: the parent's mode

At the parent's mode, the parent's unlock and its oracle at a mode are the parent's
(`parentUnlockM_parent`, `parentOracleM_parent`), so a statement over
`ACLocalRunU (WriteMode.parent sp) (parentOracleM sp (WriteMode.parent sp) tr)` is one over the
parent's oracle. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

theorem parentUnlockM_parent {ro : ReplayOrder sp FGP} :
    parentUnlockM (ro := ro) sp (WriteMode.parent sp) = parentUnlock sp := by
  rfl

theorem parentOracleM_parent {ro : ReplayOrder sp FGP} (tr : SATrace sp FGP ro) :
    parentOracleM sp (WriteMode.parent sp) tr = parentOracle sp tr := by
  funext i
  unfold parentOracleM parentOracle
  cases tr.label i <;> rfl

end Consensus.Goldilocks.SA

end
