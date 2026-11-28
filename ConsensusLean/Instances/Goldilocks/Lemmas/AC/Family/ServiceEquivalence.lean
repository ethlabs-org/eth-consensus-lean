module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

/-! # Equivalence of statement-layer service and the existing service formulas -/

public section

namespace Consensus.Goldilocks.AC.FamilyFacts

variable {sp : ACParams} {FGP : Type}

theorem retainedBefore_iff_old (o : GTrace sp FGP) (y : Fin sp.n) (j : Nat)
    (v : Vote sp.n) (T : Time) : RetainedBefore o y j v T ↔ AC.RetainedBefore o y j v T := by
  rw [AC.retainedBefore_iff]; rfl

theorem messageServedBefore_iff_old (o : GTrace sp FGP) (y : Fin sp.n) (j : Nat)
    (τ : Time) (v : Vote sp.n) :
    MessageServedBefore o y j τ v ↔ AC.MessageServedBefore o y j τ v := by
  simp only [MessageServedBefore, AC.messageServedBefore_iff, retainedBefore_iff_old]

end Consensus.Goldilocks.AC.FamilyFacts

end
