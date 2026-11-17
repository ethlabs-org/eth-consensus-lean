module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Service
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool

/-! # Equivalence of statement-layer service and the existing service formulas -/

public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

theorem poolEvidenceBefore_iff_old (st : SAState sp.n) (v : Vote sp.n) (T : Time) :
    PoolEvidenceBefore st v T ↔ SA.PoolEvidenceBefore st v T := by
  rw [SA.poolEvidenceBefore_iff]; rfl

theorem retainedBefore_iff_old (o : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (v : Vote sp.n) (T : Time) : RetainedBefore o y j v T ↔ SA.RetainedBefore o y j v T := by
  simp only [RetainedBefore, SA.retainedBefore_iff, poolEvidenceBefore_iff_old]

theorem messageServedBefore_iff_old (o : SATrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (τ : Time) (v : Vote sp.n) :
    MessageServedBefore o y j τ v ↔ SA.MessageServedBefore o y j τ v := by
  simp only [MessageServedBefore, SA.messageServedBefore_iff, retainedBefore_iff_old]

end Consensus.Goldilocks.SA.FamilyFacts

end
