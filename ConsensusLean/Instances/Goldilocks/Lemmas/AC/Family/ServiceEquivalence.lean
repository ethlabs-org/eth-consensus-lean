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

theorem serviceWindowBefore_iff_old (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (a b : Time) (o : SATrace sp FGP ro) :
    ServiceWindowBefore H U a b o ↔ SA.ServiceWindowBefore H U a b o := by
  constructor
  · intro h
    exact ⟨fun x hx i v hi ha y hy j ℓ hc hb ht =>
      (messageServedBefore_iff_old ..).mp (h.message x hx i v hi ha y hy j ℓ hc hb ht), h.relay⟩
  · intro h
    exact ⟨fun x hx i v hi ha y hy j ℓ hc hb ht =>
      (messageServedBefore_iff_old ..).mpr (h.message x hx i v hi ha y hy j ℓ hc hb ht), h.relay⟩

theorem serviceBefore_iff_old (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (b : Time) (o : SATrace sp FGP ro) :
    ServiceBefore H U b o ↔ SA.ServiceBefore H U b o :=
  serviceWindowBefore_iff_old H U 0 b o

end Consensus.Goldilocks.SA.FamilyFacts

end
