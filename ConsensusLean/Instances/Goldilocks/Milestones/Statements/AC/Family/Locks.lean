module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Enabled shared-policy write events and lock provenance packages -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- Enabled update formula witness, not a post-state lock-set difference. -/
def UpdateFastEvent (m : WriteMode) (o : SATrace sp FGP ro)
    (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) : Prop :=
  m.fastArm = true ∧ SA.FastUpdateAt o x i s B CV

/-- Enabled reconstructed-input optimistic witness. -/
def OptimisticEvent (m : WriteMode) (o : SATrace sp FGP ro)
    (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) : Prop :=
  m.optimistic = true ∧ SA.OptimisticLockAt o x i s B CV

/-- Either enabled fast-write formula; disabled arms cannot witness it. -/
def FastWriteEvent (m : WriteMode) (o : SATrace sp FGP ro)
    (x : Fin sp.n) (i s : Nat) (B : Blk sp.n FGP) (CV : Set (Vote sp.n)) : Prop :=
  UpdateFastEvent m o x i s B CV ∨ OptimisticEvent m o x i s B CV

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))

end Consensus.Goldilocks.SA.FamilyFacts

end
