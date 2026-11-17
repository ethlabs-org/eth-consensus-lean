module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Independent actual-output source packages and supplier-named evidence -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- Supplier-named evidence and eligible source candidates. A supplier must document
the actual meaning of eligible; successful outputs alone are not the full candidate set. -/
structure SourceData (A : SAOperations sp FGP S M) where
  evidence : Fin sp.n → Nat → Blk sp.n FGP → Prop
  eligible : Fin sp.n → Nat → ACLabel A.toAC → Set (Blk sp.n FGP)

end Consensus.Goldilocks.SA.FamilyFacts

end
