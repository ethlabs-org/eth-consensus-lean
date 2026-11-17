module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Conditional lock-floor preservation and read-point consequences -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}

/-- An unexpired lock witness at a specified slot, above the protected block. -/
def LockFloor (L : Set Lock) (Φ : Frm sp.n FGP) (B₀ : Blk sp.n FGP)
    (j m : Nat) : Prop :=
  ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧
    ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B

variable {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n))

end Consensus.Goldilocks.SA.FamilyFacts

end
