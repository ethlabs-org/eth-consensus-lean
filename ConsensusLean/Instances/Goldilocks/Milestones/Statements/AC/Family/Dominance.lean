module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Dominance at exact, explicitly domain-indexed cast observations -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}
  {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n))

/-- Dominance at explicitly supplied domain members, indexed by the entire cast
observation and by its exact cut time. -/
structure ScopedDominance
    (domain : Fin sp.n → Nat → ACLabel (goldilocksSA sp FGP ro) → Em sp FGP →
      Blk sp.n FGP → Blk sp.n FGP → Time → Prop) : Prop where
  above : ∀ x ∈ H, ∀ i ℓ e B C,
    CastAt (F.proj tr) x i ℓ e → domain x i ℓ e B C ((F.proj tr).time i) →
    C ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame ((F.proj tr).time i) →
    ℓ.frame.Anc B C →
    ∃ Hd ∈ ℓ.frame.tree, Hd.root = e.msg.head ∧ ℓ.frame.Anc B Hd

end Consensus.Goldilocks.SA.FamilyFacts

end
