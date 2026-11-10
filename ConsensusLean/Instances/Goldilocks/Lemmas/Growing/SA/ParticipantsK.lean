module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.VotesK

/-! # Full-set preservation of growing committee participation -/

public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}
  {A : SAOperations sp FGP S M}

/-- Logical equivalence on the same prefix, not an execution refinement. -/
theorem participantsK_full_iff (F : SAFamily A ro) (tr : ACTrace A.toAC)
    (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (d : Time) :
    ParticipantsK F tr H U (CommitteeDict.full sp.n) d ↔
      Participants F (tr.upTo d) (H d) U := by
  constructor
  · intro h
    exact ⟨fun x hx s => h.vote x hx s (Set.mem_univ x),
      fun s b hs hb X hX i ℓ hu x hx => h.early s b hs hb X hX i ℓ hu x hx (Set.mem_univ x)⟩
  · intro h
    exact ⟨fun x hx s _ => h.vote x hx s,
      fun s b hs hb X hX i ℓ hu x hx _ => h.early s b hs hb X hX i ℓ hu x hx⟩

end Consensus.Goldilocks.SA.FamilyFacts

end
