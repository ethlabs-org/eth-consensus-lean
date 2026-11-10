module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Committee
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Votes
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.UpTo

/-! # Growing committee participation on a consumer prefix -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}
  {A : SAOperations sp FGP S M}

/-- Member-qualified participation through `d`. Only the sender is committee-restricted;
the early conclusion is update-pool membership, not admission provenance. -/
structure ParticipantsK (F : SAFamily A ro) (tr : ACTrace A.toAC)
    (H : Time → Set (Fin sp.n)) (U : Set (Blk sp.n FGP))
    (K : CommitteeDict sp.n) (d : Time) : Prop where
  vote : ∀ x ∈ H d, ∀ s : Nat, x ∈ K.committee s →
    (F.proj (tr.upTo d)).awake x (sp.ts s + sp.Δ) →
    SA.JoinedAt (F.proj (tr.upTo d)) x (sp.ts s + sp.Δ) →
    ∃ i e, SA.VoteAt (F.proj (tr.upTo d)) x i e ∧ e.msg.val = x ∧ e.msg.slot = s
  early : ∀ (s : Nat) (b : Time), ServiceBefore (H d) U b (F.proj (tr.upTo d)) →
    sp.ts s + 2 * sp.Δ ≤ b → ∀ X ∈ H d, ∀ i ℓ,
    SA.UpdateAt (F.proj (tr.upTo d)) X i s ℓ →
    ∀ x ∈ H d, x ∈ K.committee s →
    (F.proj (tr.upTo d)).awake x (sp.ts s + sp.Δ) →
    SA.JoinedAt (F.proj (tr.upTo d)) x (sp.ts s + sp.Δ) →
    x ∈ SA.voters {v | v ∈ ((F.proj (tr.upTo d)).state X i).pool s}

end Consensus.Goldilocks.SA.FamilyFacts

end
