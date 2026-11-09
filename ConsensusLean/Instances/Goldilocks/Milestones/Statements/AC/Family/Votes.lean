module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family.Service

/-! # Independent observed-vote and participation packages -/

@[expose] public section

namespace Consensus.Goldilocks.SA.FamilyFacts

variable {sp : SAParams} {FGP S M : Type} {ro : ReplayOrder sp FGP}
  {A : SAOperations sp FGP S M} (F : SAFamily A ro) (tr : ACTrace A.toAC)
  (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP))

/-- Independently supplied slot, provenance, timing and head facts about observed votes. -/
structure VoteObservation : Prop where
  pool_slot : ∀ y ∈ H, ∀ i s, ∀ v ∈ ((F.proj tr).state y i).pool s, v.slot = s
  authentic : ∀ y ∈ H, ∀ i s, ∀ v ∈ ((F.proj tr).state y i).pool s, v.val ∈ H →
    ∃ j < i, ∃ e, VoteAt (F.proj tr) v.val j e ∧ e.msg = v
  timing : ∀ x ∈ H, ∀ i e, VoteAt (F.proj tr) x i e →
    sp.ts e.msg.slot ≤ (F.proj tr).time i ∧
      (F.proj tr).time i ≤ sp.ts e.msg.slot + sp.Δ
  head : ∀ x ∈ H, ∀ i ℓ e, CastAt (F.proj tr) x i ℓ e →
    ∃ B ∈ ℓ.frame.tree, B.root = e.msg.head

/-- Participation and service consequences, independent of structural observation. -/
structure Participants : Prop where
  vote : ∀ x ∈ H, ∀ s : Nat, (F.proj tr).awake x (sp.ts s + sp.Δ) →
    SA.JoinedAt (F.proj tr) x (sp.ts s + sp.Δ) →
    ∃ i e, SA.VoteAt (F.proj tr) x i e ∧ e.msg.val = x ∧ e.msg.slot = s
  early : ∀ (s : Nat) (b : Time), ServiceBefore H U b (F.proj tr) →
    sp.ts s + 2 * sp.Δ ≤ b → ∀ X ∈ H, ∀ i ℓ,
    SA.UpdateAt (F.proj tr) X i s ℓ → ∀ x ∈ H,
    (F.proj tr).awake x (sp.ts s + sp.Δ) →
    SA.JoinedAt (F.proj tr) x (sp.ts s + sp.Δ) →
    x ∈ SA.voters {v | v ∈ ((F.proj tr).state X i).pool s}

end Consensus.Goldilocks.SA.FamilyFacts

end
