module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.GrowingObservation

@[expose] public section

namespace Consensus.Goldilocks.Growing

variable {sp : SA.SAParams} {S M : Type}
  {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {A : SA.SAOperations sp (List (FG.Att sp.n)) S M}

/-- Actual-node observation under growing faults. Both provenance honesty premises
are at the block-processing cut, not the earlier emission cut. -/
structure FamilyRun (F : SA.SAFamily A ro)
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (H : Time → Set (Fin sp.n)) (tr : RunTrace A.toAC) : Prop
    extends LocalRun proposer dg H F.sg tr where
  genesis_root_ok : (sp.toParams.genesisBlock A.genesisPayload).RootOk dg
  carried_vote_unforgeable : ∀ y i B, y ∈ H (tr.time i) →
    tr.BlockCallAt y i B → ∀ v ∈ SA.blockVotes B,
    v.val ∈ H (tr.time i) →
    ∃ j < i, ∃ e, SA.VoteAt (F.proj tr.projAC) v.val j e ∧ e.msg = v
  agreement : SA.Growing.ObservationAgreement F H tr.projAC
  observation : ACObsRun (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)
    H (tr.HonestBlocksAt H) (F.proj tr.projAC)

end Consensus.Goldilocks.Growing

end
