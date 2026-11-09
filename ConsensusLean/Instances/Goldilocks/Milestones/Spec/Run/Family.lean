module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

@[expose] public section

namespace Consensus.Goldilocks

variable {sp : SA.SAParams} {S M : Type}
  {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {A : SA.SAOperations sp (List (FG.Att sp.n)) S M}

/-- An actual node run with independent SA observation and vote provenance. -/
structure FamilyRun (F : SA.SAFamily A ro)
    (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (H : Set (Fin sp.n)) (tr : RunTrace A.toAC) : Prop
    extends Node.LocalRun proposer dg H F.sg tr where
  genesis_root_ok : (sp.toParams.genesisBlock A.genesisPayload).RootOk dg
  carried_vote_unforgeable : ∀ y ∈ H, ∀ i B, tr.BlockCallAt y i B →
    ∀ v ∈ SA.blockVotes B, v.val ∈ H →
    ∃ j < i, ∃ e, SA.VoteAt (F.proj tr.projAC) v.val j e ∧ e.msg = v
  agreement : SA.ObservationAgreement F H tr.projAC
  observation : ACObsRun (SA.goldilocksSA sp (List (FG.Att sp.n)) ro)
    H (tr.HonestBlocks H) (F.proj tr.projAC)

end Consensus.Goldilocks

end
