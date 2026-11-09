module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Observation

@[expose] public section

/-! # Observational runs of an SA family

The actual node trace remains generic. Its SA observation satisfies the structural AC
contract, but not the SA execution law. Step-law consequences belong in the AC contract.
-/

namespace Consensus.Goldilocks

open SA (SAParams ReplayOrder Payload SAOperations SAFamily)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {S M : Type} {A : SAOperations sp (List (FG.Att sp.n)) S M}

/-- A real node run with SA-vocabulary unforgeability and observational AC laws.
The message signer belongs to the actual AC; the projected vote signer is always `Vote.val`.
No concrete SA local run or handler equation is a field. -/
structure FamilyRun (F : SAFamily sp (List (FG.Att sp.n)) ro A)
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (H : Set (Fin sp.n)) (sg : M → Fin sp.n) (tr : RunTrace A.toAC) : Prop
    extends Node.LocalRun proposer dg H sg tr where
  genesis_root_ok : (sp.toParams.genesisBlock A.genesisPayload).RootOk dg
  carried_vote_unforgeable : ∀ y ∈ H, ∀ i B, tr.BlockCallAt y i B →
    ∀ v ∈ SA.blockVotes B, v.val ∈ H →
      ∃ j < i, ∃ e, SA.VoteAt (F.proj tr.projAC) v.val j e ∧ e.msg = v
  observation : ACObsRun (SA.goldilocksSA sp (List (FG.Att sp.n)) ro) H
    (tr.HonestBlocks H) (F.proj tr.projAC)

end Consensus.Goldilocks

end
