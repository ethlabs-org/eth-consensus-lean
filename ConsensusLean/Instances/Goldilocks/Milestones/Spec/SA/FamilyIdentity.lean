module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Family

/-! # Goldilocks identity observation data -/

@[expose] public section

namespace Consensus.Goldilocks.SA

/-- The existing SA operations, with the payload fixed by construction. -/
noncomputable def goldilocksOperations (sp : SAParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : SAOperations sp FGP (SAState sp.n) (Vote sp.n) where
  validPayload := (goldilocksSA sp FGP ro).validPayload
  validMsg := (goldilocksSA sp FGP ro).validMsg
  holdsMsg := (goldilocksSA sp FGP ro).holdsMsg
  genesisPayload := (goldilocksSA sp FGP ro).genesisPayload
  initial := (goldilocksSA sp FGP ro).initial
  onMessage := (goldilocksSA sp FGP ro).onMessage
  onBlock := (goldilocksSA sp FGP ro).onBlock
  onTick := (goldilocksSA sp FGP ro).onTick
  proposal := (goldilocksSA sp FGP ro).proposal
  toFG := (goldilocksSA sp FGP ro).toFG
  confirmed := (goldilocksSA sp FGP ro).confirmed
  head := (goldilocksSA sp FGP ro).head
  restart := (goldilocksSA sp FGP ro).restart

/-- Identity state and vote observation with the existing parent write mode. -/
noncomputable def goldilocksFamily (sp : SAParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : SAFamily (goldilocksOperations sp FGP ro) ro where
  stateView := id
  voteEmbed := id
  voteView := some
  sg := Vote.val
  vote_retract := fun _ => rfl
  vote_signer := fun _ _ h => (Option.some.inj h) ▸ rfl
  genesis := rfl
  initial := rfl
  mode := WriteMode.parent sp

end Consensus.Goldilocks.SA

end
