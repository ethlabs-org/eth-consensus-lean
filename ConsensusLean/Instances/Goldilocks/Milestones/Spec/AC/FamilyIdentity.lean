module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Family

/-! # Goldilocks identity observation data -/

@[expose] public section

namespace Consensus.Goldilocks.AC

/-- The existing AC operations, with the payload fixed by construction. -/
noncomputable def goldilocksOperations (sp : ACParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : ACOperations sp FGP (ACState sp.n) (Vote sp.n) where
  validPayload := (goldilocksAC sp FGP ro).validPayload
  validMsg := (goldilocksAC sp FGP ro).validMsg
  holdsMsg := (goldilocksAC sp FGP ro).holdsMsg
  genesisPayload := (goldilocksAC sp FGP ro).genesisPayload
  initial := (goldilocksAC sp FGP ro).initial
  onMessage := (goldilocksAC sp FGP ro).onMessage
  onBlock := (goldilocksAC sp FGP ro).onBlock
  onTick := (goldilocksAC sp FGP ro).onTick
  proposal := (goldilocksAC sp FGP ro).proposal
  toFG := (goldilocksAC sp FGP ro).toFG
  confirmed := (goldilocksAC sp FGP ro).confirmed
  head := (goldilocksAC sp FGP ro).head
  restart := (goldilocksAC sp FGP ro).restart

/-- Identity state and vote observation with the existing parent write mode. -/
noncomputable def goldilocksFamily (sp : ACParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : ACFamily (goldilocksOperations sp FGP ro) ro where
  stateView := id
  voteEmbed := id
  voteView := some
  sg := Vote.val
  vote_retract := fun _ => rfl
  vote_signer := fun _ _ h => (Option.some.inj h) ▸ rfl
  genesis := rfl
  initial := rfl
  mode := WriteMode.parent sp

end Consensus.Goldilocks.AC

end
