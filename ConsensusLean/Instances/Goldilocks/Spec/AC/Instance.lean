module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Restart

@[expose] public section

/-! # Goldilocks AC

`goldilocksAC sp FGP`: the Goldilocks available chain (goldilocks-spec.tex §"Available chain:
Goldilocks") as an `ACInterface`, polymorphic in the FG payload `FGP`, which it never reads
(the node instantiates `FGP := List (FG.Att n)`). Its messages are head votes, its payload
is `(votes, support_votes)` (two empty lists for genesis), and its message check is trivial
(form, committee and signature are not modelled, see `Vote`). -/

namespace Consensus.Goldilocks.AC

/-- The Goldilocks AC. -/
@[reducible] noncomputable def goldilocksAC (sp : ACParams) (FGP : Type)
    : ACInterface sp.toParams FGP where
  State := ACState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun A v => v ∈ A.pool v.slot
  genesisPayload := ([], [])
  initial := ACState.initial sp.genesisRoot
  onMessage := acOnMessage sp
  onBlock := acOnBlock sp
  onTick := acOnTick sp
  proposal := acProposal sp
  toFG := acToFG sp
  confirmed := acConfirmed sp
  head := acHead sp
  restart := acRestart sp

end Consensus.Goldilocks.AC

end
