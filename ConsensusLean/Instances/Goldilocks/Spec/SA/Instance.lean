module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Restart

@[expose] public section

/-! # Goldilocks SA as an AC

`goldilocksSA sp FGP`: the Goldilocks available chain (fgsa-spec.tex §"Available chain:
Goldilocks") as an `ACInterface`, polymorphic in the FG payload `FGP`, which it never reads
(the node instantiates `FGP := List (FG.Att n)`). Its messages are Goldfish votes, its payload
is `(votes, support_votes)` (two empty lists for genesis), and its message check is trivial
(form, committee and signature are not modelled, see `Vote`). It is parametric in the restart's
replay order (`ReplayOrder`), which the spec leaves free among parent orders. -/

namespace Consensus.Goldilocks.SA

/-- The Goldilocks SA as an AC, with the restart replay order `ro`. -/
@[reducible] noncomputable def goldilocksSA (sp : SAParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : ACInterface sp.toParams FGP where
  State := SAState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun A v => v ∈ A.pool v.slot
  genesisPayload := ([], [])
  initial := SAState.initial sp.genesisRoot
  onMessage := acOnMessage sp
  onBlock := acOnBlock sp
  onTick := acOnTick sp
  proposal := acProposal sp
  toFG := acToFG sp
  confirmed := acConfirmed sp
  head := acHead sp
  restart := acRestart sp ro

end Consensus.Goldilocks.SA

end
