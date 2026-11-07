module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Actions

@[expose] public section

/-! # The evidence-release SA as an AC

`evidenceReleaseSA sp FGP ro`: the SA of `WeightedLocks.Actions` as an `ACInterface`, polymorphic
in the FG payload `FGP` (which it never reads) and parametric in the restart's replay order, as
`goldilocksSA`. Its messages, payload, payload check, message check and genesis payload are the
parent's; its state is `WState`; the confirmed tip and the head are the parent's, read on the
parent's state (whose locks are the forgotten weighted locks). -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

/-- The evidence-release SA as an AC, with the restart replay order `ro`. -/
@[reducible] noncomputable def evidenceReleaseSA (sp : SAParams) (FGP : Type)
    (ro : ReplayOrder sp FGP) : ACInterface sp.toParams FGP where
  State := WState sp.n
  Msg := Vote sp.n
  Payload := Payload sp.n
  validPayload := validPayload
  validMsg := fun _ => True
  holdsMsg := fun X v => v ∈ X.ac.pool v.slot
  genesisPayload := ([], [])
  initial := WState.initial sp.genesisRoot
  onMessage := acOnMessageW sp
  onBlock := acOnBlockW sp
  onTick := acOnTickW sp
  proposal := acProposalW sp
  toFG := acToFGW sp
  confirmed := fun X => acConfirmed sp X.ac
  head := fun X => acHead sp X.ac
  restart := acRestartW sp ro

end Consensus.Goldilocks.EvidenceRelease

end
