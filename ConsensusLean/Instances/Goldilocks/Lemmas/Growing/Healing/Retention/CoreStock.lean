module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Core
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock

public section

/-! # The stock reset bundle

`ResetPremisesUpTo.toCore`: the stock finite-reset premises give the reset core at
`Store.updateFinality` and `Node.frame`. -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Time → Set (Fin sp.n)}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {g ΔF a b hold : Time} {committee : Time → Finset (Fin sp.n)} {beta : ℚ}

/-- **The core of the stock finite-reset premises.** -/
theorem ResetPremisesUpTo.toCore
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b committee beta hold) :
    ResetRunCore tr H Store.updateFinality Node.frame proposer dg g ΔF a b committee beta hold where
  core := hp.run.toCore
  beta_le := hp.beta_le
  committee_pos := hp.committee_pos
  committeeFacts := hp.committeeFacts
  committeeFaults := hp.committeeFaults
  noColl := hp.noColl
  sync := hp.sync
  awake := hp.awake
  faults := hp.faults
  reset := hp.reset
  reset_le := hp.reset_le
  snapshot := hp.snapshot
  catchUp := hp.catchUp
  noRestart := hp.noRestart
  timeoutDelay := hp.timeoutDelay
  nonempty := hp.nonempty
  deepCover := hp.deepCover

end Consensus.Goldilocks.Healing.Growing

end
